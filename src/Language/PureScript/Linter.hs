-- |
-- This module implements a simple linting pass on the PureScript AST.
--
module Language.PureScript.Linter (lint, module L) where

import Prelude.Compat

import Control.Monad.Writer.Class

import Data.Maybe (mapMaybe)
import qualified Data.Set as S
import Data.Text (Text)

import Language.PureScript.AST
import Language.PureScript.Crash 
import Language.PureScript.Errors
import Language.PureScript.Linter.Exhaustive as L
import Language.PureScript.Linter.Imports as L
import Language.PureScript.Linter.Unused as L
import Language.PureScript.Names
import Language.PureScript.Types


-- | Lint the PureScript AST.
-- |
-- | Right now, this pass only performs a shadowing check.
lint :: forall m. (MonadWriter MultipleErrors m) => Module -> m ()
lint modl@(Module _ _ mn ds _) = do
  lintUnused modl
  censor (addHint (ErrorInModule mn)) $ mapM_ lintDeclaration ds

  where
  moduleNames :: S.Set ScopedIdent
  moduleNames = S.fromList (map ToplevelIdent (mapMaybe getDeclIdent ds))

  getDeclIdent :: Declaration -> Maybe Ident
  getDeclIdent (ValueDeclaration vd) = Just (valdeclIdent vd)
  getDeclIdent (ExternDeclaration _ ident _) = Just ident
  getDeclIdent (TypeInstanceDeclaration _ _ _ ident _ _ _ _) = Just ident
  getDeclIdent BindingGroupDeclaration{} = internalError "lint: binding groups should not be desugared yet."
  getDeclIdent _ = Nothing

  lintDeclaration :: Declaration -> m ()
  lintDeclaration = tell . f
    where
    (warningsInDecl, _, _, _, _) = everythingWithScope (\_ _ -> mempty) stepE stepB (\_ _ -> mempty) stepDo

    f :: Declaration -> MultipleErrors
    f (TypeClassDeclaration _ name args _ _ decs) = addHint (ErrorInTypeClassDeclaration name) (foldMap (f' (S.fromList $ fst <$> args)) decs)
    f dec = f' S.empty dec

    f' :: S.Set Text -> Declaration -> MultipleErrors
    f' s dec@(ValueDeclaration vd) =
      addHint (ErrorInValueDeclaration (valdeclIdent vd)) (warningsInDecl moduleNames dec <> checkTypeVarsInDecl s dec)
    f' s (TypeDeclaration td@(TypeDeclarationData (ss, _) _ _)) =
      addHint (ErrorInTypeDeclaration (tydeclIdent td)) (checkTypeVars ss s (tydeclType td))
    f' s dec = warningsInDecl moduleNames dec <> checkTypeVarsInDecl s dec

    stepE :: S.Set ScopedIdent -> Expr -> MultipleErrors
    stepE s (Abs (VarBinder ss name) _) | name `inScope` s = errorMessage' ss (ShadowedName name)
    stepE s (Let _ ds' _) = foldMap go ds'
      where
      go d | Just i <- getDeclIdent d
           , inScope i s = errorMessage' (declSourceSpan d) (ShadowedName i)
           | otherwise = mempty
    stepE _ _ = mempty

    stepB :: S.Set ScopedIdent -> Binder -> MultipleErrors
    stepB s (VarBinder ss name)
      | name `inScope` s
      = errorMessage' ss (ShadowedName name)
    stepB s (NamedBinder ss name _)
      | inScope name s
      = errorMessage' ss (ShadowedName name)
    stepB _ _ = mempty

    stepDo :: S.Set ScopedIdent -> DoNotationElement -> MultipleErrors
    stepDo s (DoNotationLet ds') = foldMap go ds'
      where
      go d
        | Just i <- getDeclIdent d, i `inScope` s = errorMessage' (declSourceSpan d) (ShadowedName i)
        | otherwise = mempty
    stepDo _ _ = mempty

  checkTypeVarsInDecl :: S.Set Text -> Declaration -> MultipleErrors
  checkTypeVarsInDecl s d = let (f, _, _, _, _) = accumTypes (checkTypeVars (declSourceSpan d) s) in f d

  checkTypeVars :: SourceSpan -> S.Set Text -> SourceType -> MultipleErrors
  checkTypeVars ss set ty = everythingWithContextOnTypes set mempty mappend step ty <> snd (findUnused ty)
    where

    step :: S.Set Text -> SourceType -> (S.Set Text, MultipleErrors)
    step s (ForAll _ tv _ _ _) = bindVar s tv
    step s _ = (s, mempty)

    bindVar :: S.Set Text -> Text -> (S.Set Text, MultipleErrors)
    bindVar = bind ss ShadowedTypeVar

    findUnused :: SourceType -> (S.Set Text, MultipleErrors)
    findUnused = go set where
      -- Recursively walk the type and prune used variables from `unused`
      go :: S.Set Text -> SourceType -> (S.Set Text, MultipleErrors)
      go unused (TypeVar _ v) = (S.delete v unused, mempty)
      go unused (ForAll _ tv _ t1 _) =
        let (nowUnused, errors) = go (S.insert tv unused) t1
            restoredUnused = if S.member tv unused then S.insert tv nowUnused else nowUnused
            combinedErrors = if S.member tv nowUnused then errors <> errorMessage' ss (UnusedTypeVar tv) else errors
        in (restoredUnused, combinedErrors)
      go unused (TypeApp _ f x) = go unused f `combine` go unused x
      go unused (ConstrainedType _ c t1) = foldl combine (unused, mempty) $ map (go unused) (constraintArgs c <> [t1])
      go unused (RCons _ _ t1 rest) = go unused t1 `combine` go unused rest
      go unused (KindedType _ t1 _) = go unused t1
      go unused (ParensInType _ t1) = go unused t1
      go unused (BinaryNoParensType _ t1 t2 t3) = go unused t1 `combine` go unused t2 `combine` go unused t3
      go unused TUnknown{} = (unused, mempty)
      go unused TypeLevelString{} = (unused, mempty)
      go unused TypeWildcard{} = (unused, mempty)
      go unused TypeConstructor{} = (unused, mempty)
      go unused TypeOp{} = (unused, mempty)
      go unused Skolem{} = (unused, mempty)
      go unused REmpty{} = (unused, mempty)

      combine ::
        (S.Set Text, MultipleErrors) ->
        (S.Set Text, MultipleErrors) ->
        (S.Set Text, MultipleErrors)
      combine (a, b) (c, d) = (S.intersection a c, b <> d)

  bind :: (Ord a) => SourceSpan -> (a -> SimpleErrorMessage) -> S.Set a -> a -> (S.Set a, MultipleErrors)
  bind ss mkError s name
    | name `S.member` s = (s, errorMessage' ss (mkError name))
    | otherwise = (S.insert name s, mempty)



lintUnused :: forall m. (MonadWriter MultipleErrors m) => Module -> m ()
lintUnused (Module modSS _ mn modDecls exports) =
  censor (addHint (ErrorInModule mn)) $ do
    topVars <- traverse lintDeclaration modDecls
    let allVars = S.unions topVars
    case exports of
      Nothing ->
        pure ()
      Just exports' -> do
        let n (ValueRef _ ident) = Just ident
            n _ = Nothing
            exportIds = S.fromList $ mapMaybe n exports'
            expectedUsedDecls = S.fromList (mapMaybe getDeclIdent modDecls) `S.difference` exportIds
            newErrs = mconcat $ map (errorMessage' modSS . UnusedDeclaration) $ S.toList $ expectedUsedDecls `S.difference` allVars
        tell newErrs
        pure ()
  where
  getDeclIdent :: Declaration -> Maybe Ident
  getDeclIdent (ValueDeclaration vd) = Just (valdeclIdent vd)
  getDeclIdent (ExternDeclaration _ ident _) = Just ident
  getDeclIdent (TypeInstanceDeclaration _ _ _ ident _ _ _ _) = Just ident
  getDeclIdent BindingGroupDeclaration{} = internalError "lint: binding groups should not be desugared yet."
  getDeclIdent _ = Nothing

  lintDeclaration :: Declaration -> m (S.Set Ident)
  lintDeclaration declToLint = do
    let (vars, errs) = goDecl declToLint
    tell errs
    pure vars
    where

    goDecl :: Declaration -> (S.Set Ident, MultipleErrors)
    goDecl d@(ValueDeclaration vd) =
        let allExprs = concatMap unguard $ valdeclExpression vd
            bindNewNames = S.fromList (concatMap binderNames $ valdeclBinders vd)
            ss = declSourceSpan d
            (vars, errs) = removeAndWarn ss bindNewNames $ foldr1 combine $ map (go ss) allExprs
            errs' = addHint (ErrorInValueDeclaration $ valdeclIdent vd) errs
        in
          (vars, errs')

    goDecl _ = mempty

    go :: SourceSpan -> Expr -> (S.Set Ident, MultipleErrors)
    go _ (Var _ (Qualified Nothing v)) = (S.singleton v, mempty)
    go _ (Var _ qident) = (S.empty, mempty)

    go ss (Let _ ds e) =
      let letNames = S.fromList $ mapMaybe (fmap valdeclIdent . getValueDeclaration) ds
      in removeAndWarn ss letNames $ foldr1 combine (go ss e : map (decl ss) ds) 
    go ss (Abs binder v1) = 
      let newNames = S.fromList (binderNames binder)
      in
      removeAndWarn ss newNames $ go ss v1
    
    go ss (UnaryMinus _ v1) = go ss v1
    go ss (BinaryNoParens _ v1 v2) = go ss v1 `combine` go ss v2
    go ss (Parens v1) = go ss v1
    go ss (TypeClassDictionaryConstructorApp _ v1) = go ss v1
    go ss (Accessor _ v1) = go ss v1
    
    -- -- TODO 
    -- -- go ss unused (ObjectUpdate obj vs) = foldl (<>.) (g'' s obj) (fmap (g'' s . snd) vs)
    -- -- go ss unused (ObjectUpdateNested obj vs) = foldl (<>.) (g'' s obj) (fmap (g'' s) vs)
  
    go ss (App v1 v2) = go ss v1 `combine` go ss v2
    go ss (Unused v) = go ss v
    go ss (IfThenElse v1 v2 v3) = go ss v1 `combine` go ss v2 `combine` go ss v3
    go ss (Case vs alts) = 
      let f (CaseAlternative binders gexprs) =
            let bindNewNames = S.fromList (concatMap binderNames binders)
                allExprs = concatMap unguard gexprs
            in
                removeAndWarn ss bindNewNames $ foldr1 combine $ map (go ss) allExprs
      in
      foldr1 combine $ map (go ss) vs ++ map f alts

    go ss (TypedValue _ v1 _) = go ss v1
    go ss (Do _ es) = doElts ss es Nothing
    go ss (Ado _ es v1) = doElts ss es (Just v1)
    go _ (PositionedValue ss' _ v1) = go ss' v1
    
    go _ _ = (mempty, mempty)

    doElts :: SourceSpan -> [DoNotationElement] -> Maybe Expr -> (S.Set Ident, MultipleErrors)
    doElts ss' (DoNotationValue e : rest) v = go ss' e `combine` doElts ss' rest v
    doElts ss' (DoNotationBind binder e : rest) v = 
      let bindNewNames = S.fromList (binderNames binder)
      in go ss' e `combine` removeAndWarn ss' bindNewNames (doElts ss' rest v)
        
    doElts ss' (DoNotationLet ds : rest) v = 
      let letNewNames = S.fromList $ mapMaybe (fmap valdeclIdent . getValueDeclaration) ds
          declRes = foldr1 combine (map (decl ss') ds)
      in removeAndWarn ss' letNewNames $ declRes `combine` doElts ss' rest v
    doElts _ (PositionedDoNotationElement ss'' _ e : rest) v = doElts ss'' (e : rest) v
    doElts ss' [] (Just e) = go ss' e
    doElts _ [] Nothing = (mempty, mempty)

    decl ss (ValueDecl _ _ _ binders gexprs) = 
      let bindNewNames = S.fromList (concatMap binderNames binders)
          allExprs = concatMap unguard gexprs
      in
          removeAndWarn ss bindNewNames $ foldr1 combine $ map (go ss) allExprs
    decl _ _ = (mempty, mempty)

    unguard (GuardedExpr guards expr) = map unguard' guards ++ [expr]
    unguard' (ConditionGuard ee) = ee
    unguard' (PatternGuard _ ee) = ee

    removeAndWarn :: SourceSpan -> S.Set Ident -> (S.Set Ident, MultipleErrors) -> (S.Set Ident, MultipleErrors)
    removeAndWarn ss newNames (used, errors) = 
      let filteredUsed = used `S.difference` newNames
          warnUnused = newNames `S.difference` used
          combinedErrors = if not $ S.null warnUnused then errors <> (mconcat $ map (errorMessage' ss . UnusedName) $ S.toList warnUnused) else errors
      in
        (filteredUsed, combinedErrors)

    combine ::
      (S.Set Ident, MultipleErrors) ->
      (S.Set Ident, MultipleErrors) ->
      (S.Set Ident, MultipleErrors)
    combine (a, b) (c, d) = (S.union a c, b <> d)
