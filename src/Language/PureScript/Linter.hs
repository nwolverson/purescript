-- |
-- This module implements a simple linting pass on the PureScript AST.
--
module Language.PureScript.Linter (lint, module L) where

import Debug.Trace

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


import Control.Applicative
import Control.Arrow (first, second)
import Control.Monad (unless)
import Control.Monad.Writer.Class
import Control.Monad.Supply.Class (MonadSupply, fresh, freshName)

import Data.Function (on)
import Data.List (foldl', sortBy)
import Data.Maybe (fromMaybe)
import qualified Data.Map as M
import Data.Text (Text)
import qualified Data.Text as T

import Language.PureScript.AST.Binders
import Language.PureScript.AST.Declarations
import Language.PureScript.AST.Literals
import Language.PureScript.Crash
import Language.PureScript.Environment
import Language.PureScript.Errors
import Language.PureScript.Kinds
import Language.PureScript.Names as P
import Language.PureScript.Pretty.Values (prettyPrintBinderAtom)
import Language.PureScript.Traversals
import Language.PureScript.Types as P
import qualified Language.PureScript.Constants as C


-- | Lint the PureScript AST.
-- |
-- | Right now, this pass only performs a shadowing check.
lint :: forall m. (MonadWriter MultipleErrors m) => Module -> m ()
lint mod@(Module _ _ mn ds _) = do
  lintUnused mod
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
lintUnused (Module _ _ mn ds _) =
  trace ("linting unused for " ++ show mn) $
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
  lintDeclaration = tell . goDecl
    where

    goDecl :: Declaration -> MultipleErrors
    -- f' d@(DataBindingGroupDeclaration ds) = foldl (<>.) (f d) (fmap f' ds)
    goDecl d@(ValueDeclaration vd) = -- (fmap h' (valdeclBinders vd) 
        foldMap (\(GuardedExpr grd v) -> goExpr (declSourceSpan d) v) (valdeclExpression vd)
    goDecl d = mempty
            --fmap k' grd ++ [g' v]) (valdeclExpression vd))
    -- f' d@(BindingGroupDeclaration ds) = foldl (<>.) (f d) (fmap (\(_, _, val) -> g' val) ds)
    -- f' d@(TypeClassDeclaration _ _ _ _ _ ds) = foldl (<>.) (f d) (fmap f' ds)
    -- f' d@(TypeInstanceDeclaration _ _ _ _ _ _ _ (ExplicitInstance ds)) = foldl (<>.) (f d) (fmap f' ds)
    -- f' d@(BoundValueDeclaration _ b expr) = f d <>. h' b <>. g' expr

    goExpr :: SourceSpan -> Expr -> MultipleErrors
    goExpr span theExpression = 
      trace "expr" $
      traceShow theExpression $
      traceShow unusedRes $
      errs
      where
      -- should unused be discharged here already?
      (unusedRes, errs) = go span mempty theExpression

      restoreAndWarn :: S.Set Ident -> S.Set Ident -> (S.Set Ident, MultipleErrors) -> (S.Set Ident, MultipleErrors)
      restoreAndWarn unused newNames (nowUnused, errors) = 
        let restoredUnused = (newNames `S.intersection` unused) `S.union` (nowUnused `S.difference` newNames)
            warnUnused = nowUnused `S.intersection` newNames
            combinedErrors = if not $ S.null warnUnused then errors <> (mconcat $ map (errorMessage' ss . UnusedName) $ S.toList warnUnused) else errors
        in
          (restoredUnused, combinedErrors)

      go :: SourceSpan -> S.Set Ident -> Expr -> (S.Set Ident, MultipleErrors)
      go ss unused (Var _ (Qualified Nothing v)) = trace "var" $ (S.delete v unused, mempty)
      go ss unused (Var _ (Qualified _ v)) = trace "qualified var??" (unused, mempty)

      go ss unused (Let _ ds e) =
        let decl unused' (ValueDecl sann ident name binders gexprs) = 
              let bindNewNames = S.fromList (concatMap binderNames binders)
                  unguard (GuardedExpr guards expr) = map unguard' guards ++ [expr]
                  unguard' (ConditionGuard ee) = ee
                  unguard' (PatternGuard _ ee) = ee
                  allExprs = concatMap unguard gexprs
              in
                  restoreAndWarn unused' bindNewNames $ foldr1 combine $ map (go ss (unused' `S.union` bindNewNames)) allExprs

            decl unused' _ = (unused', mempty)
            
            letNewNames = traceShowId $ S.fromList $ mapMaybe (fmap valdeclIdent . getValueDeclaration) ds

        in
          restoreAndWarn unused letNewNames $ foldr1 combine (map (decl (unused `S.union` letNewNames)) ds ++ [go ss (unused `S.union` letNewNames) e]) 
        -- underBinders unused (concatMap valdeclBinders ds') (map valdeclExpression ds')
        -- isValueDecl ds
        -- ValueDeclaration { valdeclIdent , valdeclBinders, valdeclExpression } getValueDeclaration
        -- ValueDecl _ ident _ binders expr = ...
        -- trace "let" $ (unused, mempty)-- NO
      go ss unused (Abs binder v1) = 
        trace "abs" $
        let newNames = S.fromList (binderNames binder)
            (nowUnused, errors) = go ss (unused `S.union` newNames) v1
            restoredUnused = (newNames `S.intersection` unused) `S.union` (nowUnused `S.difference` newNames)
            warnUnused = nowUnused `S.intersection` newNames
            combinedErrors = if not $ S.null warnUnused then errors <> (mconcat $ map (errorMessage' ss . UnusedName) $ S.toList warnUnused) else errors

        in
        traceShow warnUnused $ (restoredUnused, combinedErrors)
      
      go ss unused (UnaryMinus _ v1) = go ss unused v1
      go ss unused (BinaryNoParens _ v1 v2) = go ss unused v1 `combine` go ss unused v2
      go ss unused (Parens v1) = go ss unused v1
      go ss unused (TypeClassDictionaryConstructorApp _ v1) = go ss unused v1
      go ss unused (Accessor _ v1) = go ss unused v1
      
      -- TODO 
      -- go ss unused (ObjectUpdate obj vs) = foldl (<>.) (g'' s obj) (fmap (g'' s . snd) vs)
      -- go ss unused (ObjectUpdateNested obj vs) = foldl (<>.) (g'' s obj) (fmap (g'' s) vs)
      
    
    
      go ss unused (App v1 v2) = go ss unused v1 `combine` go ss unused v2
      go ss unused (Unused v) = go ss unused v
      go ss unused (IfThenElse v1 v2 v3) = go ss unused v1 `combine` go ss unused v2 `combine` go ss unused v3
      -- go ss unused (Case vs alts) = foldl (<>.) (foldl (<>.) r0 (fmap (g'' s) vs)) (fmap (i'' s) alts)
      go ss unused (TypedValue _ v1 _) = go ss unused v1
      -- go ss unused (Do _ es) = foldl (<>.) r0 (fmap (j'' s) es)
      -- go ss unused (Ado _ es v1) = foldl (<>.) r0 (fmap (j'' s) es) <>. g'' s v1
      go ss unused (PositionedValue ss' _ v1) = trace "positioned" $ go ss' unused v1
      
      go ss unused _ = trace "default" $ (unused, mempty)


 

    combine ::
      (S.Set Ident, MultipleErrors) ->
      (S.Set Ident, MultipleErrors) ->
      (S.Set Ident, MultipleErrors)
    combine (a, b) (c, d) = (S.intersection a c, b <> d)
