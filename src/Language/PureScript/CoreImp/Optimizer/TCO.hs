-- | This module implements tail call elimination.
module Language.PureScript.CoreImp.Optimizer.TCO (tco) where

import Prelude.Compat

import Data.Text (Text)
import qualified Language.PureScript.Constants as C
import Language.PureScript.CoreImp.AST
import Language.PureScript.AST.SourcePos (SourceSpan)
import Safe (headDef, tailSafe)

-- | Eliminate tail calls
tco :: AST -> AST
tco = everywhere convert where
  tcoVar :: Text -> Text
  tcoVar arg = "$tco_var_" <> arg

  copyVar :: Text -> Text
  copyVar arg = "$copy_" <> arg

  tcoDone :: Text
  tcoDone = "$tco_done"

  tcoLoop :: Text
  tcoLoop = "$tco_loop"

  tcoResult :: Text
  tcoResult = "$tco_result"

  convert :: AST -> AST
  convert (VariableIntroduction ss name (Just (p, unwrapIife -> (rewrapIife, fn@Function {}))))
      | isTailRecursive name body'
      = VariableIntroduction ss name (Just (p, rewrapIife . replace $ toLoop name outerArgs innerArgs body'))
    where
      innerArgs = headDef [] argss
      outerArgs = concat . reverse $ tailSafe argss
      (argss, body', replace) = collectAllFunctionArgs [] id fn
  convert js = js

  unwrapIife :: AST -> (AST -> AST, AST)
  unwrapIife (App s1 (Function s2 ident args (unwrapPureVars -> (rewrapPureVars, Return s3 value))) []) =
    (\value' -> App s1 (Function s2 ident args (rewrapPureVars (Return s3 value'))) [], value)
  unwrapIife js = (id, js)

  unwrapPureVars :: AST -> (AST -> AST, AST)
  unwrapPureVars js@(Block ss xs) = go id xs
    where
      go f [x] = (\x' -> Block ss (f [x']), x)
      go f (v@(VariableIntroduction _ _ (Just (IsPure, _))) : xs') = go (f . (v :)) xs'
      go _ _ = (id, js)
  unwrapPureVars js = (id, js)

  collectAllFunctionArgs :: [[Text]] -> (AST -> AST) -> AST -> ([[Text]], AST, AST -> AST)
  collectAllFunctionArgs allArgs f (Function s1 ident args (Block s2 (body@(Return _ _):_))) =
    collectAllFunctionArgs (args : allArgs) (\b -> f (Function s1 ident (map copyVar args) (Block s2 [b]))) body
  collectAllFunctionArgs allArgs f (Function ss ident args body@(Block _ _)) =
    (args : allArgs, body, f . Function ss ident (map copyVar args))
  collectAllFunctionArgs allArgs f (Return s1 (Function s2 ident args (Block s3 [body]))) =
    collectAllFunctionArgs (args : allArgs) (\b -> f (Return s1 (Function s2 ident (map copyVar args) (Block s3 [b])))) body
  collectAllFunctionArgs allArgs f (Return s1 (Function s2 ident args body@(Block _ _))) =
    (args : allArgs, body, f . Return s1 . Function s2 ident (map copyVar args))
  collectAllFunctionArgs allArgs f body = (allArgs, body, f)

  isTailRecursive :: Text -> AST -> Bool
  isTailRecursive ident js = countSelfReferences js > 0 && allInTailPosition js where
    countSelfReferences = everything (+) match where
      match :: AST -> Int
      match (Var _ ident') | ident == ident' = 1
      match _ = 0

    allInTailPosition (Return _ expr)
      | isSelfCall ident expr = countSelfReferences expr == 1
      | otherwise = countSelfReferences expr == 0
    allInTailPosition (While _ js1 body)
      = countSelfReferences js1 == 0 && allInTailPosition body
    allInTailPosition (For _ _ js1 js2 body)
      = countSelfReferences js1 == 0 && countSelfReferences js2 == 0 && allInTailPosition body
    allInTailPosition (ForIn _ _ js1 body)
      = countSelfReferences js1 == 0 && allInTailPosition body
    allInTailPosition (IfElse _ js1 body el)
      = countSelfReferences js1 == 0 && allInTailPosition body && all allInTailPosition el
    allInTailPosition (Block _ body)
      = all allInTailPosition body
    allInTailPosition (Throw _ js1)
      = countSelfReferences js1 == 0
    allInTailPosition (ReturnNoResult _)
      = True
    allInTailPosition (VariableIntroduction _ _ js1)
      = all ((== 0) . countSelfReferences . snd) js1
    allInTailPosition (Assignment _ _ js1)
      = countSelfReferences js1 == 0
    allInTailPosition (Comment _ _ js1)
      = allInTailPosition js1
    allInTailPosition _
      = False

  toLoop :: Text -> [Text] -> [Text] -> AST -> AST
  toLoop ident outerArgs innerArgs js =
      Block rootSS $
        map (\arg -> VariableIntroduction rootSS (tcoVar arg) (Just (UnknownPurity, Var rootSS (copyVar arg)))) outerArgs ++
        [ VariableIntroduction rootSS tcoDone (Just (UnknownPurity, BooleanLiteral rootSS False))
        , VariableIntroduction rootSS tcoResult Nothing
        , Function rootSS (Just tcoLoop) (outerArgs ++ innerArgs) (Block rootSS [loopify js])
        , While rootSS (Unary rootSS Not (Var rootSS tcoDone))
            (Block rootSS
              [(Assignment rootSS (Var rootSS tcoResult) (App rootSS (Var rootSS tcoLoop) ((map (Var rootSS . tcoVar) outerArgs) ++ (map (Var rootSS . copyVar) innerArgs))))])
        , Return rootSS (Var rootSS tcoResult)
        ]
    where
    rootSS = Nothing

    loopify :: AST -> AST
    loopify (Return ss ret)
      | isSelfCall ident ret =
        let
          allArgumentValues = concat $ collectArgs [] ret
        in
          Block ss $
            zipWith (\val arg ->
              Assignment ss (Var ss (tcoVar arg)) val) allArgumentValues outerArgs
            ++ zipWith (\val arg ->
              Assignment ss (Var ss (copyVar arg)) val) (drop (length outerArgs) allArgumentValues) innerArgs
            ++ [ ReturnNoResult ss ]
      | otherwise = Block ss [ markDone ss, Return ss ret ]
    loopify (ReturnNoResult ss) = Block ss [ markDone ss, ReturnNoResult ss ]
    loopify (While ss cond body) = While ss cond (loopify body)
    loopify (For ss i js1 js2 body) = For ss i js1 js2 (loopify body)
    loopify (ForIn ss i js1 body) = ForIn ss i js1 (loopify body)
    loopify (IfElse ss cond body el) = IfElse ss cond (loopify body) (fmap loopify el)
    loopify (Block ss body) = Block ss (map loopify body)
    loopify other = other

    markDone :: Maybe SourceSpan -> AST
    markDone ss = Assignment ss (Var ss tcoDone) (BooleanLiteral ss True)

    collectArgs :: [[AST]] -> AST -> [[AST]]
    collectArgs acc (App _ fn []) =
      -- count 0-argument applications as single-argument so we get the correct number of args
      collectArgs ([Var Nothing C.undefined] : acc) fn
    collectArgs acc (App _ fn args') = collectArgs (args' : acc) fn
    collectArgs acc _ = acc

  isSelfCall :: Text -> AST -> Bool
  isSelfCall ident (App _ (Var _ ident') _) = ident == ident'
  isSelfCall ident (App _ fn _) = isSelfCall ident fn
  isSelfCall _ _ = False
