-- | Removes unused variables
module Language.PureScript.CoreImp.Optimizer.Unused
  ( removeCodeAfterReturnStatements
  , removeUndefinedApp
  , removeUnusedPureVars
  ) where

import Prelude.Compat

import Language.PureScript.CoreImp.AST
import Language.PureScript.CoreImp.Optimizer.Common
import qualified Language.PureScript.Constants as C

removeCodeAfterReturnStatements :: AST -> AST
removeCodeAfterReturnStatements = everywhere (removeFromBlock go)
  where
  go :: [AST] -> [AST]
  go jss | not (any isReturn jss) = jss
         | otherwise = let (body, ret : _) = break isReturn jss in body ++ [ret]
  isReturn (Return _ _) = True
  isReturn (ReturnNoResult _) = True
  isReturn _ = False

removeUndefinedApp :: AST -> AST
removeUndefinedApp = everywhere convert
  where
  convert (App ss fn [Var _ arg]) | arg == C.undefined = App ss fn []
  convert js = js

removeUnusedPureVars :: AST -> AST
removeUnusedPureVars = everywhere $ removeFromBlock (foldr f [])
  where
  f :: AST -> [AST] -> [AST]
  f (VariableIntroduction _ var (Just (IsPure, _))) sts | not (any (isUsed var) sts) = sts
  f s sts = s : sts
