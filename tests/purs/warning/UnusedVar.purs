-- @shouldWarnWith UnusedName
-- @shouldWarnWith UnusedName
-- @shouldWarnWith UnusedName
-- @shouldWarnWith UnusedName
module Main where

data X = X


unusedInLambda :: X
unusedInLambda = (\z -> X) X

unusedLetName :: X
unusedLetName =
  let z = X in
  X

unusedWhereIsLet :: X
unusedWhereIsLet =
  X
  where z = X

unusedLetArgument :: X
unusedLetArgument = 
  let f x y = x
  in f X X

notUnusedLet :: X
notUnusedLet =
  let f x = f' x
      f' x = f x
  in
  f X


unusedCaseBinder :: X
unusedCaseBinder = 
  case X of
    z -> X