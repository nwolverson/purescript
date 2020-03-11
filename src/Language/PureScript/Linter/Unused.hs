module Language.PureScript.Linter.Unused
  ( checkUnused
  ) where

import Prelude.Compat
import Debug.Trace

import Control.Monad.Writer.Class

import Data.Maybe (mapMaybe)
import qualified Data.Set as S
import Data.Text (Text)

import Language.PureScript.AST
import Language.PureScript.Crash
import Language.PureScript.Errors
import Language.PureScript.Linter.Exhaustive as L
import Language.PureScript.Linter.Imports as L
import Language.PureScript.Names
import Language.PureScript.Types


import Protolude (ordNub)

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

checkUnused
  :: forall m
   . (MonadWriter MultipleErrors m, MonadSupply m)
   => Module
   -> m () 
checkUnused (Module _ _ _ _ _) = do
  pure ()