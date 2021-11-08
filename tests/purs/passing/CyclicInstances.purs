module Main where

import Prelude

import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)
import Effect.Console (log)

newtype A = A B
derive newtype instance Show A
data B = B C
       | Z
derive instance Generic B _
instance Show B where show x = genericShow x
newtype C = C A
derive instance Generic C _
instance Show C where show = genericShow

main = log "Done"
