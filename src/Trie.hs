{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}
{-@ LIQUID "--diff"       @-}
{-@ infixr ++             @-}

module Trie where

import qualified Data.Set as S
import           Prelude hiding ((++))
import           ProofCombinators
import           Lists
import           Perm

hello :: Int 
hello = 10
