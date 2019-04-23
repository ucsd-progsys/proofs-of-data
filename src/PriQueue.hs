
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}
{-@ LIQUID "--diff"       @-}

module PriQueue where

import           ProofCombinators
import           Lists
import qualified Selection as S
import           Prelude hiding ((++))

{-# ANN module "HLint: ignore Use camelCase" #-}
{-# ANN module "HLint: ignore Use Eta reduce" #-}

type PriQ a = [a]

{-@ reflect empty @-}
empty :: PriQ a 
empty = []

{-@ reflect insert @-}
insert :: a -> PriQ a -> PriQ a
insert x xs = x:xs

{-@ reflect delete_min @-}
{-@ delete_min :: (Ord a) => PriQ a -> Maybe (m :: a, PriQ {v:a | m <= v}) @-}
delete_min :: (Ord a) => PriQ a -> Maybe (a, PriQ a) 
delete_min []     = Nothing 
delete_min (x:xs) = let S.Chop y ys = S.select x xs  
                    in Just (y, ys) 

{-@ reflect merge @-}
merge :: PriQ a -> PriQ a -> PriQ a
merge q1 q2 = q1 ++ q2

------------------------------------------------------------------------------- 