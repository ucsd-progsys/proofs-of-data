
-- | A bit redundant in the LH setting; its mostly just Selection.hs ----------

{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}
{-@ LIQUID "--diff"       @-}

module PriQueue where

import           ProofCombinators
import           Perm
import           Lists
import qualified Data.Set  as S
import qualified Selection as S
import           Prelude hiding ((++))

{-# ANN module "HLint: ignore Use camelCase" #-}
{-# ANN module "HLint: ignore Use Eta reduce" #-}

type PriQ a = [a]

{-@ reflect empty @-}
empty :: PriQ a 
empty = []

{-@ reflect insert @-}
{-@ insert :: x:_ -> q:_ -> {res:_ | lElems res = S.consElems x q} @-}
insert :: a -> PriQ a -> PriQ a
insert x xs = x:xs

{-@ reflect delete_min @-}
{-@ delete_min :: (Ord a) => q:PriQ a -> 
     Maybe (m :: a, {q' :PriQ {v:a | m <= v} | lElems q = S.consElems m q'} ) 
  @-}
delete_min :: (Ord a) => PriQ a -> Maybe (a, PriQ a) 
delete_min []     = Nothing 
delete_min (x:xs) = let S.Chop y ys = S.select x xs  
                    in Just (y, ys) 

{-@ reflect merge @-}
merge :: PriQ a -> PriQ a -> PriQ a
merge q1 q2 = q1 ++ q2 


{-@ lem_merge :: q1:_ -> q2:_ -> 
      {lElems (merge q1 q2) = S.union (lElems q1) (lElems q2)} 
  @-}
lem_merge :: PriQ a -> PriQ a -> Proof
lem_merge []     _  = ()
lem_merge (x:xs) q2 = lem_merge xs q2 
------------------------------------------------------------------------------- 
