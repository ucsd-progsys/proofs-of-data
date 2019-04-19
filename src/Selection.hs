{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}
{- LIQUID "--diff"       @-}
{- infixr ++             @-}

module Selection where

import Lists
import Perm
import Sort
import ProofCombinators
import qualified Data.Set as S

-- | Increasingly Ordered Lists ----------------------------------------------

{-@ type IncList a = [a]<{\me you -> me <= you}> @-}

-- | `IncList` are indeed `sorted` -------------------------------------------

{-@ thm_inc_sorted :: xs:IncList a -> { sorted xs } @-}
thm_inc_sorted :: (Ord a) => [a] -> Proof 
thm_inc_sorted []         = () 
thm_inc_sorted [_]        = () 
thm_inc_sorted (x1:x2:xs) = thm_inc_sorted (x2:xs) 

-- | A 'Chop' of a list comprises a 'min' element and the 'rest' --------------

{-@ data Chop a = Chop { cMin :: a, cRest :: [{v:a | cMin <= v}] } @-}

data Chop a = Chop { cMin :: a, cRest :: [a] }

-- | The elements of a 'Chop' ------------------------------------------------- 

{-@ measure cElems @-}
cElems :: (Ord a) => Chop a -> S.Set a 
cElems (Chop x xs) = consElems x xs

{-@ inline consElems @-}
consElems :: (Ord a) => a -> [a] -> S.Set a
consElems x ys = S.union (S.singleton x) (lElems ys) 

-- | Selection Sort ----------------------------------------------------------

{-@ reflect select @-}
{-@ select :: x:_ -> l:_ -> {c : Chop a | cMin c <= x && len (cRest c) = len l && cElems c = consElems x l} @-}
select :: (Ord a) => a -> [a] -> Chop a 
select x []    = Chop x []
select x (h:t) 
  | x <= h     = let Chop j l' = select x t in Chop j (h : l')  
  | otherwise  = let Chop j l' = select h t in Chop j (x : l')  

{-@ reflect selsort @-}
{-@ selsort :: (Ord a) => xs:[a] -> {v: IncList a | perm v xs} @-}
selsort :: (Ord a) => [a] -> [a] 
selsort []     = [] 
selsort (x:xs) = let Chop y ys = select x xs 
                 in y : selsort ys 

-- | Selection Sort is a Correct Sorting Algorithm ---------------------------

{-@ thm_selsort_correct :: Is_Sorting_Algo selsort @-}
thm_selsort_correct :: (Ord a) => [a] -> Proof 
thm_selsort_correct xs = thm_inc_sorted (selsort xs) 

{-# ANN module "HLint: ignore Use camelCase" #-}