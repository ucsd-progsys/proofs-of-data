
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}
{-@ LIQUID "--diff"       @-}
{-@ infixr ++             @-}

module Multiset where

import Lists
import ProofCombinators
import Prelude hiding ((++))
import Sort 

{-# ANN module "HLint: ignore Use camelCase" #-}
{-# ANN module "HLint: ignore Use foldr"     #-}
{-# ANN module "HLint: ignore Use const"     #-}

-- | Datatype ----------------------------------------------------------------- 

type Multiset a = a -> Int

{-@ reflect empty @-}
empty :: Multiset a
empty x = 0 

{-@ reflect union @-}
union :: Multiset a -> Multiset a -> Multiset a
union a b x = a x + b x

{-@ reflect singleton @-}
singleton :: (Eq a) => a -> Multiset a
singleton x y = if x == y then 1 else 0

-- | Properties of MultiSet ---------------------------------------------------

{-@ lem_union_comm :: a:_ -> b:_ -> ExtEq (union a b) (union b a) @-}
lem_union_comm :: Multiset a -> Multiset a -> a -> Proof
lem_union_comm a b x = ()

{-@ lem_union_assoc :: a:_ -> b:_ -> c:_ -> ExtEq (union (union a b) c) (union a (union b c)) @-}
lem_union_assoc :: Multiset a -> Multiset a -> Multiset a -> a -> Proof
lem_union_assoc a b c x = ()

-- | The `contents` of a list ------------------------------------------------

{-@ reflect contents @-}
contents :: (Eq a) => [a] -> Multiset a
contents []     z = empty z 
contents (x:xs) z = (singleton x `union` contents xs) z

-- | Insertion `sort` preserves multiset -------------------------------------

{-@ lem_insert_contents :: x:_ -> ys:_ -> 
        ExtEq (contents (insert x ys)) (contents (cons x ys)) 
  @-}
lem_insert_contents :: (Ord a) => a -> [a] -> a -> Proof
lem_insert_contents x []     = const ()
lem_insert_contents x (y:ys) 
  | x <= y                = const ()
  | otherwise             = lem_insert_contents x ys

{-@ thm_insert_contents :: xs:_ -> ExtEq (contents xs) (contents (sort xs)) @-}
thm_insert_contents :: (Ord a) => [a] -> a -> Proof
thm_insert_contents []     = \_ -> ()
thm_insert_contents (x:xs) = \z -> lem_insert_contents x (sort xs) z
                               &&& thm_insert_contents xs z 