{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}
{- LIQUID "--diff"       @-}

{-@ infixr ++             @-}

module Trie where

-- import qualified Data.Set as S
-- import           Prelude hiding ((++))
import           ProofCombinators
import           Positive
-- import           Lists
-- import           Perm
-- import           Perm


-- | The `Trie` data type  ----------------------------------------------------

data Trie a 
  = Leaf 
  | Node (Maybe a) (Trie a) (Trie a)
  deriving (Show)

-- | Implementation of a get/set API ------------------------------------------

{-@ reflect empty @-}
empty :: () -> Trie a
empty _ = Leaf

{-@ reflect get @-}
get :: Trie v -> Pos -> Maybe v
get Leaf _                   = Nothing  
get (Node x _ _) XH          = x  
get (Node _ l _) (X False p) = get l p  
get (Node _ _ r) (X True  p) = get r p  

{-@ reflect spine @-}
spine :: Pos -> v -> Trie v
spine XH          v = Node (Just v) Leaf        Leaf
spine (X False p) v = Node Nothing  (spine p v) Leaf
spine (X True  p) v = Node Nothing  Leaf        (spine p v) 

{-@ reflect set @-}
set :: Trie v -> Pos -> v -> Trie v 
set Leaf p v                   = spine p v
set (Node _ l r) XH v          = Node (Just v) l           r 
set (Node x l r) (X False p) v = Node x        (set l p v) r 
set (Node x l r) (X True  p) v = Node x        l           (set r p v) 

{- 
-- TODO https://github.com/ucsd-progsys/liquidhaskell/issues/1470

{-@ ex_trie :: _ -> TT @-}
ex_trie _ = True -- get t0 k5  == Nothing
         -- && get t1 k14 == Just "horse"
         -- FAILS && get t2 k5  == Just "cat"
         && get t2 k14  == Just "horse"

         -- get t0 k5  == Just "cat" 
         -- && get t2 k14 == Just "horse"
  where 
    t0    = empty () :: Trie String 
    t1    = set t0 k14  "horse"
    t2    = set t1 k5   "cat"
    k5    = p5  ()
    k14   = p14 ()
------
-}


-- | Map Laws ------------------------------------------------------------------

{-@ lem_get_spine :: p:_ -> val:_ -> { get (spine p val) p == Just val } @-}
lem_get_spine :: Pos -> v -> Proof
lem_get_spine XH _          = ()
lem_get_spine (X False p) v = lem_get_spine p v 
lem_get_spine (X True  p) v = lem_get_spine p v 

{-@ lem_get_eq :: m:_ -> key:_ -> val:_ -> 
      { get (set m key val) key == Just val }
  @-}
lem_get_eq :: Trie v -> Pos -> v -> Proof
lem_get_eq Leaf         p           v = lem_get_spine p v  
lem_get_eq (Node x l r) XH          v = () 
lem_get_eq (Node x l r) (X False p) v = lem_get_eq l p v 
lem_get_eq (Node x l r) (X True  p) v = lem_get_eq r p v

{-@ lem_get_neq :: m:_ -> k1:_ -> k2:{k2 /= k1} -> v:_ -> 
      { get (set m k2 v) k1 == get m k1 }
  @-}
lem_get_neq :: Trie v -> Pos -> Pos -> v -> Proof
lem_get_neq = todo ()   -- HEREHEREHEREHEREHERE

------------------------------------------------------------------------------
hello :: Int 
hello = 10
