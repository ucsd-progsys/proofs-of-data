{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}
{-@ LIQUID "--diff"       @-}

{-@ infixr ++             @-}

module Trie where

-- import qualified Data.Set as S
import           Prelude hiding (abs)
import           ProofCombinators
import           Positive
import qualified TotalMaps as T
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
empty :: Trie a
empty = Leaf

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


------------------------------------------------------------------------------
-- | Map Laws ----------------------------------------------------------------
------------------------------------------------------------------------------

{-@ lem_spine_eq :: p:_ -> val:_ -> { get (spine p val) p == Just val } @-}
lem_spine_eq :: Pos -> v -> Proof
lem_spine_eq XH _          = ()
lem_spine_eq (X False p) v = lem_spine_eq p v 
lem_spine_eq (X True  p) v = lem_spine_eq p v 

{-@ lem_spine_neq :: p1:_ -> p2:{p2 /= p1} -> val:_ -> 
      { get (spine p2 val) p1 == Nothing } 
  @-}
lem_spine_neq :: Pos -> Pos -> v -> Proof
lem_spine_neq XH           XH        _ = impossible ()
lem_spine_neq XH           (X _ _)   _ = ()
lem_spine_neq (X True  p1) XH        _ = ()
lem_spine_neq (X False p1) XH        _ = ()
lem_spine_neq (X b1 p1)    (X b2 p2) v 
  | b1 == b2                           = lem_spine_neq p1 p2 v
  | otherwise                          = () 

{-@ lem_get_eq :: m:_ -> key:_ -> val:_ -> 
      { get (set m key val) key == Just val }
  @-}
lem_get_eq :: Trie v -> Pos -> v -> Proof
lem_get_eq Leaf         p           v = lem_spine_eq p v  
lem_get_eq (Node x l r) XH          v = () 
lem_get_eq (Node x l r) (X False p) v = lem_get_eq l p v 
lem_get_eq (Node x l r) (X True  p) v = lem_get_eq r p v

{-@ lem_get_neq :: m:_ -> p1:_ -> p2:{p2 /= p1} -> val:_ -> 
      { get (set m p2 val) p1 == get m p1 }
  @-}
lem_get_neq :: Trie v -> Pos -> Pos -> v -> Proof
lem_get_neq Leaf         p1        p2        v = lem_spine_neq p1 p2 v  
lem_get_neq (Node {})    XH        XH        v = impossible () 
lem_get_neq (Node {})    XH        (X b2 p2) v = () 
lem_get_neq (Node {})    (X b1 p1) XH        v = ()
lem_get_neq (Node x l r) (X b1 p1) (X b2 p2) v 
  | b1 == b2                                   = lem_get_neq l p1 p2 v &&& lem_get_neq r p1 p2 v  
  | otherwise                                  = ()


------------------------------------------------------------------------------
-- | Bijection between `Pos` and `Int`; move into `Positive.hs`?
------------------------------------------------------------------------------

{-@ reflect natBool @-}
natBool :: Int -> Bool 
natBool 0 = False 
natBool _ = True 

{-@ reflect natPos @-}
{-@ natPos :: {v:Int | 0 < v} -> Pos @-}
natPos :: Int -> Pos
natPos 1 = XH
natPos n = X (natBool d) (natPos n') 
  where 
     d   = n `mod` 2 
     n'  = n `div` 2

{-@ lem_natPosNat :: p:_ -> {p = natPos (posNat p)} @-}
lem_natPosNat :: Pos -> Proof
lem_natPosNat = todo () 

{-@ lem_posNatPos :: n:{0 < n} -> {n = posNat (natPos n) } @-}
lem_posNatPos :: Int -> Proof
lem_posNatPos = todo () 

------------------------------------------------------------------------------
-- | Abstraction Function ----------------------------------------------------  
------------------------------------------------------------------------------
{-@ type TMap a = T.TotalMap {v:Int | 0 < v} (Maybe a) @-}

{-@ reflect abs @-}
{-@ abs :: Trie v -> TMap v @-}
abs t n = get t (natPos n)


-- | When is a `A :: TMap` "equivalent to" a `T :: Trie` ---------------------

{-@ type EquivTrie A T = posKey:_ -> { A (posNat posKey) == get T posKey } @-}

------------------------------------------------------------------------------
-- | `abs` is a legitimate abstraction ---------------------------------------
------------------------------------------------------------------------------

-- | The empty Trie is equal to the empty TotalMap ---------------------------

{-@ lem_abs_emp :: EquivTrie (abs empty) empty @-}
lem_abs_emp :: Pos -> Proof
lem_abs_emp _ = ()


-- | A 'get' returns the same value as the 'abs' total map  ------------------

{-@ lem_abs_get :: t:_ -> EquivTrie (abs t) t @-}
lem_abs_get :: Trie v -> Pos -> Proof 
lem_abs_get t p =   abs t (posNat p) 
                -- === get t (natPos (posNat p)) 
                  ? lem_natPosNat p
                -- === get t p
                  *** QED

-- | A 'set' on a  Trie yields a 'set' on its abstraction --------------------

{-@ lem_abs_set :: t:_ -> p:_ -> v:_ -> 
      EquivTrie (T.set (abs t) (posNat p) (Just v)) (set t p v) 
  @-} 
lem_abs_set :: Trie v -> Pos -> v -> Pos -> Proof 
lem_abs_set t p v key = todo ()

{- 
lem_abs_set m k v key 
  | key == k  = () --  T.set (abs m) k (Just v) key
              ? T.lem_get_set_eq (abs m) k (Just v)  
              -- === Just v 
              ? lem_get_eq m k v
              -- === get m' key
              ? lem_abs_get m' key 
              -- === abs m' key 

  | otherwise = () -- T.set (abs m) k (Just v) key 
              ? T.lem_get_set_neq (abs m) k (Just v)
              -- === abs m key
              ? lem_abs_get m key
              -- === get m key
              ? lem_get_neq m key k v
              -- === get m' key
              ? lem_abs_get (set m k v) key
              -- === abs m' key 

  where m'    = set m k v

-}