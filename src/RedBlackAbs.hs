{-@ LIQUID "--reflection" @-} 
{-@ LIQUID "--ple"        @-} 
{-@ LIQUID "--diff"       @-} 

------------------------------------------------------------------------------
-- | Proofs that RedBlack.Tree implements a TotalMap i.e. Abs Props ---------- 
------------------------------------------------------------------------------

module RedBlackAbs where

import           ProofCombinators
import qualified TotalMaps as T
import           Prelude hiding (abs)
import           RedBlack 

{-# ANN module "HLint: ignore Use camelCase" #-}
{-# ANN module "HLint: ignore Use Eta reduce" #-}

-- | @mkb@ preserves the key-value relationship ------------------------------

{-@ lem_mkb :: t:_ -> key:_ -> { get (makeBlack t) key = get t key } @-}
lem_mkb ::  (Ord k) => Tree k v -> k -> Proof 
lem_mkb (Node c k v l r) key
  | key == k     = () 
  | key <  k     = ()
  | otherwise    = () 
lem_mkb Leaf key = ()

-- | @bal@ preserves the key-value relationship ------------------------------

{-@ lem_blkbal_lt :: k:_ -> v:_ -> l:TreeLt k -> r:TreeGt k -> key:{key < k} -> 
      { get (blkbal k v l r) key == get l key }
  @-}
lem_blkbal_lt :: (Ord k) => k -> v -> Tree k v -> Tree k v -> k -> Proof 
-- lem_blkbal_lt = todo "uncomment below, PLE-SLOW"

{- TODO:PLE-SLOW -}
lem_blkbal_lt k v (Node R ky vy (Node R kx vx a b) c) _ key 
  | key == ky                                               = ()
  | key > ky                                                = ()
  | key == kx                                               = ()
  | key <  kx                                               = ()
  | key >  kx                                               = ()
lem_blkbal_lt k v (Node R kx vx a (Node R ky vy b c)) _ key 
  | key == kx                                               = ()
  | key <  kx                                               = ()
  | key == ky                                               = ()
  | key <  ky                                               = ()
  | key >  ky                                               = ()
lem_blkbal_lt k v a (Node R kz vz (Node R ky vy b c) d) key = () 
lem_blkbal_lt k v a (Node R ky vy b (Node R kz vz c d)) key = ()  
lem_blkbal_lt k v l r                                   key = () 
{- -}

{-@ lem_blkbal_gt :: k:_ -> v:_ -> l:TreeLt k -> r:TreeGt k -> key:{k < key} -> 
      { get (blkbal k v l r) key == get r key }
  @-}
lem_blkbal_gt :: (Ord k) => k -> v -> Tree k v -> Tree k v -> k -> Proof 
{- lem_blkbal_gt = todo "uncomment below, PLE-SLOW" -}
{- TODO:PLE-SLOW -} 
lem_blkbal_gt k v (Node R ky vy (Node R kx vx a b) c) r key = () 
lem_blkbal_gt k v (Node R kx vx a (Node R ky vy b c)) r key = () 
lem_blkbal_gt k v a (Node R kz vz (Node R ky vy b c) d) key
  | key == kz                                               = ()
  | key >  kz                                               = () 
  | key == ky                                               = ()
  | key <  ky                                               = ()
  | key >  ky                                               = ()
lem_blkbal_gt k v a (Node R ky vy b (Node R kz vz c d)) key 
  | key == ky                                               = () 
  | key <  ky                                               = ()
  | key == kz                                               = () 
  | key <  kz                                               = () 
  | key >  kz                                               = () 
lem_blkbal_gt k v l r                                   key = () 
{- -}

{-@ lem_blkbal_eq :: k:_ -> v:_ -> l:TreeLt k -> r:TreeGt k -> key:{k = key} -> 
      { get (blkbal k v l r) key == Just v }
  @-}
lem_blkbal_eq :: (Ord k) => k -> v -> Tree k v -> Tree k v -> k -> Proof 
-- lem_blkbal_eq = todo "no, really do this"

lem_blkbal_eq k v (Node R ky vy (Node R kx vx a b) c) r key = () 
lem_blkbal_eq k v (Node R kx vx a (Node R ky vy b c)) r key = () 
lem_blkbal_eq k v a (Node R kz vz (Node R ky vy b c) d) key = ()
lem_blkbal_eq k v a (Node R ky vy b (Node R kz vz c d)) key = ()
lem_blkbal_eq k v l r                                   key = () 

-- | @bal@ preserves the key-value relationship -----------------------------

{-@ lem_bal_lt :: c:_ -> k:_ -> v:_ -> l:TreeLt k -> r:TreeGt k -> key:{key < k} -> 
      { get (bal c k v l r) key == get l key }
  @-}
lem_bal_lt :: (Ord k) => Color -> k -> v -> Tree k v -> Tree k v -> k -> Proof 
lem_bal_lt R k v l r key = ()
lem_bal_lt B k v l r key = lem_blkbal_lt k v l r key

{-@ lem_bal_gt :: c:_ -> k:_ -> v:_ -> l:TreeLt k -> r:TreeGt k -> key:{k < key} -> 
      { get (bal c k v l r) key == get r key }
  @-}
lem_bal_gt :: (Ord k) => Color -> k -> v -> Tree k v -> Tree k v -> k -> Proof 
lem_bal_gt R k v l r key = ()
lem_bal_gt B k v l r key = lem_blkbal_gt k v l r key

{-@ lem_bal_eq :: c:_ -> k:_ -> v:_ -> l:TreeLt k -> r:TreeGt k -> key:{k = key} -> 
      { get (bal c k v l r) key == Just v }
  @-}
lem_bal_eq :: (Ord k) => Color -> k -> v -> Tree k v -> Tree k v -> k -> Proof 
lem_bal_eq R k v l r key = ()
lem_bal_eq B k v l r key = lem_blkbal_eq k v l r key

-- | @ins@ preserves the key-value relationship --------------------------------

{-@ lem_ins_eq :: t:_ -> key:_ -> val:_ -> {get (ins t key val) key = Just val} @-}
lem_ins_eq ::  (Ord k) => Tree k v -> k -> v -> Proof 
lem_ins_eq Leaf key val             = ()
lem_ins_eq (Node c k v l r) key val 
  | key < k                         = lem_bal_lt c k v (ins l key val) r key &&& lem_ins_eq l key val
  | k < key                         = lem_bal_gt c k v l (ins r key val) key &&& lem_ins_eq r key val
  | otherwise                       = ()

-- | @get@ returns the value of the updated key -------------------------------

{-@ lem_get_eq :: (Ord k) => t:_ -> k:_ -> v:_ -> 
      {get (set t k v) k = Just v}
  @-}
lem_get_eq :: (Ord k) => Tree k v -> k -> v -> Proof
lem_get_eq t key val = get (set t key val) key 
                       ? lem_mkb (ins t key val)
                       ? lem_ins_eq t key val
                   === Just val 
                   *** QED

-- | @get@ preserves the values of other keys --------------------------------

{-@ lem_get_neq :: (Ord k) => t:_ -> k:_ -> v:_ -> key:{key /= k} -> 
      { get (set t k v) key = get t key }
  @-}
lem_get_neq :: (Ord k) => Tree k v -> k -> v -> k -> Proof
lem_get_neq t k v key 
    = get (set t k v) key 
  -- === get (makeBlack (ins t k v)) key
    ? lem_mkb (ins t k v) key 
  -- === get (ins t k v) key
    ? lem_ins_neq t k v key
  -- === get t key 
  *** QED

{-@ lem_ins_neq :: (Ord k) => t:_ -> k:_ -> v:_ -> key:{key /= k} -> 
      { get (ins t k v) key = get t key }
  @-}
lem_ins_neq :: (Ord k) => Tree k v -> k -> v -> k -> Proof
lem_ins_neq Leaf k v key = ()
lem_ins_neq (Node tc tk tv tl tr) k v key 
  | k == tk              = ()
  | k <  tk && key == tk = lem_bal_eq tc tk tv (ins tl k v) tr key
  | k <  tk && key >  tk = lem_bal_gt tc tk tv (ins tl k v) tr key
  | k <  tk && key <  tk =  () -- get (set t k v) key
                       -- === get (bal tc tk tv (ins tl k v) tr) key
                         ? lem_bal_lt tc tk tv (ins tl k v) tr key
                       -- === get (ins tl k v) key
                         ? lem_ins_neq tl k v key
                       -- === get tl key
                       -- *** QED
  | k >  tk && key == tk = lem_bal_eq tc tk tv tl (ins tr k v) key
  | k >  tk && key <  tk = lem_bal_lt tc tk tv tl (ins tr k v) key
  | k >  tk && key >  tk = () -- get (set t k v) key 
                        -- === get (bal tc tk tv tl (ins tr k v)) key 
                           ? lem_bal_gt tc tk tv tl (ins tr k v) key 
                        -- === get (ins tr k v) key
                           ? lem_ins_neq tr k v key
                        -- === get tr key
                        -- *** QED

-------------------------------------------------------------------------------
-- | Abstraction Function (same as SearchTree) --------------------------------
-------------------------------------------------------------------------------

type TMap k v = T.TotalMap k (Maybe v)

{-@ reflect abs @-}
abs :: (Ord k) => Tree k v -> TMap k v
abs (Node _ k v l r) key = combine k v (abs l) (abs r) key 
abs Leaf             key = Nothing

{-@ reflect combine @-}
combine :: (Ord k) => k -> v -> TMap k v -> TMap k v -> TMap k v 
combine key val lm rm k
  | k < key   = lm k 
  | key < k   = rm k
  | otherwise = Just val

------------------------------------------------------------------------------
-- | `abs` is a legitimate abstraction (same as SearchTree) ------------------
------------------------------------------------------------------------------

-- | The empty Map is equal to the empty TotalMap

{-@ lem_abs_emp :: ExtEq (abs emp) (T.def Nothing) @-}
lem_abs_emp :: k -> Proof 
lem_abs_emp _ = ()

-- | A 'get' returns the same value as the 'abs' total map 

{-@ lem_abs_get :: m:_ -> ExtEq (abs m) (get m)  @-} 
lem_abs_get :: (Ord k) => Tree k v -> k -> Proof 
lem_abs_get (Node _ k v l r) key 
  | key < k          = lem_abs_get l key 
  | k < key          = lem_abs_get r key 
  | otherwise        = () 
lem_abs_get Leaf key = ()

-- | A 'set' on a  Map' yields a 'set' on the abstraction

{-@ lem_abs_set :: m:_ -> k:_ -> v:_ -> 
      ExtEq (T.set (abs m) k (Just v)) (abs (set m k v)) 
  @-} 
lem_abs_set :: (Ord k) => Tree k v -> k -> v -> k -> Proof 
lem_abs_set m k v key 
  | key == k  = () --  T.set (abs m) k (Just v) key
              -- ? T.lem_get_set_eq (abs m) k (Just v)  
              -- === Just v 
              ? lem_get_eq m k v
              -- === get m' key
              ? lem_abs_get m' key 
              -- === abs m' key 

  | otherwise = () -- T.set (abs m) k (Just v) key 
              -- WHY NOT NEEDED ? T.lem_get_set_neq (abs m) k (Just v)
              -- === abs m key
              ? lem_abs_get m key
              -- === get m key
              ? lem_get_neq m k v key 
              -- === get m' key
              ? lem_abs_get (set m k v) key
              -- === abs m' key 

  where m'    = set m k v