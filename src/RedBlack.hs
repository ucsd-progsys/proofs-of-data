{-@ LIQUID "--reflection" @-} 
{-@ LIQUID "--ple"        @-} 
{-@ LIQUID "--diff"       @-} 

module RedBlack where

import           ProofCombinators
import qualified TotalMaps as T
import           Prelude hiding (abs)

{-# ANN module "HLint: ignore Use camelCase" #-}
{-# ANN module "HLint: ignore Use Eta reduce" #-}

{-@ data Tree k v = 
      Leaf 
    | Node { tCol   :: Color 
           , tKey   :: k 
           , tVal   :: v 
           , tLeft  :: Tree {o:k | o < tKey} v 
           , tRight :: Tree {o:k | tKey < o} v
           }
  @-}

------------------------------------------------------------------------------
-- | Red Black Trees ---------------------------------------------------------
------------------------------------------------------------------------------

data Color = R | B 
  deriving (Eq)

data Tree k v 
  = Leaf 
  | Node Color k v (Tree k v) (Tree k v) 

{-@ measure size @-}
{-@ size :: Tree k v -> Nat @-}
size :: Tree k v -> Int
size Leaf             = 0
size (Node _ _ _ l r) = 1 + size l + size r    

------------------------------------------------------------------------------
-- | Tree Operations ---------------------------------------------------------
------------------------------------------------------------------------------

{-@ reflect emp @-}
emp :: Tree k v
emp = Leaf 

{-@ reflect get @-}
get :: (Ord k) => Tree k v -> k -> Maybe v
get (Node _ k v l r) key
  | key == k  = Just v
  | key <  k  = get l key
  | otherwise = get r key
get Leaf _    = Nothing 

------------------------------------------------------------------------------
-- | Insertion ---------------------------------------------------------------
------------------------------------------------------------------------------

{-@ reflect set @-} 
set :: (Ord k) => Tree k v -> k -> v -> Tree k v 
set t k v = makeBlack (ins t k v) 

{-@ reflect makeBlack @-}
makeBlack :: Tree k v -> Tree k v 
makeBlack Leaf             = Leaf  
makeBlack (Node _ k v l r) = Node B k v l r

{- ins :: (Ord a) => a -> t:RBT a -> {v: ARBTN a {bh t} | IsB t => isRB v} @-}

{-@ reflect ins @-} 
{-@ ins :: forall <p :: k -> Bool> . Tree (k<p>) v -> k<p> -> v -> Tree (k<p>) v @-}
ins :: (Ord k) => Tree k v -> k -> v -> Tree k v 
ins (Node c k v l r) key val
  | key < k      = bal c k v (ins l key val) r
  | k < key      = bal c k v l (ins r key val)
  | otherwise    = Node B key val l r 
ins Leaf key val = Node R key val Leaf Leaf

-- | Balancing ---------------------------------------------------------------

{-@ reflect bal @-}
{-@ bal :: forall <p :: k -> Bool>._ -> key:k<p> -> _ ->
             Tree {o:k<p>|o < key} _ -> Tree {o:k<p>| key < o} _ -> Tree (k<p>) v 
  @-}
bal :: Color -> k -> v -> Tree k v -> Tree k v -> Tree k v
bal R key val l r = Node R key val l r 
bal B key val l r = blkbal key val l r 

{-@ reflect blkbal @-}
-- {-@ blkbal :: k:_ -> _ -> Tree {o:_|o < k} _ -> Tree {o:_| k < o} _ -> _ @-}
{-@ blkbal :: k:_ -> _ -> TreeLt k -> TreeGt k -> _ @-}
blkbal :: k -> v -> Tree k v -> Tree k v -> Tree k v
blkbal k v (Node R ky vy (Node R kx vx a b) c) r  = Node R ky vy (Node B kx vx a b) (Node B k v c r)
blkbal k v (Node R kx vx a (Node R ky vy b c)) r  = Node R ky vy (Node B kx vx a b) (Node B k v c r)
blkbal k v a (Node R kz vz (Node R ky vy b c) d)  = Node R ky vy (Node B k v a b) (Node B kz vz c d)
blkbal k v a (Node R ky vy b (Node R kz vz c d))  = Node R ky vy (Node B k v a b) (Node B kz vz c d)
blkbal k v l r                                    = Node B k v l r

------------------------------------------------------------------------------
-- | SearchTree Property -----------------------------------------------------
------------------------------------------------------------------------------

{-@ searchTree :: _  -> TT @-} 
searchTree :: (Ord k) => Tree k v -> Bool 
searchTree Leaf             = True  
searchTree (Node _ k v l r) =  all_keys   l (< k) 
                            && all_keys   r (k <) 
                            && searchTree l 
                            && searchTree r

{-@ all_keys :: forall <p :: k -> Bool>. Tree (k<p>) v -> (k<p> -> TT) -> TT @-} 
all_keys :: Tree k v -> (k -> Bool) -> Bool
all_keys Leaf _             = True 
all_keys (Node _ k _ l r) p = p k && all_keys l p && all_keys r p

-- | Every `t :: Tree k v` is a `searchTree` ---------------------------------- 

{-@ lem_searchtree :: t:_ -> TT @-}
lem_searchtree :: (Ord k) => Tree k v -> Bool
lem_searchtree = searchTree

------------------------------------------------------------------------------
-- | Abs Props ---------------------------------------------------------------
------------------------------------------------------------------------------

-- | @mkb@ preserves the key-value relationship ------------------------------

{-@ lem_mkb :: t:_ -> key:_ -> { get (makeBlack t) key = get t key } @-}
lem_mkb ::  (Ord k) => Tree k v -> k -> Proof 
lem_mkb (Node c k v l r) key
  | key == k     = () 
  | key <  k     = ()
  | otherwise    = () 
lem_mkb Leaf key = ()

-- | @bal@ preserves the key-value relationship ------------------------------

{-@ type TreeLt K = Tree {o:_| o < K} _ @-}
{-@ type TreeGt K = Tree {o:_| K < o} _ @-}

{-@ lem_blkbal_lt :: k:_ -> v:_ -> l:TreeLt k -> r:TreeGt k -> key:{key < k} -> 
      { get (blkbal k v l r) key == get l key }
  @-}
lem_blkbal_lt :: (Ord k) => k -> v -> Tree k v -> Tree k v -> k -> Proof 
lem_blkbal_lt = todo ()

{- TODO:PLE-SLOW
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
-}

{-@ lem_blkbal_gt :: k:_ -> v:_ -> l:TreeLt k -> r:TreeGt k -> key:{k < key} -> 
      { get (blkbal k v l r) key == get r key }
  @-}
lem_blkbal_gt :: (Ord k) => k -> v -> Tree k v -> Tree k v -> k -> Proof 
lem_blkbal_gt = todo ()

{- TODO:PLE-SLOW 
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
-}

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
lem_ins_neq = todo ()

{- 
lem_get_neq t k v key 
  | key < k = get (set t k v) key 
  | k < key = get (set t k v) key   
  ==! 

 -}
------------------------------------------------------------------------------
-- | RedBlack Props ----------------------------------------------------------
------------------------------------------------------------------------------
-- TODO 