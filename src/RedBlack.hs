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
           , tLeft  :: TreeLt tKey
           , tRight :: {t : TreeGt tKey | bh t == bh tLeft}
           }
  @-}

{-@ type TreeLt K = Tree {o:_| o < K} _ @-}

{-@ type TreeGt K = Tree {o:_| K < o} _ @-}


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

{-@ type RBT k v = {t:Tree k v | isRB t} @-}

{-@ reflect set @-} 
{-@ set :: RBT _ _ -> _ -> _ -> RBT _ _ @-}
set :: (Ord k) => Tree k v -> k -> v -> Tree k v 
set t k v = makeBlack (ins t k v) 

{-@ reflect makeBlack @-}
{-@ makeBlack :: {t:_ | isARB t} -> {res: _ | isRB res} @-}
makeBlack :: Tree k v -> Tree k v 
makeBlack Leaf             = Leaf  
makeBlack (Node _ k v l r) = Node B k v l r

{- ins :: (Ord a) => a -> t:RBT a -> {v: ARBTN a {bh t} | IsB t => isRB v} @-}

{-@ reflect ins @-} 
{-@ ins :: forall <p :: k -> Bool> . {t: Tree (k<p>) v | isRB t}  -> k<p> -> v -> {res : Tree (k<p>) v | isARB res && bh res = bh t && (isB t => isRB res) } @-}
ins :: (Ord k) => Tree k v -> k -> v -> Tree k v 
ins (Node c k v l r) key val
  | key < k      = bal c k v (ins l key val) r  -- c == R => isRB (ins l key val)
  | k < key      = bal c k v l (ins r key val)  -- c == R => isRB (ins r key val)
  | otherwise    = Node c key val l r 
ins Leaf key val = Node R key val Leaf Leaf

-- | Balancing ---------------------------------------------------------------

{-@ reflect bal @-}
{-@ bal :: c:_ -> k:_ -> _ -> {l:TreeLt k | c = R => isRB l} -> {r:TreeGt k | bh r = bh l && oneBad l r && (c = R => isRB r)} -> 
           {t:_ | isARB t && bh t = col c + bh l}
  @-}
bal :: Color -> k -> v -> Tree k v -> Tree k v -> Tree k v
bal R key val l r = Node R key val l r
bal B key val l r = blkbal key val l r 

{-@ reflect oneBad @-}
oneBad :: Tree k v -> Tree k v -> Bool
oneBad l r = (isARB l && isRB r) || (isRB l && isARB r)

{-@ reflect blkbal @-}
{-@ blkbal :: k:_ -> _ -> l:TreeLt k -> {r: TreeGt k | bh r = bh l && oneBad l r} -> 
      {res: _ | isRB res && bh res = 1 + bh l} 
  @-}
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
-- | RedBlack Props ----------------------------------------------------------
------------------------------------------------------------------------------

-- | Black-height Property ---------------------------------------------------

{-@ measure bh @-}
{-@ bh :: Tree k v -> Nat @-}
bh :: Tree k v -> Int
bh Leaf             = 0
bh (Node c k _ l r) = bh l + col c

{-@ reflect col @-}
col :: Color -> Int
col R = 0
col B = 1

-- | Red-Black invariant ------------------------------------------------------ 

{-@ measure isARB @-}
isARB :: Tree k v -> Bool
isARB Leaf             = True
isARB (Node _ _ _ l r) = isRB l && isRB r

{-@ measure isRB @-}
isRB :: Tree k v -> Bool
isRB Leaf             = True
isRB (Node c _ _ l r) = isRB l && isRB r && isNodeRB c l r 

{-@ inline isNodeRB @-}
isNodeRB :: Color -> Tree k v -> Tree k v -> Bool
isNodeRB c l r = c /= R || (isB l && isB r) 

{-@ measure isB @-}
isB :: Tree k v -> Bool
isB Leaf             = True 
isB (Node c _ _ l r) = c == B