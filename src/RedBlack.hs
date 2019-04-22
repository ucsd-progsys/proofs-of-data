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
           , tRight :: {t : Tree {o:k | tKey < o} v | bh t == bh tLeft}
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
{-@ ins :: forall <p :: k -> Bool> . t: Tree (k<p>) v -> k<p> -> v -> {res : Tree (k<p>) v | bh res = bh t } @-}
ins :: (Ord k) => Tree k v -> k -> v -> Tree k v 
ins (Node c k v l r) key val
  | key < k      = bal c k v (ins l key val) r
  | k < key      = bal c k v l (ins r key val)
  | otherwise    = Node c key val l r 
ins Leaf key val = Node R key val Leaf Leaf

-- | Balancing ---------------------------------------------------------------

{-@ reflect bal @-}
{-@ bal :: forall <p :: k -> Bool>.
             c:_ -> 
             key:k<p> -> 
             _ ->
             l:Tree {o:k<p>|o < key} _ -> 
             {tt: Tree {o:k<p>| key < o} _ | bh tt = bh l} -> 
             {res : Tree (k<p>) v | bh res = col c + bh l}
  @-}
bal :: Color -> k -> v -> Tree k v -> Tree k v -> Tree k v
bal R key val l r = Node R key val l r 
bal B key val l r = blkbal key val l r 

{-@ reflect blkbal @-}
{-@ blkbal :: k:_ -> _ -> l:TreeLt k -> {r: TreeGt k | bh r = bh l} -> {res: _ | bh res = 1 + bh l} @-}
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

{-@ type TreeLt K = Tree {o:_| o < K} _ @-}
{-@ type TreeGt K = Tree {o:_| K < o} _ @-}

------------------------------------------------------------------------------
-- | RedBlack Props ----------------------------------------------------------
------------------------------------------------------------------------------

{-@ measure bh @-}
{-@ bh :: Tree k v -> Nat @-}
bh :: Tree k v -> Int
bh Leaf             = 0
bh (Node c k _ l r) = bh l + col c -- if c == R then 0 else 1

{-@ reflect col @-}
col :: Color -> Int
col R = 0
col B = 1

-- TODO 

{- 
-- {-@ lbal                              :: k:a -> l:ARBT {v:a | v < k} -> RBTN {v:a | k < v} {bh l} -> RBTN a {1 + bh l} @-}
-- {-@ rbal                              :: k:a -> l:RBT {v:a | v < k} -> ARBTN {v:a | k < v} {bh l} -> RBTN a {1 + bh l} @-}

{-@ measure isBH        :: RBTree a -> Bool
    isBH (Leaf)         = true
    isBH (Node c x l r) = (isBH l && isBH r && bh l = bh r)
  @-}

{-@ measure isARB        :: (RBTree a) -> Bool
    isARB (Leaf)         = true
    isARB (Node c x l r) = (isRB l && isRB r)
  @-}
{-@ measure isRB        :: RBTree a -> Bool
    isRB (Leaf)         = true
    isRB (Node c x l r) = isRB l && isRB r && (c == R => (IsB l && IsB r))
  @-}
{-@ measure isB        :: RBTree a -> Bool
    isB (Leaf)         = false
    isB (Node c x l r) = c == B
  @-}




-}

