{-@ LIQUID "--reflection" @-} 
{-@ LIQUID "--ple"        @-} 
{- LIQUID "--diff"       @-} 

module RedBlack where

import           ProofCombinators
import qualified TotalMaps as T

import Prelude hiding (abs)

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
{-@ blkbal :: k:_ -> _ -> Tree {o:_|o < k} _ -> Tree {o:_| k < o} _ -> _ @-}
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

-- | Eery `t :: Tree k v` is a `searchTree` ---------------------------------- 
lem_searchtree :: (Ord k) => Tree k v -> Bool
lem_searchtree t = searchTree t == True 

------------------------------------------------------------------------------
-- | Abs Props ---------------------------------------------------------------
------------------------------------------------------------------------------

{-@ lem_mkb :: t:_ -> k:_ -> { get (makeBlack t) k = get t k } @-}
lem_mkb ::  (Ord k) => Tree k v -> k -> Proof 
lem_mkb (Node c k v l r) key
  | key == k     = () 
  | key <  k     = ()
  | otherwise    = () 
lem_mkb Leaf key = ()

{-@ lem_ins_eq :: t:_ -> k:_ -> v:_ -> { get (ins t k v) k = Just v } @-}
lem_ins_eq ::  (Ord k) => Tree k v -> k -> v -> Proof 
lem_ins_eq = undefined

{-@ lem_get_eq :: (Ord k) => t:_ -> k:_ -> v:_ -> 
      {get (set t k v) k = Just v}
  @-}
lem_get_eq :: (Ord k) => Tree k v -> k -> v -> Proof
lem_get_eq t key val =   get (set t key val) key 
                       ? lem_mkb (ins t key val)
                       ? lem_ins_eq t key val
                     === Just val 
                     *** QED

------------------------------------------------------------------------------
-- | RedBlack Props ----------------------------------------------------------
------------------------------------------------------------------------------
-- TODO 







{- 
ins (Node B k v l r) key val                                -- Root is Black 
  | key < k      = lbal k v (ins l key val) r
  | k < key      = rbal k v l (ins r key val)
  | otherwise    = Node B key val l r 

ins (Node R k v l r) key val                                -- Root is Red
  | key < k      = Node R k v (ins l key val) r
  | k < key      = Node R k v l (ins r key val) 
  | otherwise    = Node R key val l r 

{-@ reflect lbal @-}
{- lbal :: k:a -> l:ARBT {v:a | v < k} -> RBTN {v:a | k < v} {bh l} -> RBTN a {1 + bh l} @-}
lbal k v (Node R ky vy (Node R kx vx a b) c) r  = Node R ky vy (Node B kx vx a b) (Node B k v c r)
lbal k v (Node R kx vx a (Node R ky vy b c)) r  = Node R ky vy (Node B kx vx a b) (Node B k v c r)
lbal k v l r                                    = Node B k l r

{-@ reflect rbal @-}
{- rbal :: k:a -> l:RBT {v:a | v < k} -> ARBTN {v:a | k < v} {bh l} -> RBTN a {1 + bh l} @-}
rbal k v a (Node R ky vy b (Node R kz vz c d))  = Node R ky vy (Node B kx vx a b) (Node B kz vz c d)
rbal k v a (Node R kz vz (Node R ky vy b c) d)  = Node R ky vy (Node B kx vx a b) (Node B kz vz c d)
rbal k v l r                                    = Node B k v l r
-}