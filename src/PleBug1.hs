{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}

{-@ infixr ++ @-}

data Pos    = XH | X Bool Pos 

data Trie a = Leaf | Node (Maybe a) (Trie a) (Trie a)

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

{-@ ex_trie :: _ -> TT @-}
ex_trie _ = get t2 k2  == Just 675
  where 
    t1    = set Leaf k2 99
    t2    = set t1   k2 675
    k2    = X False XH
