{-@ LIQUID "--reflection"                          @-}
{-@ LIQUID "--ple"                                 @-}
{-@ LIQUID "--exactdc"                             @-}
{-@ LIQUID "--exact-data-con"                      @-}
{-@ LIQUID "--higherorder"                         @-}
{-@ LIQUID "--noadt"                               @-}

{-@ infix : @-}
{-@ infix ++ @-}

module Binom where
import Prelude hiding(abs, (++), succ, lookup, pred, compare, unzip, Maybe(..))
import Language.Haskell.Liquid.ProofCombinators 	
import Lists
import Language.Haskell.Liquid.Bag	
import Permutations 


data Maybe a = Just a | Nothing  deriving (Eq)


{-@ reflect isJust @-}
isJust :: Maybe a -> Bool  
isJust (Just _) = True 
isJust Nothing  = False 


{-@ measure fromJust @-}
{-@ fromJust :: {v:Maybe a | isJust v } -> a @-}
fromJust :: Maybe a -> a 
fromJust (Just x) = x 


{-@ type Key = Nat@-}
type Key = Int

data Pair a b = P a b deriving (Eq, Ord)

data Tree = Leaf | Node Key Tree Tree deriving (Eq, Ord)
 
{-@
data Tree [tlen] = Leaf
  | Node { key    :: Nat
         , tLeft  :: Tree
         , tRight :: Tree }
@-}


{-@ measure tlen @-}
tlen :: Tree  -> Int
{-@ tlen :: Tree -> Nat @-}
tlen (Leaf)        = 0
tlen (Node key l r) = 1 + (tlen l) + (tlen r)


{-@ type Priqueue = [Tree] @-}
type Priqueue = [Tree]


{-@ reflect p_empty @-}
p_empty :: [Tree]
p_empty = []


{-@ reflect smash @-}
smash :: Tree -> Tree -> Tree
smash (Node x t1 Leaf) (Node y u1 Leaf) = if (x>y) then Node x (Node y u1 t1) Leaf
                                          else Node y (Node x t1 u1) Leaf
smash _ _ = Leaf                                           


{-@ reflect carry @-}
{-@ carry :: Priqueue -> Tree -> Priqueue @-}
carry :: [Tree] -> Tree -> [Tree]
carry []        Leaf = []
carry []        t    = [t]
carry (Leaf:q') t    = (t:q')
carry (u:q')    Leaf = (u:q')
carry (u:q')    t    = Leaf:carry q' (smash t u)


{-@ reflect insert @-}
{-@ insert :: Nat -> Priqueue -> Priqueue @-}
insert :: Key -> Priqueue -> Priqueue
insert x q = carry q (Node x Leaf Leaf)


{-@ reflect join @-}
join :: Priqueue -> Priqueue -> Tree -> Priqueue
join []       q        c            = carry q c
join p        []       c            = carry p c
join (Leaf:p) (Leaf:q) c            = c    : join p q Leaf
join (Leaf:p) (q1:q)   (Leaf)       = q1   : join p q Leaf
join (Leaf:p) (q1:q)   (Node k l r) = Leaf : join p q (smash (Node k l r) q1)
join (p1:p)   (Leaf:q) (Leaf)       = p1   : join p q Leaf
join (p1:p)   (Leaf:q) (Node k l r) = Leaf : join p q (smash (Node k l r) p1)
join (p1:p)   (q1:q)   c            = c    : join p q (smash p1 q1)


{-@ reflect unzip@-}
unzip:: Tree -> Priqueue -> Priqueue
unzip Leaf           cont = cont 
unzip (Node x t1 t2) cont = unzip t2 ( (Node x t1 Leaf) : cont )


{-@ reflect heap_delete_max @-}
heap_delete_max :: Tree -> Priqueue
heap_delete_max (Node x t1 Leaf) = unzip t1 []
heap_delete_max  _               = []
 

{-@ reflect find_max'@-}
{-@find_max' :: Priqueue -> Key -> Nat @-}
find_max' :: Priqueue -> Key -> Key 
find_max' []               current  = current
find_max' (Leaf:q)         current  = find_max' q current
find_max' ((Node x _ _):q) current  = if(x>current) then find_max' q x else find_max' q current


{-@ reflect node_toKey @-}
{-@ node_toKey :: t:{Tree | t/= Leaf} -> Key @-}
node_toKey :: Tree -> Key
node_toKey (Node k l r) = k


{-@ reflect find_max @-}
{-@ find_max :: p:Priqueue -> Maybe Nat  @-}
find_max :: Priqueue -> Maybe Key
find_max []               = Nothing
find_max (Leaf:q)         = find_max q  
find_max ((Node x _ _):q) = Just (find_max' q x)


{-@ reflect delete_max_aux@-}
delete_max_aux :: Priqueue -> Key -> (Pair Priqueue Priqueue)
delete_max_aux (Leaf: p)            m = (P (Leaf:(fst1 (delete_max_aux p m))) (snd1 (delete_max_aux p m)))
delete_max_aux ((Node x t1 Leaf):p) m = if(m>x) then (P ((Node x t1 Leaf):(fst1 (delete_max_aux p m))) (snd1 (delete_max_aux p m))) 
                                        else (P (Leaf:p) (heap_delete_max (Node x t1 Leaf)))
delete_max_aux  _                   m = (P [] [])



{-@ reflect snd1 @-}
snd1 :: (Pair a b) -> b
snd1 (P a b) = b


{-@ reflect fst1 @-}
fst1 :: (Pair a b) -> a
fst1 (P a b) = a


{-@ reflect delete_max @-}
delete_max :: Priqueue -> Maybe (Pair Key Priqueue)
delete_max q  
          | (isJust k) = Just (P (fromJust k) (join  (fst1 (delete_max_aux q (fromJust k)))  (snd1 (delete_max_aux q (fromJust k)))  Leaf))  
          | otherwise = Nothing   
             where k = (find_max q)


{-@ reflect merge @-}
merge:: Priqueue -> Priqueue -> Priqueue
merge p q = join p q Leaf


{-@ reflect pow2heap' @-}
{-@ pow2heap':: Nat -> Key -> Tree -> Bool @-}
pow2heap':: Int -> Key -> Tree -> Bool
pow2heap' 0 m Leaf         = True 
pow2heap' 0 m (Node _ _ _) = False
pow2heap' n m Leaf         = False
pow2heap' n m (Node k l r) = (m >= k) && pow2heap' (n-1) k l && pow2heap' (n-1) m r


{-@ reflect pow2heap @-}
{-@ pow2heap :: Nat -> Tree -> Bool @-}
pow2heap :: Int -> Tree -> Bool
pow2heap n (Node m t1 Leaf) = pow2heap' n m t1
pow2heap n _                = False


{-@ reflect priq'@-}
{-@ priq' ::  [Tree] -> Nat -> Bool @-}
priq' :: [Tree] -> Int -> Bool
priq' (t:l) i = (t==Leaf || pow2heap i t) && priq' l (i+1) 
priq' _     i = True



{-@ reflect priq@-}
{-@ priq ::  Priqueue ->  Bool @-}
priq :: Priqueue -> Bool
priq q = priq' q 0

--------------------------------------------------------------------------------------------------

{-@ thm_empty_priq :: {priq p_empty} @-}
thm_empty_priq :: Proof
thm_empty_priq = trivial


{-@ thm_smash_valid :: n: Nat -> t:{Tree | pow2heap n t } -> u:{Tree | pow2heap n u } -> { pow2heap (n+1) (smash t u) } @-}
thm_smash_valid :: Int -> Tree -> Tree -> Proof
thm_smash_valid n t u = trivial


{-@ thm_carry_valid :: n: Nat -> q: {Priqueue | priq' q n}-> t: {Tree | t == Leaf || pow2heap n t} -> { priq' (carry q t) n} @-}
thm_carry_valid :: Int ->  Priqueue -> Tree -> Proof
thm_carry_valid n []     Leaf = trivial
thm_carry_valid n (q:qs) Leaf = trivial
thm_carry_valid n []     t    = trivial
thm_carry_valid n (q:qs) t   | q== Leaf =   priq' (carry (Leaf:qs) t) n
                                        === priq' (t:qs) n
                                        === True *** QED
                              
                             |otherwise = priq' (carry (q:qs) t) n
                                        === priq' (Leaf:carry qs (smash t q)) n
                                        === ((Leaf==Leaf || pow2heap n Leaf) && priq' (carry qs (smash t q)) (n+1))
                                            ? thm_carry_valid (n+1) qs (smash t q)
                                        === True    
                                        *** QED


{-@ thm_insert_priq :: x: Key -> q: {Priqueue | priq q} -> { priq (insert x q) } @-}
thm_insert_priq :: Key -> Priqueue -> Proof
thm_insert_priq x q =   (pow2heap 0 (Node x Leaf Leaf) , thm_carry_valid 0 q (Node x Leaf Leaf)) *** QED
             

{-@ thm_join_valid :: n:Nat -> p :{Priqueue | priq' p n} -> q:{Priqueue | priq' q n} -> c : {Tree | (c==Leaf || pow2heap n c)} 
    -> {priq'(join p q c) n} 
@-}
thm_join_valid :: Int -> Priqueue -> Priqueue -> Tree -> Proof
thm_join_valid n []        q       c            =   priq' (join [] q c) n
                                                === priq' (carry q c) n ? thm_carry_valid n q c 
                                                === True     
                                                *** QED

thm_join_valid n  p        []      c            =   priq' (join p [] c) n
                                                === priq' (carry p c) n ? thm_carry_valid n p c
                                                === True     
                                                *** QED

thm_join_valid n (Leaf:p) (Leaf:q) c            =   priq' (join (Leaf:p) (Leaf:q) c) n
                                                === priq' (c:join p q Leaf) n
                                                === (  (c==Leaf || pow2heap n c) && priq' (join p q Leaf) (n+1)) ? thm_join_valid (n+1) p q Leaf
                                                === True   
                                                *** QED

thm_join_valid n (Leaf:p) (q1:q)   Leaf         =   priq' (join (Leaf:p) (Leaf:q) Leaf) n
                                                === priq' ( q1   : join p q Leaf ) n
                                                === (  (q1==Leaf || pow2heap n q1) && priq' (join p q Leaf) (n+1)) ? thm_join_valid (n+1) p q Leaf
                                                === True  
                                                *** QED

thm_join_valid n  (Leaf:p) (q1:q)  (Node k l r) = priq' (join (Leaf:p) (q1:q) (Node k l r) ) n
                                                ===  priq' ( Leaf : join p q (smash (Node k l r) q1) ) n
                                                === (  (Leaf==Leaf || pow2heap n Leaf) && priq' (join p q (smash (Node k l r) q1)) (n+1)) 
                                                  ? thm_join_valid (n+1) p q (smash (Node k l r) q1)
                                                === (True && True)   
                                                *** QED

thm_join_valid n (p1:p)   (Leaf:q) (Leaf)       =   priq' (join (p1:p)   (Leaf:q) (Leaf)) n
                                                === priq' ( p1   : join p q Leaf ) n
                                                ===  (  (p1==Leaf || pow2heap n p1) &&  priq' (join p q Leaf) (n+1))
                                                  ? thm_join_valid (n+1) p q Leaf
                                                === True   
                                                *** QED

thm_join_valid n (p1:p)   (Leaf:q) (Node k l r) =   priq' (join (p1:p)   (Leaf:q) (Node k l r)) n
                                                === priq' ( Leaf : join p q (smash (Node k l r) p1) ) n
                                                ===  (  (Leaf==Leaf || pow2heap n Leaf) &&  priq' (join p q (smash (Node k l r) p1)) (n+1))
                                                   ? thm_join_valid (n+1) p q (smash (Node k l r) p1)
                                                === True  
                                                *** QED

thm_join_valid n (p1:p)   (q1:q)   c            =   priq' (join (p1:p)   (q1:q)   c  ) n
                                                === priq' ( c : join p q (smash p1 q1) ) n
                                                ===  (  (c==Leaf || pow2heap n c) &&  priq' ( join p q (smash p1 q1) ) (n+1))
                                                    ? thm_join_valid (n+1) p q (smash p1 q1)
                                                === True  
                                                *** QED
