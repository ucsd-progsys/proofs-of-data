{-@ LIQUID "--reflection"                          @-}
{-@ LIQUID "--ple"                                 @-}
{-@ LIQUID "--exactdc"                             @-}
{-@ LIQUID "--exact-data-con"                      @-}
{-@ LIQUID "--higherorder"                         @-}
{-@ LIQUID "--noadt"                               @-}

{-@ infix : @-}
{-@ infix ++ @-}

module Binom2 where
import Prelude hiding(abs, (++), succ, lookup, pred, compare, unzip, Maybe(..))
import Language.Haskell.Liquid.ProofCombinators 	
import Language.Haskell.Liquid.Bag	
import Permutations 
import Lists
import Binom 




{-@ thm_merge_priq :: p: {Priqueue | priq p} -> q: {Priqueue | priq q} -> {priq (merge p q)} @-}
thm_merge_priq :: Priqueue -> Priqueue -> Proof
thm_merge_priq p q = [thm_join_valid 0 p q Leaf] *** QED


{-@ thm_delete_max_Some_priq_aux :: n:Int ->  p:{Priqueue | priq' p n} -> m:Int-> { priq' (fst1( delete_max_aux p m)) n} @-}
thm_delete_max_Some_priq_aux :: Int -> Priqueue -> Key -> Proof
thm_delete_max_Some_priq_aux n []       m = trivial
thm_delete_max_Some_priq_aux n (Leaf:p) m = thm_delete_max_Some_priq_aux (n+1) p m
thm_delete_max_Some_priq_aux n ((Node x t1 Leaf):p) m 
                              | m>x       =   thm_delete_max_Some_priq_aux (n+1) p m
                              | otherwise = thm_delete_max_Some_priq_aux (n+1) p m
thm_delete_max_Some_priq_aux n p m        =  trivial


{-@ thm_delete_max_Some_priq_aux2 :: p:Priqueue -> m:Int-> { priq (snd1( delete_max_aux p m))  }@-}
thm_delete_max_Some_priq_aux2 :: Priqueue -> Key -> Proof
thm_delete_max_Some_priq_aux2  [] m       = trivial
thm_delete_max_Some_priq_aux2  (Leaf:p) m =  thm_delete_max_Some_priq_aux2 p m                   
thm_delete_max_Some_priq_aux2  ((Node x t1 Leaf):p) m 
                              | m>x       =   thm_delete_max_Some_priq_aux2 p m
                              | otherwise = todo "this"
thm_delete_max_Some_priq_aux2 p m         =  trivial  

{-@ thm_delete_max_Some_priq:: p: {Priqueue | priq p &&  delete_max p /= Nothing } -> {priq' (snd1 (fromJust ( delete_max p ))) 0} @-}
thm_delete_max_Some_priq :: Priqueue -> Proof
thm_delete_max_Some_priq []  = trivial
thm_delete_max_Some_priq p 
                            | isJust(find_max p) 
       =   priq' (snd1 (fromJust ( delete_max p ))) 0
       === priq' (snd1 ( fromJust (   Just (P (fromJust (find_max p)) (join  (fst1 (delete_max_aux p (fromJust (find_max p))))  (snd1 (delete_max_aux p (fromJust (find_max p))))  Leaf))    ))) 0
       === priq' (snd1 (   (P (fromJust (find_max p)) (join  (fst1 (delete_max_aux p (fromJust (find_max p))))  (snd1 (delete_max_aux p (fromJust (find_max p))))  Leaf))   ))  0               
       === priq' (  (join  (fst1 (delete_max_aux p (fromJust (find_max p))))  (snd1 (delete_max_aux p (fromJust (find_max p))))  Leaf)    ) 0
        ?  ( thm_delete_max_Some_priq_aux 0 p (fromJust(find_max p))) &&& ( thm_delete_max_Some_priq_aux2  p (fromJust(find_max p))) &&&   (thm_join_valid  0 (fst1 (delete_max_aux p (fromJust (find_max p))))  (snd1 (delete_max_aux p (fromJust (find_max p))))  Leaf) 
       === True
       *** QED  
                            | otherwise = trivial


{-@ reflect elements @-}
{-@ elements:: Tree -> [Nat]  @-}
elements:: Tree -> [Key] 
elements Leaf = []
elements (Node k l r)  = k: ((elements l) ++ (elements r))

{-@ reflect tree_elems @-}
{-@ tree_elems :: Tree -> [Nat] -> Bool @-}
tree_elems :: Tree -> [Key] -> Bool
tree_elems t    l  = permutation (elements t) l


{-@ thmPermProp :: xs:[a] -> ys:{[a] | permutation xs ys} -> zs:{[a] | permutation xs zs} -> {permutation ys zs } @-}
thmPermProp:: (Ord a) => [a] -> [a] -> [a] -> Proof
thmPermProp xs ys zs = trivial

{-@ thm_tree_elems_ext :: t:Tree -> e1: { [Key] | tree_elems t e1} -> e2:{ [Key] | permutation e1 e2} -> {tree_elems t e2 } @-}
thm_tree_elems_ext :: Tree -> [Key] -> [Key] -> Proof
thm_tree_elems_ext t e1 e2 = [thmPermProp (elements t) e1 e2] *** QED


{-@ thm_tree_perm :: t:Tree -> e1: { [Key] | tree_elems t e1} -> e2:{ [Key] | tree_elems t e2} -> {permutation e1 e2 } @-}
thm_tree_perm :: Tree -> [Key] -> [Key] -> Proof
thm_tree_perm t e1 e2 = [thmPermProp (elements t) e1 e2] *** QED


{-@ thmAppNilR :: xs:[a] -> {( xs ++ []) = xs } @-}
thmAppNilR :: [a] -> Proof
thmAppNilR [] = trivial
thmAppNilR (x:xs) = thmAppNilR xs


{-@ thm_smash_elems2 ::  t: Tree -> u:{Tree | smash t u /= Leaf}
      -> {bag (elements (smash t u)) = union (bag (elements u)) (bag (elements t)) } 
@-}
thm_smash_elems2 :: Tree -> Tree  -> Proof
thm_smash_elems2  Leaf                Leaf                = trivial
thm_smash_elems2  Leaf                u                   = trivial
thm_smash_elems2  t                   Leaf                = trivial
thm_smash_elems2  (Node m1 t1 Leaf) (Node m2 u1 (Node _ _ _)) = trivial
thm_smash_elems2  (Node m1 t1 (Node _ _ _)) (Node m2 u1 Leaf) = trivial
thm_smash_elems2  (Node m1 t1 Leaf) (Node m2 t2 Leaf) 
                      | m1 > m2    =   bag (elements (smash (Node m1 t1 Leaf) (Node m2 t2 Leaf))) 
                                   === bag (elements (Node m1 (Node m2 t2 t1) Leaf)) 
                                   === bag (m1: (elements (Node m2 t2 t1) ++ (elements Leaf) ))
                                   === bag (m1: (elements (Node m2 t2 t1) ++ [] ))  ? thmAppNilR  (elements (Node m2 t2 t1))
                                   === bag (m1: (elements (Node m2 t2 t1)) ) 
                                   === bag (m1: (m2 :(elements t2 ++ elements t1)) ) ? appendBag2 m1 m2 (elements t2)  (elements t1)
                                   === union (bag (m2: elements t2)) (bag (m1: elements t1))  ?thmAppNilR  (elements t2 ) &&& thmAppNilR  (elements t1 )
                                   === union (bag (m2: (elements t2 ++ []) )) (bag (m1: (elements t1 ++ []))) 
                                   === union (bag (m2: (elements t2 ++ (elements Leaf)) )) (bag (m1: (elements t1 ++ (elements Leaf)))) 
                                   === union (bag ( elements (Node m2 t2 Leaf) )) (bag ( elements (Node m1 t1 Leaf) )) 
                                   *** QED
                       | otherwise =   bag (elements (smash (Node m1 t1 Leaf) (Node m2 t2 Leaf))) 
                                   === bag (elements (Node m2 (Node m1 t1 t2) Leaf)) 
                                   === bag (m2: (elements (Node m1 t1 t2) ++ (elements Leaf) ))
                                   === bag (m2: (elements (Node m1 t1 t2) ++ [] )) ? thmAppNilR  (elements (Node m1 t1 t2))
                                   === bag (m2: (elements (Node m1 t1 t2)) ) 
                                   === bag (m2: (m1 :(elements t1 ++ elements t2)) ) ? appendBag3 m2 m1 (elements t1)  (elements t2)
                                   === union (bag (m2: elements t2)) (bag (m1: elements t1)) ? thmAppNilR  (elements t2 ) &&& thmAppNilR  (elements t1 )
                                   === union (bag (m2: (elements t2 ++ []) )) (bag (m1: (elements t1 ++ []))) 
                                   === union (bag (m2: (elements t2 ++ (elements Leaf)) )) (bag (m1: (elements t1 ++ (elements Leaf)))) 
                                   === union (bag ( elements (Node m2 t2 Leaf) )) (bag ( elements (Node m1 t1 Leaf) )) 
                                   *** QED             




{-@ appendBag2 ::(Eq k, Ord k) => x:k -> y:k -> as:[k] -> bs:[k] -> {bag (x:(y:(as ++ bs))) == union (bag (y:as)) (bag (x:bs)) } @-}
appendBag2 :: (Eq k, Ord k) => k-> k-> [k] -> [k] -> Proof
appendBag2 x y [] _      = ()       
appendBag2 x y  (_:as) bs = appendBag2 x y  as bs 

{-@ appendBag3 ::(Eq k, Ord k) => x:k -> y:k -> as:[k] -> bs:[k] -> {bag (x:(y:(as ++ bs))) == union (bag (x:as)) (bag (y:bs)) } @-}
appendBag3 :: (Eq k, Ord k) => k-> k-> [k] -> [k] -> Proof
appendBag3 x y [] _      = ()       
appendBag3 x y  (_:as) bs = appendBag3 x y  as bs 


{-@ thm_smash_elems :: n:Int -> t: {Tree | pow2heap n t} -> u:{Tree | pow2heap n u} -> bt:{[Key] | tree_elems t bt} 
                             -> bu:{[Key]| tree_elems u bu} -> {tree_elems (smash t u) (bt ++ bu) } @-}
thm_smash_elems :: Int -> Tree -> Tree -> [Key] -> [Key] -> Proof
thm_smash_elems n Leaf Leaf bt bu = trivial 
thm_smash_elems n Leaf u bt bu = trivial
thm_smash_elems n t Leaf bt bu = trivial 
thm_smash_elems n (Node m1 t1 Leaf) (Node m2 u1 (Node _ _ _)) bt bu = trivial
thm_smash_elems n (Node m1 t1 (Node _ _ _)) (Node m2 u1 Leaf) bt bu = trivial  -- [thm_smash_elems2 t u , appendBag (bt)( bu)] *** QED
thm_smash_elems n  (Node m1 t1 Leaf) (Node m2 u1 Leaf) bt bu = [thm_smash_elems2  (Node m1 t1 Leaf) (Node m2 u1 Leaf) , appendBag (bt)( bu)] *** QED


{-@ reflect priqueue_elements @-}
{-@ priqueue_elements :: Priqueue -> [Nat]@-}
priqueue_elements :: Priqueue -> [Key]
priqueue_elements []     = []
priqueue_elements (t:ts) =  (elements t)++ (priqueue_elements ts)

{-@ reflect priqueue_elems @-}
{-@ priqueue_elems :: Priqueue -> [Nat] -> Bool @-}
priqueue_elems :: Priqueue -> [Key] -> Bool
priqueue_elems p    l  = permutation (priqueue_elements p) l

{-@ reflect abs @-}
{-@abs :: Priqueue -> [Nat] -> Bool@-}
abs :: Priqueue -> [Key] -> Bool
abs p al = priqueue_elems p al


{-@ thm_empty_relate :: {abs p_empty []}@-}
thm_empty_relate :: Proof
thm_empty_relate = trivial


{-@ thm_priqueue_elems_ext :: q: Priqueue -> e1:{ [Key] | priqueue_elems q e1} -> e2:{[Key] | permutation e1 e2 } 
      -> { priqueue_elems q e2 }
@-}
thm_priqueue_elems_ext :: Priqueue -> [Key] -> [Key] -> Proof
thm_priqueue_elems_ext q e1 e2 = [thmPermProp (priqueue_elements q) e1 e2] *** QED


{-@ lemma_tree_can_relate :: t:Tree -> {tree_elems t (elements t)} @-}
lemma_tree_can_relate :: Tree -> Proof
lemma_tree_can_relate t = trivial


{-@ thm_can_relate :: p:{Priqueue | priq p} -> {abs p (priqueue_elements p)} @-}
thm_can_relate :: Priqueue -> Proof
thm_can_relate t = trivial


{-@ thm_abs_perm :: p:{Priqueue | priq p} -> al: { [Key] | abs p al} -> bl:{ [Key] | abs p bl} -> {permutation al bl } @-}
thm_abs_perm :: Priqueue -> [Key] -> [Key] -> Proof
thm_abs_perm p al bl = [thmPermProp (priqueue_elements p) al bl] *** QED


{-@ thm_abs_perm3 :: p:Priqueue -> al: { [Key] | abs p al} -> bl:{ [Key] | abs p bl} -> {abs p al = abs p bl } @-}
thm_abs_perm3 :: Priqueue -> [Key] -> [Key] -> Proof
thm_abs_perm3 p al bl = trivial


{-@ thm_smash_elems3 ::  t: Tree -> u:{Tree | smash t u /= Leaf}
      -> {tree_elems (smash t u) ((elements t)++(elements u)) } 
@-}
thm_smash_elems3 :: Tree -> Tree -> Proof
thm_smash_elems3 t u = [thm_smash_elems2 t u , appendBag (elements t) (elements u)] *** QED


{-@ thm_tree :: p:Priqueue -> pl : [Key] -> t:{Tree | abs (t:p) pl} -> { permutation (pl) (elements t ++ priqueue_elements p) } @-}
thm_tree :: Priqueue ->[Key] ->  Tree -> Proof
thm_tree p pl t = trivial


{-@ thm_tree2 ::  tl : [Int] -> t:{Tree | tree_elems t tl} -> u:{Tree | smash t u /= Leaf} -> { tree_elems (smash t u) (tl ++ elements u) } @-}
thm_tree2 ::  [Key] ->  Tree ->  Tree -> Proof
thm_tree2 tl t u = [thm_smash_elems2 t u , appendBag tl (elements u)]*** QED


{-@ ignore todo @-}
{-@ todo :: String -> {v:a | false } @-} 
todo :: String -> a 
todo  = error 

