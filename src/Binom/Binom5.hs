{-@ LIQUID "--reflection"                          @-}
{-@ LIQUID "--ple"                                 @-}
{-@ LIQUID "--exactdc"                             @-}
{-@ LIQUID "--exact-data-con"                      @-}
{-@ LIQUID "--higherorder"                         @-}
{-@ LIQUID "--noadt"                               @-}

{-@ infix : @-}
{-@ infix ++ @-}

module Binom5 where
import Prelude hiding(abs, (++), succ, lookup,  pred, compare, unzip, Maybe(..))
import Language.Haskell.Liquid.ProofCombinators 	
import Lists
import Language.Haskell.Liquid.Bag	
import Permutations
import Binom4
import Binom3
import Binom2
import Binom


{-@ thm_merge_relate :: p:{Priqueue | priq p} -> q:{Priqueue | priq q} -> pl:{[Key] | abs p pl} -> ql:{[Key] | abs q ql} 
     -> al:{[Key] | abs (merge p q) al} -> { permutation al (pl++ql)}
@-}
thm_merge_relate :: Priqueue -> Priqueue -> [Key] -> [Key] -> [Key] -> Proof
thm_merge_relate p q pl ql al = thm_join_elems 0 p q Leaf pl ql []


{-@ thm_del1 :: t:{Tree | t/=  Leaf} -> {len (elements t)>0} @-}
thm_del1 :: Tree -> Proof
thm_del1 Leaf = trivial
thm_del1 (Node k l r) = len (elements (Node k l r)) > 0 
                      === (len (k: ((elements l) ++ (elements r)))) > 0 
                      === (1+ len ((elements l) ++ (elements r))) > 0
                      === True *** QED


{-@ thm_del2 :: p:{Priqueue | len p>0 && lHd p /=  Leaf} -> {len (priqueue_elements p)>0} @-}
thm_del2 :: Priqueue -> Proof
thm_del2 (Leaf:p) = trivial
thm_del2 (p1:p) = ( app_length (elements p1) (priqueue_elements p), thm_del1 p1 ) *** QED


{-@ thm_del3 :: pl:[Key] -> p:{Priqueue | len p>0 && lHd p ==  Leaf && abs p pl} -> {abs (lTl p) pl} @-}
thm_del3 :: [Key] -> Priqueue -> Proof
thm_del3 pl (Leaf:p) = abs (lTl (Leaf:p)) pl 
                     === abs (p) pl 
                     === permutation (priqueue_elements p) pl
                     === permutation ([] ++ priqueue_elements p) pl
                     === permutation (priqueue_elements ((Leaf:p))) pl
                     === abs (Leaf:p) pl
                     === True 
                     *** QED

 
{-@ thm_delete_max_None_relate :: p: Priqueue  -> { abs p [] ==> delete_max p = Nothing} @-}
thm_delete_max_None_relate :: Priqueue -> Proof
thm_delete_max_None_relate [] = trivial
thm_delete_max_None_relate (Leaf:p) = ( thm_delete_max_None_relate p, 
									   thm_delete_max_None_relate_aux2 p,
									   thm_delete_max_None_relate_aux p, find_max p == Nothing,
										find_max (Leaf:p) == Nothing, delete_max (Leaf:p) == Nothing ) *** QED
thm_delete_max_None_relate (p1:p) =  [ thm_del2 (p1:p), thm_perm2 (priqueue_elements (p1:p)) [] ] *** QED  


{-@ thm_find_max2 :: p: { Priqueue | abs (Leaf:p) []} -> { abs (p) []} @-}
thm_find_max2 :: Priqueue -> Proof
thm_find_max2 p = trivial


 {-@ assume thm_size2 :: xs:[k] ->  { bagSize (bag xs) == len xs }  @-}
thm_size2 :: (Ord k) => [k] -> ()  
thm_size2 _ = ()


{-@ thm_perm2 :: (Ord a, Eq a) => xs: [a] -> ys: {[a] |len xs /= len ys}  -> {permutation xs ys == False} @-}
thm_perm2 :: (Ord a, Eq a) => [a] -> [a] -> Proof
thm_perm2 xs ys
  = (  permutation xs ys 
  , bag xs == bag ys 
  , bagSize (bag xs) == bagSize (bag ys) 
       , thm_size2 xs , thm_size2 ys )
  *** QED 


{-@ thm_del5:: p:{Priqueue | len p>0 && lHd p /= Leaf} -> {find_max p /= Nothing}@-}
thm_del5 :: Priqueue -> Proof
thm_del5 (Leaf:p) = trivial
thm_del5 (p1:p)   = trivial


{-@ thm_del4:: p:{Priqueue | len p>0 && lHd p /= Leaf} -> {delete_max p /= Nothing} @-}
thm_del4 :: Priqueue -> Proof
thm_del4 (Leaf:p) = trivial
thm_del4 (p1:p)   = delete_max (p1:p) /= Nothing
                  ==. (if(find_max (p1:p) == Nothing) then Nothing else let (P p' q') = delete_max_aux (p1:p) (fromJust (find_max (p1:p))) in Just (P (fromJust (find_max (p1:p))) (join p' q' Leaf)) ) /= Nothing
                  ==. (let (P p' q') = delete_max_aux (p1:p) (fromJust (find_max (p1:p))) in Just (P (fromJust (find_max (p1:p))) (join p' q' Leaf)) ) /= Nothing   ? thm_del5 (p1:p)
                  ==. True
                  *** QED


{-@ thm_delete_max_None_relate_aux :: p: Priqueue ->   { find_max (Leaf:p) /= Nothing <=> find_max p /= Nothing }  @-}
thm_delete_max_None_relate_aux :: Priqueue -> Proof
thm_delete_max_None_relate_aux p = trivial
                             

{-@ thm_delete_max_None_relate4 :: p: Priqueue ->   { delete_max (Leaf:p) == Nothing ==> delete_max p == Nothing }  @-}
thm_delete_max_None_relate4 :: Priqueue -> Proof
thm_delete_max_None_relate4 [] = trivial
thm_delete_max_None_relate4 p | (find_max p == Nothing ) = trivial
thm_delete_max_None_relate4 p | (find_max p /= Nothing ) = 
     [thm_delete_max_None_relate_aux2 (Leaf:p), thm_delete_max_None_relate_aux p ] *** QED


{-@ thm_delete_max_None_relate_aux1 :: p: Priqueue ->   { find_max p == Nothing ==> delete_max p == Nothing }  @-}
thm_delete_max_None_relate_aux1 :: Priqueue -> Proof
thm_delete_max_None_relate_aux1 [] = trivial
thm_delete_max_None_relate_aux1 p | (find_max p == Nothing ) = trivial
thm_delete_max_None_relate_aux1 p | (find_max p /= Nothing ) = trivial


{-@ thm_delete_max_None_relate1 :: p: Priqueue ->   { delete_max p == Nothing ==> find_max p == Nothing }  @-}
thm_delete_max_None_relate1 :: Priqueue -> Proof
thm_delete_max_None_relate1 [] = trivial
thm_delete_max_None_relate1 p | find_max p == Nothing = trivial
thm_delete_max_None_relate1 q | find_max q /= Nothing = 
  (thm_delete_max_None_relate_aux3 (find_max q), isJust (find_max q), 
   thm_delete_max_None_relate_aux4 (P (fromJust (find_max q)) (join  (fst1 (delete_max_aux q (fromJust (find_max q))))  (snd1 (delete_max_aux q (fromJust (find_max q))))  Leaf))  ,
   thm_delete_max_None_relate_aux3 (Just (P (fromJust (find_max q)) (join  (fst1 (delete_max_aux q (fromJust (find_max q))))  (snd1 (delete_max_aux q (fromJust (find_max q))))  Leaf))))
  *** QED


{-@ thm_delete_max_None_relate_aux2 :: p: Priqueue ->   { find_max p == Nothing <=> delete_max p == Nothing }  @-}
thm_delete_max_None_relate_aux2 :: Priqueue -> Proof
thm_delete_max_None_relate_aux2 p = [thm_delete_max_None_relate_aux1 p, thm_delete_max_None_relate1 p] *** QED


{-@ thm_delete_max_None_relate_aux3 :: (Eq a) =>   y: Maybe a ->  {  y /= Nothing <=>isJust y   }  @-}
thm_delete_max_None_relate_aux3 ::  Maybe a -> Proof
thm_delete_max_None_relate_aux3 (Just y) = trivial
thm_delete_max_None_relate_aux3 Nothing  = trivial


{-@ thm_delete_max_None_relate_aux4 :: (Eq a) =>   x: a ->  { isJust (Just x) }  @-}
thm_delete_max_None_relate_aux4 ::  a -> Proof
thm_delete_max_None_relate_aux4 x = trivial  


{-@ thm_delete_max_None_relate2 :: p: Priqueue ->  { delete_max p = Nothing ==> abs p [] } @-}
thm_delete_max_None_relate2 :: Priqueue -> Proof
thm_delete_max_None_relate2 [] = trivial
thm_delete_max_None_relate2 (Leaf:p) =  abs (Leaf:p) []
                                     ==. permutation (priqueue_elements (Leaf:p))  []
                                     ==. permutation (elements Leaf ++ (priqueue_elements p)) []
                                     ==. permutation ([] ++ (priqueue_elements p)) []
                                     ==. permutation (priqueue_elements p) []
                                     ==.  True ? thm_delete_max_None_relate4 p  &&& thm_delete_max_None_relate2 p *** QED

thm_delete_max_None_relate2 (p1:p) = [thm_del4 (p1:p) ]   *** QED                                 


{-@ thm_delete_max_None_relate3 :: p:{Priqueue | priq p} -> { abs p [] <=> delete_max p = Nothing } @-}
thm_delete_max_None_relate3 :: Priqueue -> Proof
thm_delete_max_None_relate3 [] = trivial
thm_delete_max_None_relate3 p = [thm_delete_max_None_relate p, thm_delete_max_None_relate2 p] *** QED
