{-@ LIQUID "--reflection"                          @-}
{-@ LIQUID "--ple"                                 @-}
{-@ LIQUID "--exactdc"                             @-}
{-@ LIQUID "--exact-data-con"                      @-}
{-@ LIQUID "--higherorder"                         @-}
{-@ LIQUID "--noadt"                               @-}

{-@ infix : @-}
{-@ infix ++ @-}

module Binom4 where
import Prelude hiding(abs, (++), succ, lookup, length,  pred, compare, unzip, Maybe(..))
import Language.Haskell.Liquid.ProofCombinators    
import Lists
import Language.Haskell.Liquid.Bag  
import Permutations
import Binom3
import Binom2
import Binom


{-@thm_join_elems :: n:Key -> p:{Priqueue | priq' p n} -> q:{Priqueue | priq' q n} -> c:{Tree | (c=Leaf || pow2heap n c)}
                           -> pe:{[Nat] | priqueue_elems p pe} -> qe:{[Nat] | priqueue_elems q qe} -> ce:{[Nat] | tree_elems c ce}
                           -> { priqueue_elems (join p q c) (ce++pe++qe) } / [len p]
@-}
thm_join_elems :: Key -> Priqueue -> Priqueue -> Tree -> [Key] -> [Key] -> [Key] -> Proof
thm_join_elems n [] q c pe qe ce =   priqueue_elems (join [] q c) (ce++pe++qe) ? appendAssoc2 ce pe qe
                                 === priqueue_elems (join [] q c) (ce++(pe++qe)) 
                                 === priqueue_elems (carry q c) (ce++(pe++qe)) ? thm1 [] pe
                                 === priqueue_elems (carry q c) (ce++([]++qe)) 
                                 === priqueue_elems (carry q c) (ce++qe) ? thm_carry_elems q n c qe ce -- ? thmAppNilR ce
                                 === True 
                                 *** QED

thm_join_elems n p [] c pe qe ce =   priqueue_elems (join p [] c) (ce++pe++qe) ? appendAssoc2 ce pe qe
                                 === priqueue_elems (join p [] c) (ce++(pe++qe))
                                 === priqueue_elems (carry p c) (ce++(pe++qe)) ? thm1 [] qe
                                 === priqueue_elems (carry p c) (ce++(pe++[])) ? thmAppNilR (pe)
                                 === priqueue_elems (carry p c) (ce++pe)  ? thm_carry_elems p n c pe ce
                                 === True 
                                 *** QED

thm_join_elems n (Leaf:p) (Leaf:q) c pe qe ce 
                                 =   priqueue_elems (join  (Leaf:p) (Leaf:q) c) (ce++pe++qe) ? appendAssoc2 ce pe qe
                                 === priqueue_elems (join  (Leaf:p) (Leaf:q) c) (ce++(pe++qe)) 
                                 === priqueue_elems (c: join p q Leaf) (ce++(pe++qe))
                                 === priqueue_elems ([c] ++ join p q Leaf) (ce++(pe++qe))
                                 ? ( thm_join_elems (n+1) p q Leaf pe qe [] ) &&& (thmAppNilR (pe++qe)) 
                                 &&& (thm_join_elems_aux2 c ce) &&& thm_join_elems_aux [c] (join p q Leaf) ce (pe++qe)
                                 === True 
                                 *** QED

thm_join_elems n (Leaf:p) (q1:q) Leaf pe qe ce 
                                 =   priqueue_elems (join  (Leaf:p) (q1:q) Leaf) (ce++pe++qe)  ? appendAssoc2 ce pe qe 
                                 === priqueue_elems (join  (Leaf:p) (q1:q) Leaf) (ce++(pe++qe)) ? thm1 [] ce
                                 === priqueue_elems (join  (Leaf:p) (q1:q) Leaf) ([]++(pe++qe)) 
                                 === priqueue_elems ( q1   : join p q Leaf) (pe++qe)
                                 === priqueue_elems ([q1] ++ join p q Leaf) (pe++qe) ? thmPermProp12 pe qe (priqueue_elements (q1:q)) (priqueue_elements ([q1] ++ join p q Leaf))
                                 === priqueue_elems ([q1] ++ join p q Leaf) (pe++(priqueue_elements (q1:q))) 
                                 === priqueue_elems ([q1] ++ join p q Leaf) (pe++ ((elements q1) ++  (priqueue_elements q))) ? thmPermProp13 pe qe (priqueue_elements (q1:q)) (priqueue_elements ([q1] ++ join p q Leaf))
                                 === priqueue_elems ([q1] ++ join p q Leaf) (( (elements q1) ++ (priqueue_elements q) ) ++ pe)  ? appendAssoc (elements q1) (priqueue_elements q) pe
                                 === priqueue_elems ([q1] ++ join p q Leaf) ((elements q1) ++  ((priqueue_elements q)  ++ pe))  
                                   ? ( thm_join_elems (n+1) p q Leaf pe (priqueue_elements q) [] )  
                                            &&& (thmPermProp14 (priqueue_elements (join p q Leaf)) (pe) (priqueue_elements q)) 
                                            &&& (thm_join_elems_aux2 q1 (elements q1) ) &&& thm_join_elems_aux [q1] (join p q Leaf) (elements q1) ((priqueue_elements q)++pe)
                                 === True
                                 *** QED

thm_join_elems n (Leaf:p) (q1:q)  (Node k l r) pe qe ce  
                                 =   priqueue_elems (join  (Leaf:p) (q1:q)  (Node k l r)) (ce++pe++qe) 
                                 === priqueue_elems (Leaf : join p q (smash (Node k l r) q1)) (ce++pe++qe) 
                                 === permutation (priqueue_elements (Leaf : join p q (smash (Node k l r) q1))) (ce++pe++qe) 
                                 === permutation ( (elements Leaf) ++ priqueue_elements (join p q (smash (Node k l r) q1))) (ce++pe++qe)
                                 === permutation ( [] ++ priqueue_elements (join p q (smash (Node k l r) q1))) (ce++pe++qe)
                                 === permutation (priqueue_elements (join p q (smash (Node k l r) q1))) (ce++pe++qe)
                                 === priqueue_elems (join p q (smash (Node k l r) q1)) (ce++pe++qe) ?  appendAssoc2 ce pe qe
                                 === priqueue_elems (join p q (smash (Node k l r) q1)) (ce++(pe++qe)) ?  (thmPermProp15 pe qe) &&& thmPermProp12 ce (pe++qe) (qe++pe) (priqueue_elements (join p q (smash (Node k l r) q1)))
                                 === priqueue_elems (join p q (smash (Node k l r) q1)) (ce++(qe++pe)) ? (thmPermProp17 qe (priqueue_elements (q1:q)) pe) &&& thmPermProp12 ce (qe++pe) ((priqueue_elements (q1:q))++pe) (priqueue_elements (join p q (smash (Node k l r) q1)))
                                 === priqueue_elems (join p q (smash (Node k l r) q1)) (ce++((priqueue_elements (q1:q))++pe)) ? appendAssoc ce (priqueue_elements (q1:q)) pe
                                 === priqueue_elems (join p q (smash (Node k l r) q1)) ((ce++(priqueue_elements (q1:q)))++pe) 
                                 === priqueue_elems (join p q (smash (Node k l r) q1)) ((ce++((elements q1) ++ (priqueue_elements q)))++pe) ? appendAssoc ce (elements q1) (priqueue_elements q)
                                 === priqueue_elems (join p q (smash (Node k l r) q1)) (((ce++(elements q1)) ++ (priqueue_elements q))++pe) ? appendAssoc (ce++(elements q1)) (priqueue_elements q) pe
                                 === priqueue_elems (join p q (smash (Node k l r) q1)) ((ce++(elements q1)) ++ ((priqueue_elements q)++pe)) ? (thmPermProp15 (priqueue_elements q) pe) &&& thmPermProp12 (ce++(elements q1))  ((priqueue_elements q)++pe) (pe++(priqueue_elements q)) (priqueue_elements (join p q (smash (Node k l r) q1)))
                                 === priqueue_elems (join p q (smash (Node k l r) q1)) ((ce++(elements q1)) ++ (pe++(priqueue_elements q))) ? appendAssoc (ce++(elements q1)) pe (priqueue_elements q)
                                 === priqueue_elems (join p q (smash (Node k l r) q1)) ((ce++(elements q1)) ++ pe++(priqueue_elements q))   
                                    ?  (thm_smash_elems n (Node k l r) q1 ce (elements q1)) &&& (thm_join_elems (n+1) p q (smash (Node k l r) q1) pe (priqueue_elements q) (ce++(elements q1)) )
                                 === True
                                 *** QED

thm_join_elems n  (p1:p)   (Leaf:q) (Leaf)  pe qe ce 
                                 =   priqueue_elems (join  (p1:p) (Leaf:q) Leaf) (ce++pe++qe) ? appendAssoc2 ce pe qe 
                                 === priqueue_elems (join  (p1:p) (Leaf:q) Leaf) (ce++(pe++qe)) ? thm1 [] ce
                                 === priqueue_elems (join  (p1:p) (Leaf:q) Leaf) ([]++pe++qe) 
                                 === priqueue_elems (p1   : join p q Leaf) ([]++pe++qe)
                                 === priqueue_elems ([p1]++ join p q Leaf) (pe++qe) ?  thmPermProp16 qe pe (priqueue_elements (p1:p))  (priqueue_elements ([p1]++ join p q Leaf))
                                 === priqueue_elems ([p1]++ join p q Leaf) (priqueue_elements (p1:p) ++ qe) 
                                 === priqueue_elems ([p1]++ join p q Leaf) (((elements p1) ++ (priqueue_elements p)) ++ qe) ? appendAssoc (elements p1) (priqueue_elements p) qe
                                 === priqueue_elems ([p1]++ join p q Leaf) ((elements p1) ++ ((priqueue_elements p) ++ qe)) 
                                           ? (thm_join_elems (n+1) p q Leaf (priqueue_elements p) qe []) &&& (thm_join_elems_aux2 p1 (elements p1))
                                                   &&& thm_join_elems_aux [p1] (join p q Leaf) (elements p1) ((priqueue_elements p)++qe)
                                 === True
                                 *** QED           

thm_join_elems n (p1:p) (Leaf:q) (Node k l r) pe qe ce  
                                 =   priqueue_elems (join  (p1:p) (Leaf:q) (Node k l r)) (ce++pe++qe) 
                                 ===   priqueue_elems (join  (p1:p) (Leaf:q) (Node k l r)) (ce++pe++qe) 
                                 === priqueue_elems (Leaf : join p q (smash (Node k l r) p1)) (ce++pe++qe) 
                                 === permutation (priqueue_elements (Leaf : join p q (smash (Node k l r) p1))) (ce++pe++qe) 
                                 === permutation ( (elements Leaf) ++ priqueue_elements (join p q (smash (Node k l r) p1))) (ce++pe++qe)
                                 === permutation ( [] ++ priqueue_elements (join p q (smash (Node k l r) p1))) (ce++pe++qe)
                                 === permutation (priqueue_elements (join p q (smash (Node k l r) p1))) (ce++pe++qe)
                                 === priqueue_elems (join p q (smash (Node k l r) p1)) (ce++pe++qe) ? appendAssoc2 ce pe qe
                                 === priqueue_elems (join p q (smash (Node k l r) p1)) (ce++(pe++qe)) 
                                    ? (thmPermProp17 pe (priqueue_elements (p1:p)) qe)  &&& thmPermProp12 ce (pe++qe) ((priqueue_elements (p1:p))++qe) (priqueue_elements  (join p q (smash (Node k l r) p1)) )
                                 === priqueue_elems (join p q (smash (Node k l r) p1)) (ce++((priqueue_elements (p1:p))++qe))    ? appendAssoc ce (priqueue_elements (p1:p)) qe               
                                 === priqueue_elems (join p q (smash (Node k l r) p1)) ((ce++(priqueue_elements (p1:p)))++qe)    
                                 === priqueue_elems (join p q (smash (Node k l r) p1)) ((ce++((elements p1) ++ (priqueue_elements p)))++qe) ? appendAssoc ce (elements p1) (priqueue_elements p)
                                 === priqueue_elems (join p q (smash (Node k l r) p1)) (((ce++(elements p1)) ++ (priqueue_elements p))++qe) ? appendAssoc (ce++(elements p1)) (priqueue_elements p) qe
                                 === priqueue_elems (join p q (smash (Node k l r) p1)) ((ce++(elements p1)) ++ ((priqueue_elements p)++qe)) 
                                    ? (thm_smash_elems n (Node k l r) p1 ce (elements p1)) &&& (thm_join_elems (n+1) p q (smash (Node k l r) p1) (priqueue_elements p) qe (ce++(elements p1)) )
                                 === True   
                                 *** QED

thm_join_elems n (p1:p) (q1:q) c pe qe ce 
                                 =   priqueue_elems (join  (p1:p) (q1:q) c) (ce++pe++qe) 
                                 === priqueue_elems (c : join p q (smash p1 q1)) (ce++pe++qe) ? appendAssoc2 ce pe qe
                                 === priqueue_elems (c : join p q (smash p1 q1)) (ce++(pe++qe))  
                                    ? thmPermProp18 pe qe (priqueue_elements (p1:p)) (priqueue_elements (q1:q)) &&&
                                       thmPermProp12 ce (pe++qe) ( priqueue_elements (p1:p)++(priqueue_elements (q1:q))) ( priqueue_elements (c : join p q (smash p1 q1)))
                                 === priqueue_elems (c : join p q (smash p1 q1)) (ce++( priqueue_elements (p1:p)++(priqueue_elements (q1:q))) )                          
                                 === priqueue_elems (c : join p q (smash p1 q1)) (ce++( ((elements p1) ++ (priqueue_elements p)) ++( ((elements q1) ++ (priqueue_elements q)))) )
                                    ? thmPermProp19 (elements p1) (priqueue_elements p) (elements q1) (priqueue_elements q) &&&
                                       thmPermProp12 ce ( ((elements p1) ++ (priqueue_elements p) ) ++( ((elements q1) ++ (priqueue_elements q) )))  (  ( (elements p1) ++ (elements q1))  ++ ( (priqueue_elements p) ++ (priqueue_elements q)) )  ( priqueue_elements (c : join p q (smash p1 q1))) 
                                 === priqueue_elems (c : join p q (smash p1 q1)) (ce++(  ( (elements p1) ++ (elements q1)) ++ ( (priqueue_elements p) ++ (priqueue_elements q)) ) )
                                    ? appendAssoc ((elements p1) ++ (elements q1)) (priqueue_elements p)  (priqueue_elements q) 
                                 === priqueue_elems (c : join p q (smash p1 q1)) (ce++(  ( ((elements p1) ++ (elements q1)) ++  (priqueue_elements p)) ++ (priqueue_elements q) ) )
                                    ? thm_smash_elems n p1 q1 (elements p1) (elements q1) &&&
                                       thm_join_elems (n+1) p q (smash p1 q1) (priqueue_elements p) (priqueue_elements q) ((elements p1) ++ (elements q1)) &&&  (thm_join_elems_aux2 c ce) &&&
                                       thm_join_elems_aux [c] (join p q (smash p1 q1)) ce ( ( (elements p1) ++ (elements q1)) ++ ( (priqueue_elements p) ++ (priqueue_elements q)) )
                                 === True
                                 *** QED 

