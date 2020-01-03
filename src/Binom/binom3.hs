{-@ LIQUID "--reflection"                          @-}
{-@ LIQUID "--ple"                                 @-}
{-@ LIQUID "--exactdc"                             @-}
{-@ LIQUID "--exact-data-con"                      @-}
{-@ LIQUID "--higherorder"                         @-}
{-@ LIQUID "--noadt"                               @-}

{-@ infix : @-}
{-@ infix ++ @-}

module Binom3 where
import Prelude hiding(abs, (++), succ, lookup, pred, compare, unzip, Maybe(..))
import Language.Haskell.Liquid.ProofCombinators 	
import Lists
import Language.Haskell.Liquid.Bag	
import Permutations
import Binom2
import Binom


{-@ thm_carry_elems :: q: Priqueue -> n: {Key |priq' q n} -> t:{Tree | (t=Leaf || pow2heap n t)} -> eq:{ [Key] | priqueue_elems q eq} 
                                   -> et:{[Key] | tree_elems t et } -> { priqueue_elems (carry q t) (et++eq) }
@-}
thm_carry_elems :: Priqueue -> Key -> Tree -> [Key] -> [Key] -> Proof
thm_carry_elems [] n Leaf  eq et = [thm1 [] et , thm1 [] eq] *** QED
thm_carry_elems [] n t  eq et    = [thm1 [] eq , thmAppNilR (elements t), thmAppNilR et] *** QED
thm_carry_elems (Leaf:q') n t  eq et    = [appendBag (elements t) (priqueue_elements q') ,appendBag et eq] *** QED
thm_carry_elems (u:q') n Leaf  eq et  = [thm1 [] et] *** QED
thm_carry_elems (u:q') n t eq et =   priqueue_elems (carry (u:q') t) (et++eq)
                                 === priqueue_elems (Leaf:carry q' (smash t u)) (et++eq)
                                 === permutation (priqueue_elements (Leaf:carry q' (smash t u))) (et++eq)
                                 === permutation ( (elements Leaf) ++ priqueue_elements ( carry q' (smash t u) )  ) (et++eq)
                                 === permutation ( [] ++ priqueue_elements ( carry q' (smash t u) )  ) (et++eq)
                                 === permutation (  priqueue_elements ( carry q' (smash t u) )  ) (et++eq)  ? thmPermProp12 et eq (priqueue_elements (u:q')) (priqueue_elements ( carry q' (smash t u)) )
                                 === permutation (  priqueue_elements ( carry q' (smash t u) )  ) (et++(priqueue_elements (u:q'))) 
                                 === permutation (  priqueue_elements ( carry q' (smash t u) )  ) (et++(elements u ++ (priqueue_elements q'))) ? appendAssoc et (elements u) (priqueue_elements q')
                                 === permutation (  priqueue_elements ( carry q' (smash t u) )  ) ((et++elements u )++ (priqueue_elements q'))  
                                 === priqueue_elems ( carry q' (smash t u) ) ((et++elements u )++ (priqueue_elements q'))
                                 	?(thm_smash_valid n t u)  &&& (thm_tree2 et t u)  &&& thm_carry_elems q' (n+1) (smash t u) (priqueue_elements q') ( et ++ elements u)
                                 === True 
                                 *** QED


{-@ thm_insert_relate :: {p: Priqueue | priq p} -> k:Key -> al:{[Key] | abs p al} -> {abs (insert k p) (k:al)} @-}
thm_insert_relate:: Priqueue -> Key -> [Key] -> Proof
thm_insert_relate p k al = abs (insert k p) (k:al) 
                         === abs (carry p (Node k Leaf Leaf)) (k:al)
                         === abs (carry p (Node k Leaf Leaf)) ([k]++al)
                         === priqueue_elems (carry p (Node k Leaf Leaf))  ([k]++al)
                         	? thm_carry_elems p 0 (Node k Leaf Leaf) al [k]
                         === True 
                         *** QED


{-@ thm_perm1 :: xs: {[a] | len xs >0} ->  { permutation xs [] == False }  @-}
thm_perm1 :: (Eq a, Ord a) => [a] -> Proof 
thm_perm1 [] 
  = ()  
thm_perm1 (x:xs) 
  =   (permutation xs [] 
  , bag xs == bag []
  ,put x (bag xs) == empty 
       , thm_emp x (bag xs) )
  *** QED 

{-@ thm1:: l:{[a] | l = []} -> l2:{[a] | permutation l l2} -> { l2 = []}  @-}
thm1:: (Eq a, Ord a) => [a] -> [a] -> Proof
thm1 [] [] =trivial
thm1 [] l = thm_perm1 l *** QED


{-@ thm_join_elems_aux :: p:{Priqueue | len p = 1}-> q:Priqueue -> pl:{[Key] | priqueue_elems p pl} -> ql:{[Key] | priqueue_elems q ql}
      -> {priqueue_elems (p++q) (pl++ql)}
@-}
thm_join_elems_aux :: Priqueue -> Priqueue -> [Int] -> [Int] -> Proof
thm_join_elems_aux [c] q pl ql = priqueue_elems ([c]++q) (pl++ql)
                               === permutation (priqueue_elements ([c]++q)) (pl++ql)
                               === permutation (priqueue_elements (c:q)) (pl++ql)
                               === permutation ( (elements c) ++ priqueue_elements (q)) (pl++ql) ? thmAppNilR (elements c)
                               === permutation ( ((elements c) ++ []) ++ priqueue_elements (q)) (pl++ql) 
                               === permutation ( (priqueue_elements [c]) ++ priqueue_elements (q)) (pl++ql)
                               	 ?thm_join_elems_aux_p (priqueue_elements [c]) (priqueue_elements q) pl ql
                               === True 
                               *** QED


{-@ thm_join_elems_aux_p :: p:[a]-> q:[a] -> pl:{[a] | permutation p pl} -> ql:{[a] | permutation q ql}
      -> {permutation (p++q) (pl++ql)}
@-}
thm_join_elems_aux_p :: (Ord a) => [a] -> [a] -> [a] -> [a] -> Proof
thm_join_elems_aux_p p q pl ql = [appendBag p q, appendBag pl ql] *** QED


{-@ thm_join_elems_aux2 :: c:Tree -> cl:{[Key] | tree_elems c cl} -> {priqueue_elems [c] (cl)}
@-}
thm_join_elems_aux2 :: Tree -> [Key] -> Proof
thm_join_elems_aux2 c cl = priqueue_elems [c] cl
						 === permutation (priqueue_elements [c]) cl
						 === permutation (elements c ++ priqueue_elements []) cl
						 === permutation (elements c ++ []) cl ? thmAppNilR (elements c)
						 === permutation (elements c) cl
						 === tree_elems c cl
						 === True
						 *** QED


{-@ thmPermProp12 :: ws: [a] -> xs:[a] -> ys:{[a] | permutation xs ys} -> zs:[a] -> {permutation zs (ws++xs) <=> permutation zs (ws++ys)} @-}
thmPermProp12:: (Ord a) => [a] -> [a] -> [a] -> [a] -> Proof
thmPermProp12 ws xs ys zs = [appendBag ws xs , appendBag ws ys] *** QED

{-@ thmPermProp13 :: ws: [a] -> xs:[a] -> ys:{[a] | permutation xs ys} -> zs:[a] -> {permutation zs (ws++xs) <=> permutation zs (ys++ws)} @-}
thmPermProp13:: (Ord a) => [a] -> [a] -> [a] -> [a] -> Proof
thmPermProp13 ws xs ys zs = [appendBag ws xs , appendBag ys ws] *** QED

{-@ thmPermProp14 :: xs: [a] -> ys:[a] -> zs:[a] -> {permutation xs (ys++zs) <=> permutation xs (zs++ys)} @-}
thmPermProp14:: (Ord a) => [a] -> [a] -> [a] -> Proof
thmPermProp14 xs ys zs = [appendBag ys zs, appendBag zs ys] *** QED

{-@ thmPermProp15 :: xs: [a] -> ys:[a] -> {permutation  (xs++ys) (ys++xs)} @-}
thmPermProp15:: (Ord a) => [a] -> [a] -> Proof
thmPermProp15 xs ys = [appendBag xs ys, appendBag ys xs] *** QED

{-@ thmPermProp16 :: ws: [a] -> xs:[a] -> ys:{[a] | permutation xs ys} -> zs:[a] -> {permutation zs (xs++ws) <=> permutation zs (ys++ws)} @-}
thmPermProp16:: (Ord a) => [a] -> [a] -> [a] -> [a] -> Proof
thmPermProp16 ws xs ys zs = [appendBag xs ws , appendBag ys ws] *** QED

{-@ thmPermProp17 :: xs: [a] -> ys:{[a] | permutation xs ys} -> zs:[a] -> {permutation  (xs++zs) (ys++zs)} @-}
thmPermProp17:: (Ord a) => [a] -> [a] -> [a] -> Proof
thmPermProp17 xs ys zs = [appendBag ys zs, appendBag xs zs] *** QED

{-@ thmPermProp18 :: xs: [a] -> ys: [a] -> zs : {[a] | permutation xs zs} -> ws : {[a] | permutation ys ws} ->  {permutation (xs++ys) (zs++ws)}  @-}
thmPermProp18:: (Ord a) => [a] -> [a] -> [a] -> [a] -> Proof
thmPermProp18 xs ys zs ws = [appendBag xs ys, appendBag zs ws] *** QED


{-@ thmPermProp19 :: xs: [a] -> ys: [a] -> zs : [a] -> ws : [a] ->  {permutation ((xs++ys) ++ (zs++ws)) ((xs++zs) ++ (ys++ws))  }  @-}
thmPermProp19:: (Ord a) => [a] -> [a] -> [a] -> [a] -> Proof
thmPermProp19 xs ys zs ws = [appendBag xs ys, appendBag zs ws, appendBag (xs++ys) (zs++ws), appendBag ys ws, appendBag xs zs, appendBag (xs++zs) (ys++ws) ] *** QED

{-@ thm_priq_pow2heap:: n:Nat -> p:{Priqueue | len p > 0 && priq' p n && lHd p /= Leaf} -> { pow2heap n (lHd p)} @-}
thm_priq_pow2heap :: Int -> Priqueue -> Proof
thm_priq_pow2heap n (p1:p) = trivial

{-@ appendAssoc2 :: xs:_ -> ys:_ -> zs:_ -> { xs ++ ys ++ zs = xs ++ (ys ++ zs) } @-}
appendAssoc2 :: [a] -> [a] -> [a] -> Proof                
appendAssoc2 [] _ _       = trivial
appendAssoc2 (_:xs) ys zs = appendAssoc xs ys zs
