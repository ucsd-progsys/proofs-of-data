{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}
{-@ infixr ++             @-}

module Tmp where
import Prelude hiding (fst, snd)
import ProofCombinators

{-@ reflect fst @-}
fst :: (a, b) -> a 
fst (x, y) = x 

{-@ reflect snd @-}
snd :: (a, b) -> b 
snd (x, y) = y 

{-@ reflect select @-}
{-@ select :: _ -> l:_ -> (a, {v:_|len v = len l}) @-}
select :: (Ord a) => a -> [a] -> (a, [a])
select x []    = (x, [])
select x (h:t) 
  | x <= h     = -- THIS DEF IS SAFE
                 -- let s_x_t = select x t in (fst s_x_t, h : snd s_x_t)

                 -- THIS DEF IS NOT SAFE! 
                 let (j, l') = select x t  in (j, h:l')  
  | otherwise  = let (j, l') = select h t  in (j, x:l') 

lem_select_1 :: (Ord a) => a -> [a] -> Proof 
lem_select_1 _ []    = () 
lem_select_1 x (h:t) 
  | x <= h           = let s_x_t  = select x t
                           s_x_ht = (fst s_x_t, h : snd s_x_t)  
                       in 
                         select x (h:t) 
                         === s_x_ht 
                         *** QED
  | otherwise        = undefined 

