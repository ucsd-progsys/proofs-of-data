{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}
{-@ infixr ++             @-}

module Tmp where

import ProofCombinators

data Pair a b = P a b 

{-@ measure pFst @-}
pFst :: Pair a b -> a 
pFst (P x _) = x 

{-@ measure pSnd @-}
pSnd :: Pair a b -> b 
pSnd (P _ y) = y 

{-@ reflect select @-}
{-@ select :: _ -> l:_ -> Pair a {v:_|len v = len l} @-}
select :: (Ord a) => a -> [a] -> Pair a [a]
select x []    = P x []
select x (h:t) 
  | x <= h     = -- THIS DEF IS SAFE
                 -- let s_x_t = select x t in P (pFst s_x_t) (h : pSnd s_x_t)

                 -- THIS DEF IS NOT SAFE! 
                 let P j l' = select x t in P j (h:l')  
  | otherwise  = let P j l' = select h t in P j (x:l') 

{- lem_select_1 :: x:_ -> l:_ -> { pFst (select x l) <= x } @-}
lem_select_1 :: (Ord a) => a -> [a] -> Proof 
lem_select_1 _ []    = () 
lem_select_1 x (h:t) 
  | x <= h           = let s_x_t  = select x t
                           s_x_ht = P (pFst s_x_t) (h : pSnd s_x_t)  
                       in 
                         select x (h:t) === s_x_ht *** QED
 
  | otherwise        = undefined 

