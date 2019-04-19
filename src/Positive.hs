{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}
{- LIQUID "--diff"       @-}
{-@ infixr ++             @-}

module Positive where

import           Prelude hiding ((++))
import           ProofCombinators
-- import           Lists
-- import           Perm

-- | Positive Integers in Binary -----------------------------------------------

data Pos = X1 Pos | X0 Pos | XH deriving (Show)

{-@ reflect pos2Nat @-}
pos2Nat :: Pos -> Int 
pos2Nat XH     = 1
pos2Nat (X1 p) = 1 + 2 * pos2Nat p 
pos2Nat (X0 p) = 0 + 2 * pos2Nat p 

-- | An example, 10 -----------------------------------------------------------

{-@ reflect fourteen @-}
fourteen :: () -> Pos 
fourteen _ = X0 (X1 (X1 XH))

{-@ ex14 :: _ -> TT @-}
ex14 :: () -> Bool 
ex14 _ = pos2Nat (fourteen ()) == 14 

-- | Successor ---------------------------------------------------------------

suc :: Pos -> Pos
suc XH     = X0 XH 
suc (X0 p) = X1 p 
suc (X1 p) = X0 (suc p) 


-- >>> suc XH
-- <interactive>:2675:2-4: error:
--     • Variable not in scope: suc :: t0 -> t
--     • Perhaps you meant one of these:
--         ‘sum’ (imported from Prelude), ‘succ’ (imported from Prelude)
-- <BLANKLINE>
-- <interactive>:2675:6-7: error: Data constructor not in scope: XH
--
{-@ exSuc14 :: _ -> TT @-}
exSuc14 :: () -> Bool
exSuc14 _ = pos2Nat (suc (fourteen ())) == 15
-- exSuc14 _ = pos2Nat (suc (fourteen ())) == 15
