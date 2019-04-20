{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}
{-@ LIQUID "--diff"       @-}
{-@ infixr ++             @-}

module Positive where

import           Prelude hiding ((++))
import           ProofCombinators
-- import           Lists
-- import           Perm

-- | Positive Integers in Binary -----------------------------------------------

data Pos = X Bool Pos | XH deriving (Show)

{-@ reflect boolNat @-}
boolNat :: Bool -> Int 
boolNat False = 0
boolNat True  = 1

{-@ reflect posNat @-}
posNat :: Pos -> Int 
posNat XH      = 1
posNat (X b p) = boolNat b + 2 * posNat p 

-- | An example, 10 -----------------------------------------------------------

{-@ reflect fourteen @-}
fourteen :: () -> Pos 
fourteen _ = X False (X True (X True XH))

{-@ ex14 :: _ -> TT @-}
ex14 :: () -> Bool 
ex14 _ = posNat (fourteen ()) == 14 

-- | Successor ---------------------------------------------------------------

{-@ reflect suc @-}
suc :: Pos -> Pos
suc XH          = X False XH 
suc (X False p) = X True  p 
suc (X True  p) = X False (suc p) 

{-@ exSuc14 :: _ -> TT @-}
exSuc14 :: () -> Bool
exSuc14 _ = posNat (suc (fourteen ())) == 15

{-@ lem_suc :: p:_ -> { posNat (suc p) == 1 + posNat p } @-}
lem_suc :: Pos -> Proof
lem_suc XH      = ()
lem_suc (X b p) = lem_suc p

-- | Addition -----------------------------------------------------------------

xor :: Bool -> Bool -> Bool
xor b1 b2 = ((b1 && not b2)) || (b2 && not b1)

imp :: Bool -> Bool -> Bool
imp b1 b2 = (not b1) || b2 

{-@ reflect carry @-}
carry :: Bool -> Bool -> Bool -> Bool 
carry False d1 d2 = d1 && d2 
carry True  d1 d2 = d1 || d2  

{-@ reflect digit @-}
digit :: Bool -> Bool -> Bool -> Bool 
digit False d1 d2 = d1 /= d2
digit True  d1 d2 = d1 == d2 

{-@ reflect addc1 @-}
addc1 True p  = suc p 
addc1 False p = p

{-@ reflect addc @-}
addc :: Bool -> Pos -> Pos -> Pos 
addc c XH        p         = addc1 c (suc p)
addc c p         XH        = addc1 c (suc p) 
addc c (X d1 p1) (X d2 p2) = X d' p' 
  where 
    c'                     = carry c d1 d2 
    d'                     = digit c d1 d2
    p'                     = addc c' p1 p2 


{-@ reflect add @-}
add :: Pos -> Pos -> Pos 
add p1 p2 = addc False p1 p2

-- | Correctness of addition --------------------------------------------------

{-@ lem_addc1 :: b:_ -> p:_ -> { posNat (addc1 b p) = boolNat b + posNat p } @-}
lem_addc1 :: Bool -> Pos -> Proof 
lem_addc1 True  p = lem_suc p
lem_addc1 False p = ()

{-@ lem_addc :: c:_ -> p1:_ -> p2:_ -> 
      { posNat (addc c p1 p2) = boolNat c + posNat p1 + posNat p2 } 
  @-}
lem_addc :: Bool -> Pos -> Pos -> Proof 
lem_addc c XH p                = lem_suc p &&& lem_addc1 c (suc p)
lem_addc c p  XH               = lem_suc p &&& lem_addc1 c (suc p)
lem_addc c (X b1 p1) (X b2 p2) = lem_addc (carry c b1 b2) p1 p2  

{-@ thm_add :: p1:_ -> p2:_ -> { posNat (add p1 p2) == posNat p1 + posNat p2 } @-}
thm_add :: Pos -> Pos -> Proof
thm_add p1 p2 = lem_addc False p1 p2

