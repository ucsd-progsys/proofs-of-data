{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}
{-@ LIQUID "--diff"       @-}
{-@ infixr ++             @-}

module Positive where

import           Prelude hiding ((++))
import           ProofCombinators

{-# ANN module "HLint: ignore Use camelCase" #-}
{-# ANN module "HLint: ignore Use foldr"     #-}
{-# ANN module "HLint: ignore Use const"     #-}

-- | Positive Integers in Binary -----------------------------------------------

data Pos = X Bool Pos | XH deriving (Eq, Show)

{-@ reflect boolNat @-}
boolNat :: Bool -> Int 
boolNat False = 0
boolNat True  = 1

{-@ reflect posNat @-}
{-@ posNat :: Pos -> {v:Int | 0 < v} @-}
posNat :: Pos -> Int 
posNat XH      = 1
posNat (X b p) = boolNat b + 2 * posNat p 

-- | Some examples -----------------------------------------------------------

{-@ reflect p5 @-}
p5 :: () -> Pos 
p5 _ = X True (X False XH)

{-@ reflect p14 @-}
p14 :: () -> Pos 
p14 _ = X False (X True (X True XH))

{-@ p_examples :: _ -> TT @-}
p_examples :: () -> Bool 
p_examples _ = posNat (p14 ()) == 14
            && posNat (p5 ())  == 5

-- | Successor ---------------------------------------------------------------

{-@ reflect suc @-}
suc :: Pos -> Pos
suc XH          = X False XH 
suc (X False p) = X True  p 
suc (X True  p) = X False (suc p) 

{-@ exSuc14 :: _ -> TT @-}
exSuc14 :: () -> Bool
exSuc14 _ = posNat (suc (p14 ())) == 15

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

-- | Comparison ---------------------------------------------------------------

data Cmp = Lt | Gt | Eq

{-@ reflect cmpNat @-}
cmpNat :: Int -> Int -> Cmp
cmpNat x y 
  | x <  y    = Lt
  | x == y    = Eq
  | otherwise = Gt

{-@ reflect cmp @-}
cmp :: Pos -> Pos -> Cmp
cmp (X True  p) (X True  q) = cmp p q
cmp (X False p) (X False q) = cmp p q
cmp (X True  p) (X False q) = force Lt (cmp p q) 
cmp (X False p) (X True  q) = force Gt (cmp p q) 
cmp (X _     _) XH          = Gt
cmp XH          (X _     _) = Lt
cmp XH          XH          = Eq

{-@ reflect force @-}
force :: Cmp -> Cmp -> Cmp 
force Lt Lt = Lt 
force Lt _  = Gt 
force Gt Gt = Gt
force Gt _  = Lt
force Eq c  = c

-- | Correctness of Comparison ------------------------------------------------

{-@ lem_posNat_pos :: p:_ -> {posNat p > 0} @-}
lem_posNat_pos :: Pos -> Proof
lem_posNat_pos XH      = ()
lem_posNat_pos (X _ p) = lem_posNat_pos p

{-@ thm_cmp :: p:_ -> q:_ -> { cmp p q == cmpNat (posNat p) (posNat q) } @-}
thm_cmp :: Pos -> Pos -> Proof
thm_cmp (X True  p) (X True  q) = thm_cmp p q 
thm_cmp (X False p) (X False q) = thm_cmp p q
thm_cmp (X True  p) (X False q) = thm_cmp p q
thm_cmp (X False p) (X True  q) = thm_cmp p q
thm_cmp (X _     p) XH          = lem_posNat_pos p
thm_cmp XH          (X _     p) = lem_posNat_pos p
thm_cmp XH          XH          = () 

------------------------------------------------------------------------------
-- | Bijection between Pos and Integers
------------------------------------------------------------------------------

{-@ reflect natBool @-}
{-@ natBool :: {v:Nat | v <= 1} -> _ @-} 
natBool :: Int -> Bool
natBool 0 = False 
natBool 1 = True 

{-@ reflect natPos @-}
{-@ natPos :: {v:Int | 0 < v} -> Pos @-}
natPos :: Int -> Pos
natPos 1 = XH
natPos n = X (natBool b') (natPos n') 
  where 
     b'  = n `mod` 2 
     n'  = n `div` 2

{-@ lem_natPosNat :: p:_ -> {p = natPos (posNat p)} @-}
lem_natPosNat :: Pos -> Proof
lem_natPosNat XH          = () 
lem_natPosNat (X False p) = lem_natPosNat p
lem_natPosNat (X True  p) = lem_natPosNat p &&& lem_mod2 (posNat p)

-- | A few handy facts about div and mod --------------------

{-@ lem_div2 :: n:{0 < n} -> { div (1 + (2 * n)) 2 == n } @-}
lem_div2 :: Int -> Proof
lem_div2 _ = ()

{-@ lem_mod2 :: n:{0 < n} -> { (1 + (2 * n)) mod 2 == 1 } @-}
lem_mod2 :: Int -> Proof
lem_mod2 _ = ()

{-@ lem_posNatPos :: n:{0 < n} -> {n = posNat (natPos n) } @-}
lem_posNatPos :: Int -> Proof
lem_posNatPos 1 = () 
lem_posNatPos n = lem_posNatPos (n `div` 2)

{- 
{-@ lem_divmod2 :: n:{0 < n} -> { n == (n mod 2) + 2 * (div n 2) } @-}
lem_divmod2 :: Int -> Proof
lem_divmod2 _ = () 

{-@ lem_boolNatBool :: b:{0 == b || b == 1} -> {b == boolNat (natBool b)} @-}
lem_boolNatBool :: Int -> Proof
lem_boolNatBool 0 = ()
lem_boolNatBool 1 = ()


-- &&& lem_boolNatBool b') 
                  posNat (natPos n) 
              === posNat (X (natBool b') (natPos n')) 
              === boolNat (natBool b') + 2 * (posNat (natPos n'))
                ? lem_posNatPos n' -- &&& lem_boolNatBool b') 
              === b' + 2 * n'
              === n 
              *** QED
  where
    b' = n `mod` 2 
    n' = n `div` 2
-}
-- | posNat / natPos are injective --------------------------------------------

{-@ thm_posNat_inj :: p1:_ -> p2:_ -> { (p1 = p2) <=> (posNat p1 = posNat p2)} @-}
thm_posNat_inj :: Pos -> Pos -> Proof
thm_posNat_inj p1 p2 = lem_natPosNat p1 &&& lem_natPosNat p2 

