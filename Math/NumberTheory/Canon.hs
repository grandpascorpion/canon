-- |
-- Module:      Math.NumberTheory.Canon
-- Copyright:   (c) 2015-2018 Frederick Schneider
-- Licence:     MIT
-- Maintainer:  Frederick Schneider <frederick.schneider2011@gmail.com> 
-- Stability:   Provisional
--
-- A Canon is an exponentation-based representation for arbitrarily massive numbers, including prime towers.

{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies, PatternSynonyms, ViewPatterns, RankNTypes #-}

module Math.NumberTheory.Canon ( 
  makeCanon, makeC,
  canonToGCR, cToGCR,

  cMult, cDiv, cAdd, cSubtract, cExp,
  cReciprocal,
  cGCD, cLCM, cMod, cOdd, cTotient, cPhi,
  cLog, cLogDouble,
  cNegative, cPositive,
  cIntegral, cRational, cIrrational,
  cSimplify, cSimplified, 
  cDepth, 
  cSplit, cNumerator, cDenominator,
  cCanonical, cBare, cBareStatus, cValueType,
  cIsPrimeTower, cPrimeTowerLevel,
                                               
  cTetration, cPentation, cHexation, cHyperOp,
  (>^), (<^), (%), (<^>), (<<^>>), (<<<^>>>)         
)
where

import Math.NumberTheory.Primes.Testing (isPrime)
import Data.List (intersperse)
import GHC.Real (Ratio(..))
import Math.NumberTheory.Canon.Internals
import Math.NumberTheory.Canon.Additive
import Math.NumberTheory.Canon.AurifCyclo (CycloMap, crCycloInitMap)
import Math.NumberTheory.Canon.Simple (CanonConv(..))

-- | CanonValueType: 3 possibilities for this GADT.  Imaginary/complex numbers are not supported
data CanonValueType = IntegralC | NonIntRationalC | IrrationalC deriving (Eq, Ord, Show)

-- | GCR_ stands for Generalized Canonical Representation
type GCR_  = [GCRE_]
type GCRE_ = (Integer, Canon)

-- | Canon: GADT for either Bare or some variation of a canonical form.
data Canon = Bare Integer BareStatus | Canonical GCR_ CanonValueType 

-- | BareStatus: A "Bare Simplified" number means a prime number, +/-1 or 0.  The code must set the flag properly
--               A "Bare NotSimplified" number is an Integer that has not been checked (to see if it can be factored).
data BareStatus = Simplified | NotSimplified deriving (Eq, Ord, Show)

makeCanon, makeC, makeCanonFull, makeDefCanonForExpnt :: Integer -> Canon

-- | Create a Canon from an Integer.  This may involve expensive factorization.
makeCanon n = makeCanonI n False

-- | Shorthand for makeCanon
makeC       = makeCanon

-- | Make a Canon and attempt a full factorization
makeCanonFull n = makeCanonI n True

makeCanonI :: Integer -> Bool -> Canon
makeCanonI n b = crToC (crFromI n) b 
-- TODO: next step: enhance this once we can partially factor numbers

cCutoff :: Integer
cCutoff = 1000000

-- | Create type of Canon based on whether it exceeds a cutoff
makeDefCanonForExpnt e | e > cCutoff = Bare e (getBareStatus e) 
                       | otherwise   = makeCanonFull e

-- | Convert from underlying canonical rep. to Canon.  The 2nd param indicates whether or not to force factorization/simplification.
crToC :: CR_ -> Bool -> Canon
crToC POne _                  = Bare 1              Simplified
crToC c    b | crSimplified c = Bare (fst $ head c) Simplified -- a little ugly
             | otherwise      = Canonical g (gcrCVT g)
                                where g          = map (\(p,e) -> (p, convPred e)) c
                                      convPred e | b =         makeCanonFull e        -- do complete factorization
                                                 | otherwise = makeDefCanonForExpnt e
                                                  -- Leave exponents "Bare" with flag based on if whether it's "simplified"
                                                 -- (can't be reduced any further)

-- | Instances for Canon
instance Eq Canon where
  x == y = cEq x y

instance Show Canon where 
  show (Bare n NotSimplified) = "(" ++ (show n) ++ ")" -- Note the extra characters.  This does not mean the figure is negative.
  show (Bare n Simplified)    = show n
  show c                      | denom == c1 = s numer False 
                              | otherwise   = s numer True ++ " / " ++ s denom True
                              where (numer, denom)      = cSplit c  
                                    s (Bare n f) _ = show $ Bare n f
                                    s v          w | w         = "(" ++ catList ++ ")" 
                                                   | otherwise = catList               -- w = with(out) parens
                                                   where catList   = concat $ intersperse " * " $ map sE $ cToGCR v -- sE means showElem
                                                         sE (p, e) | ptLevel > 2 = sp ++ " <^> " ++ s (makeCanonFull $ ptLevel) True
                                                                   | otherwise   = case e of
                                                                                     Bare 1 _ -> sp 
                                                                                     Bare _ _ -> sp ++ "^" ++ se
                                                                                     _        -> sp ++ " ^ (" ++ se ++ ")"
                                                                   where ptLevel = cPrimeTowerLevelI e p 1 
                                                                         sp      = show p
                                                                         se      = show e
                                                                          -- TODO: try for add'l collapse into <<^>>
                                                                                     
instance Enum Canon where
  toEnum   n = makeCanon $ fromIntegral n
  fromEnum c = fromIntegral $ cToI c

instance Ord Canon where
  compare x y = cCmp x y 

instance Real Canon where
  toRational c | cIrrational c = toRational $ cToD c
               | otherwise     = (cToI $ cNumerator c) :% (cToI $ cDenominator c)

instance Integral Canon where
  toInteger c | cIntegral c = cToI c 
              | otherwise   = floor $ cToD c
  quotRem n m = fst $ cQuotRem n m crCycloInitMap  --  tries to use map but ultimately throws it away 
  -- ToDo: mod n m     = fst $ cModBAD n m crCycloInitMap -- fix this "bad" logic and use this instead of the original function
  mod n m     = cMod n m
            
instance Fractional Canon where
  fromRational (n :% d) = makeCanon n / makeCanon d                    
  (/) x y               = fst $ cDiv x y crCycloInitMap -- tries to use map but ultimately throws it away

instance Num Canon where -- tries to use the map but ultimately throws it away when using +, - and * operators
  fromInteger n = makeCanon n
  x + y         = fst $ cAdd      x y crCycloInitMap
  x - y         = fst $ cSubtract x y crCycloInitMap
  x * y         = fst $ cMult     x y crCycloInitMap
  
  negate x      = cNegate x
  abs x         = cAbs    x
  signum x      = cSignum x

-- | Checks if the Canon is Canonical, a more complex expression.
cCanonical :: Canon -> Bool
cCanonical (Canonical _ _ ) = True
cCanonical _                = False

-- | Checks if the Canon just a "Bare" Integer.
cBare :: Canon -> Bool
cBare (Bare _ _ ) = True
cBare _           = False

-- | Returns the status for "Bare" numbers.
cBareStatus :: Canon -> BareStatus
cBareStatus (Bare _ b) = b
cBareStatus _          = error "cBareStatus: Can only checked for 'Bare' Canons"

-- | Return the CanonValueType (Integral, etc).
cValueType :: Canon -> CanonValueType
cValueType (Bare      _ _ ) = IntegralC
cValueType (Canonical _ v ) = v

-- | Split a Canon into the numerator and denominator.
cSplit :: Canon -> (Canon, Canon)
cSplit c = (cNumerator c, cDenominator c)

-- | Check for equality.
cEq:: Canon -> Canon -> Bool  
cEq (Bare x _ )            (Bare y _ )            = x == y
cEq (Bare _ Simplified)    (Canonical _ _ )       = False
cEq (Canonical _ _ )       (Bare _ Simplified)    = False

cEq (Bare x NotSimplified) y                      | cValueType y /= IntegralC = False
                                                  | otherwise                 = cEq (makeCanon x) y

cEq x                      (Bare y NotSimplified) | cValueType x /= IntegralC = False
                                                  | otherwise                 = cEq x (makeCanon y)

cEq (Canonical x a )       (Canonical y b)        = if a /= b then False else gcrEqCheck x y

-- | Check if a Canon is an odd Integer.  Note: If the Canon is not integral, return False 
cOdd :: Canon -> Bool
cOdd (Bare x _)               = mod x 2 == 1
cOdd (Canonical c IntegralC ) = gcrOdd c
cOdd (Canonical _ _ )         = False

-- | GCD and LCM functions for Canon
cGCD, cLCM :: Canon -> Canon -> Canon
cGCD x y = cLGApply gcrGCD x y
cLCM x y = cLGApply gcrLCM x y

-- | Compute log as a Rational number.
cLog :: Canon -> Rational
cLog x = gcrLog $ cToGCR x 

-- | Compute log as a Double.
cLogDouble :: Canon -> Double
cLogDouble x = gcrLogDouble $ cToGCR x 

-- | Compare Function
cCmp :: Canon -> Canon -> Ordering
cCmp (Bare x _) (Bare y _) = compare x y
cCmp x          y          = gcrCmp (cToGCR x) (cToGCR y)

-- | QuotRem Function
cQuotRem :: Canon -> Canon -> CycloMap -> ((Canon, Canon), CycloMap)
cQuotRem x y m | cIntegral x && cIntegral y = ((gcrToC q', md'), m'')
               | otherwise                  = error "cQuotRem: Must both parameters must be integral"
               where (q', md', m'') = case gcrDiv (cToGCR x) gy of
                                        -- ToDo: Left  _        -> (q,        md, mm) -- fix "cModBAD" and stop pointing to orig fcn
                                        Left  _        -> (q,        md, m')
                                        Right quotient -> (quotient, c0, m)
                                      where gy       = cToGCR y
                                            -- ToDo: fix  (md, mm) = cModBAD x y m'  -- Better to compute quotient this way .. to take adv. of alg. forms
                                            md       = cMod x y
                                            q        = gcrDivStrict (cToGCR d) gy  -- equivalent to: (x - x%y) / y.
                                            (d, m')  = cSubtract x md m

-- | Mod function
cMod :: Canon -> Canon -> Canon
cMod c m = if (cIntegral c) && (cIntegral m) then (makeCanon $ cModI c (cToI m))
                                             else error "cMod: Must both parameters must be integral"

cModI :: Canon -> Integer -> Integer
cModI _   0       = error "cModI: Divide by zero error when computing n mod 0"
cModI _   1       = 0
cModI _   (-1)    = 0
cModI Pc1 PIntPos = 1
cModI Pc0 _       = 0
cModI c   m       | cn && mn         = -1 * cModI (cAbs c) (abs m)
                  | (cn && not mn) ||
                    (mn && not cn) = (signum m) * ( (abs m) - (cModI' (cAbs c) (abs m)) )
                  | otherwise        = cModI' c m
                    where cn         = cNegative c
                          mn         = m < 0

cModI' :: Canon -> Integer -> Integer
cModI' (Bare      n _         ) m = mod n m
cModI' (Canonical c IntegralC ) m = mod (product $ map (\x -> pmI (fst x) (mmt $ snd x) m) c) m
                                    where tm    = totient m
                                          mmt e = cModI e tm -- optimization
cModI' (Canonical _ _         ) _ = error "cModI': Logic error:  Canonical var has to be integral at this point" 

-- | Totient functions
cTotient, cPhi :: Canon -> CycloMap -> (Canon, CycloMap)
cTotient c m | (not $ cIntegral c) || cNegative c = error "Not defined for non-integral or negative numbers"
             | c == c0                            = (c0, m)
             | otherwise                          = f (cToGCR c) c1 m
             where f []         prd m' = (prd, m') 
                   f ((p,e):gs) prd m' = f gs wp mw 
                   -- f is equivalent to the crTotient function but with threading of CycloMap 
                   -- => product $ map (\(p,e) -> (p-1) * p^(e-1)) cr
                                       where cp           = makeC p -- "Canon-ize" this.  Generally, this should be a prime already
                                             (pM1, mp)    = cSubtract cp c1 m'
                                             (eM1, me)    = cSubtract e c1 mp 
                                             (pxeM1, mpm) = cExp cp eM1 False me
                                             (nprd, mprd) = cMult pM1 pxeM1 mpm    
                                             (wp, mw)     = cMult prd nprd  mprd

cPhi = cTotient

-- | The thinking around the hyperoperators is that they should look progressively scarier :)
infixr 9 <^>, <<^>>, <<<^>>>
(<^>), (<<^>>), (<<<^>>>) :: Canon -> Integer -> Canon
a <^>     b = fst $ cTetration a b crCycloInitMap
a <<^>>   b = fst $ cPentation a b crCycloInitMap
a <<<^>>> b = fst $ cHexation  a b crCycloInitMap

cTetration, cPentation, cHexation :: Canon -> Integer -> CycloMap -> (Canon, CycloMap)

-- | Tetration function
cTetration = cHyperOp 4 

-- | Pentation Function
cPentation = cHyperOp 5

-- | Hexation Function
cHexation  = cHyperOp 6

-- | Generalized Hyperoperation Function (https://en.wikipedia.org/wiki/Hyperoperation)
cHyperOp :: Integer -> Canon -> Integer -> CycloMap -> (Canon, CycloMap)
cHyperOp n a b m | b < -1                       = error "Hyperoperations not defined when b < -1"
                 | n < 0                        = error "Hyperoperations require the level n >= 0"
                 | a /= c0 && a /= c1 && 
                   b > 1 && (a /= c2 && b == 2) = c n cb m
                 | otherwise                    = (sp n a b, m)
                 where cb = makeCanon b
                       -- Function for regular cases
                       c 1  b' m'  = cAdd a b' m'  -- addition
                       c 2  b' m'  = cMult a b' m' -- multiplication
                       c 3  b' m'  = (a <^ b', m')  -- exponentiation: ToDo: Plug in the CycloMap logic for expo.
                       -- Tetration and beyond
                       c _  Pc1 m' = (a, m')
                       c n' b'  m' = c (n'-1) r m'' -- TODO: Find a way to optimize this
                                     where (r, m'') = c n' (b'-1) m'

                       -- Function for special cases:                 
                       -- Note: When n (first param) is zero, that is known as "succession"
                       --   Cases when a is zero ...
                       sp 0 Pc0 b'   = makeCanon (b' + 1)
                       sp 1 Pc0 b'   = makeCanon b'
                       sp 2 Pc0 _    = c0
                       sp 3 Pc0 b'   = if b' == 0 then c1 else c0
                       sp _ Pc0 b'   = if (mod b' 2) == 1 then c0 else c1
                       --   Cases when b is zero ...
                       sp 0 _   0    = c1 
                       sp 1 a'  0    = a'
                       sp 2 _   0    = c0 
                       sp _ _   0    = c1 
                       --   Cases when b is -1 ...
                       sp 0 _   (-1) = c0
                       sp 1 a'  (-1) = a' - 1
                       sp 2 a'  (-1) = cNegate a'
                       sp 3 a'  (-1) = cReciprocal a'
                       sp _ _   (-1) = c0
                       --   Other Cases ...
                       sp h Pc2 2    | h == 0    = makeCanon 3
                                     | otherwise = makeCanon 4 -- recursive identity
                       sp _ Pc1 _    = c1
                       sp _ a'  1    = a'
                       sp _ _   _    = error "Can't compute this hyperoperation.  b must be >= -1"                

infixl 7 %
-- | Mod operator
(%) :: (Integral a) => a -> a -> a
n % m = mod n m 

-- | Exponentation operator declaration
infixr 9 <^   
-- Note: Even with Flexible Contexts switched on, it doesn't infer a bare number to be an Integer

-- | Dedicated multi-param typeclass for exponentiation operator.
class CanonExpnt a b c | a b -> c where 
  -- | Exponentiation operator
  (<^) :: a -> b -> c

instance CanonExpnt Canon Canon Canon where
  p <^ e = fst $ cExp p e True crCycloInitMap 
  
instance CanonExpnt Integer Integer Canon where
  p <^ e = fst $ cExp (makeCanon p) (makeDefCanonForExpnt e) True crCycloInitMap

instance CanonExpnt Canon Integer Canon where
  p <^ e = fst $ cExp p (makeDefCanonForExpnt e) True crCycloInitMap

instance CanonExpnt Integer Canon Canon where
  p <^ e = fst $ cExp (makeCanon p) e True crCycloInitMap

-- | Operator declaration: r >^ n means: attempt to take the rth root of n 
infixr 9 >^ 

-- | Dedicated multi-param typeclass for radical or root operator.
class CanonRoot a b c | a b -> c where 
  -- | Root operator
  (>^) :: a -> b -> c

instance CanonRoot Canon Canon Canon where
  r >^ n = cRoot n r
  
instance CanonRoot Integer Integer Canon where
  r >^ n = cRoot (makeCanon n) (makeCanon r)
  
instance CanonRoot Integer Canon Canon where
  r >^ n = cRoot n (makeCanon r) 

instance CanonRoot Canon Integer Canon where
  r >^ n = cRoot (makeCanon n) r 

-- | Check if underlying rep is simplified
crSimplified :: CR_ -> Bool
crSimplified POne  = True
crSimplified PZero = True                                                        
crSimplified PN1   = True  
crSimplified c     = crPrime c

-- | Convert a Canon back to its underlying rep (if possible).
cToCR :: Canon -> CR_
cToCR (Canonical c v)         | v /= IrrationalC = gcrToCR c 
                              | otherwise        = error "cToCR: Cannot convert irrational canons to underlying data structure"
cToCR (Bare 1 _ )             = cr1
cToCR (Bare n NotSimplified)  = crFromI n
cToCR (Bare n Simplified)     = [(n,1)] -- not ideal

-- | Convert generalized canon rep to Canon.
gcrToC :: GCR_ -> Canon
gcrToC g | gcrBare g = Bare (gcrToI g) Simplified
         | otherwise = Canonical g (gcrCVT g)

-- | For generalized canon rep, determine the CanonValueType.   
gcrCVT :: GCR_ -> CanonValueType         
gcrCVT POne = IntegralC
gcrCVT g    = g' g IntegralC -- start Integral, can only get "worse"
              where g' _           IrrationalC = IrrationalC -- short-circuits once IrrationalC is found
                    g' POne        v           = v
                    g' ((_,ce):cs) v           = g' cs (dcv v ce) -- check the exponents for expr's value type
                    g' _           _           = error "gcrCVT : Logic error. Patterns should have been exhaustive"

                    -- checking exponents
                    dcv IrrationalC _                             = IrrationalC
                    dcv _           (Canonical _ IrrationalC)     = IrrationalC
                    dcv _           (Canonical _ NonIntRationalC) = IrrationalC
                    dcv IntegralC   (Bare      n _ )              = if n < 0 then NonIntRationalC else IntegralC
                    dcv v           (Bare      _ _ )              = v
                    dcv v           c                             = if cNegative c then NonIntRationalC else v

c1, c0, cN1, c2 :: Canon
c1  = makeCanon 1
c0  = makeCanon 0
cN1 = makeCanon (-1)
c2  = makeCanon 2

-- | Convert Canon to Integer if possible.
cToI :: Canon -> Integer
cToI (Bare i _ )     = i
cToI (Canonical c v) | v == IntegralC = gcrToI c 
                     | otherwise      = error "Can't convert non-integral Canon to an Integer"

-- | Convert Canon To Double.
cToD :: Canon -> Double
cToD (Bare i _ )      = fromIntegral i
cToD (Canonical c _ ) = gcrToD c 

-- | Multiply Function: Generally speaking, this will be much cheaper.
cMult :: Canon -> Canon -> CycloMap -> (Canon, CycloMap) 
cMult Pc0 _   m = (c0, m)
cMult _   Pc0 m = (c0, m)
cMult Pc1 y   m = (y, m)
cMult x   Pc1 m = (x, m)
cMult x   y   m = (gcrToC g, m') 
                  where (g, m') = gcrMult (cToGCR x) (cToGCR y) m

-- | Addition and subtraction is generally much more expensive because it requires refactorization.
--   There is logic to look for algebraic forms which can greatly reduce simplify factorization.
cAdd, cSubtract :: Canon -> Canon -> CycloMap -> (Canon, CycloMap)
cAdd      = cApplyAdtvOp True 
cSubtract = cApplyAdtvOp False 

-- | Internal Function to compute sum or difference based on first param.  Much heavy lifting under the hood here.
cApplyAdtvOp :: Bool -> Canon -> Canon -> CycloMap -> (Canon, CycloMap)
cApplyAdtvOp _     x   Pc0 m = (x, m)
cApplyAdtvOp True  Pc0 y   m = (y, m)         -- True -> (+)
cApplyAdtvOp False Pc0 y   m = (negate y, m)  -- False -> (-) 
cApplyAdtvOp b     x   y   m = (gcd' * r, m')
                               where gcd'    = cGCD x y 
                                     x'      = x / gcd'
                                     y'      = y / gcd'
                                     r       = crToC c False
                                     (c, m') = crApplyAdtvOptConv b (cToCR x') (cToCR y') m -- costly bit

-- | Exponentiation: This does allow for negative exponentiation if the Bool flag is True.
cExp :: Canon -> Canon -> Bool -> CycloMap -> (Canon, CycloMap)
cExp c e b m | cNegative e && (not b) 
                         = error "Per param flag, negative exponentiation is not allowed here."
             | cIrrational c && cIrrational e 
                         = error "cExp: Raising an irrational number to an irrational power is not currently supported."
             | otherwise = cExp' c e m
                         where cExp' Pc0 e'  m' | cPositive e' = (c0, m')
                                                | otherwise    = error "0^e where e <= 0 is either undefined or illegal"
                               cExp' Pc1 _   m' = (c1, m')
                               cExp' _   Pc0 m' = (c1, m')
                               cExp' c'   e' m' = (gcrToC g, mg)
                                                  where (g, mg) = gE (cToGCR c') e' m' 
                               gE :: GCR_ -> Canon -> CycloMap -> (GCR_, CycloMap)
                               gE g' e' m' | gcrNegative g' 
                                             = case cValueType e' of  -- gcr exponentiation
                                                 IntegralC       -> if cOdd e' then (gcreN1:absTail, m'')
                                                                               else (absTail, m'')
                                                 NonIntRationalC -> if cOdd d then (gcreN1:absTail, m'')
                                                                              else error "gE: Imaginary numbers not supported"
                                                 IrrationalC     -> error "gE: Raising neg numbers to irr. powers not supported" 
                                           | otherwise      
                                             = f g' m' -- equivalent to multiplying each exp by e' (with CycloMap threaded)
                                           where (absTail, m'')  = gE (gcrAbs g') e' m'
                                                 (_, d)          = cSplit e' -- even denominator means you will have an imag. number
                                                 f []         mf = ([], mf) 
                                                 f ((p,x):gs) mf = (fp, mf')
                                                                    where (prd, mx) = cMult e' x mf
                                                                          (t, mn)   = f gs mx
                                                                          (fp, mf') = gcrMult [(p, prd)] t mn

-- | Functions to check if a canon is negative/positive
cNegative, cPositive :: Canon -> Bool

cNegative (Bare n      _ ) = n < 0
cNegative (Canonical c _ ) = gcrNegative c

cPositive (Bare n _      ) = n > 0
cPositive (Canonical c _ ) = gcrPositive c

-- | Functions for negation, absolute value and signum
cNegate, cAbs, cSignum :: Canon -> Canon 

cNegate (Bare 0 _)             = c0
cNegate (Bare 1 _)             = cN1
cNegate (Bare x Simplified)    = Canonical (gcreN1 : [(x, c1)]) IntegralC -- prepend a "-1", not ideal
cNegate (Bare x NotSimplified) = Bare (-1 * x) NotSimplified 
cNegate (Canonical x v)        = gcrNegateCanonical x v
      
cAbs x | cNegative x = cNegate x
       | otherwise   = x

cSignum (Bare 0 _)      = c0
cSignum g | cNegative g = cN1
          | otherwise   = c1

-- This internal function works for either gcrGCD or gcrLCM.
cLGApply :: (GCR_ -> GCR_ -> GCR_) -> Canon -> Canon -> Canon
cLGApply _ Pc0 y   = y
cLGApply _ x   Pc0 = x
cLGApply f x   y   | cNegative x || 
                     cNegative y = gcrToC $ f (cToGCR $ cAbs x) (cToGCR $ cAbs y)
                   | otherwise   = gcrToC $ f (cToGCR x)        (cToGCR y)

-- | Div function : Multiply by the reciprocal.
cDiv :: Canon -> Canon -> CycloMap -> (Canon, CycloMap)
cDiv _ Pc0 _ = error "cDiv: Division by zero error"
cDiv x y   m = cMult (cReciprocal y) x m -- multiply by the reciprocal

-- | Compute reciprocal (by negating exponents).
cReciprocal :: Canon -> Canon
cReciprocal x = fst $ cExp x cN1 True crCycloInitMap  -- raise number to (-1)st power

-- | Functions to check if a Canon is Integral, (Ir)Rational, "Simplified" or a prime tower
cIntegral, cIrrational, cRational, cSimplified, cIsPrimeTower :: Canon -> Bool

cIntegral (Bare      _ _ ) = True
cIntegral (Canonical _ v ) = v == IntegralC

cIrrational (Canonical _ IrrationalC ) = True
cIrrational _                          = False

cRational c = not $ cIrrational c

cSimplified (Bare      _ Simplified)    = True
cSimplified (Bare      _ NotSimplified) = True
cSimplified (Canonical c _ )            = gcrSimplified c

cIsPrimeTower c = cPrimeTowerLevel c > 0 -- x^x would not be, but x^x^x would be

-- | cNumerator and cDenominator are for processing "rational" canon reps.
cNumerator, cDenominator :: Canon -> Canon

cNumerator (Canonical c _ ) = gcrToC $ filter (\x -> cPositive $ snd x) c -- filter positive exponents
cNumerator b                = b 

cDenominator (Canonical c _ ) = gcrToC $ map (\(p,e) -> (p, cN1 * e)) $ filter (\(_,e) -> cNegative e) c -- negate negative expnts
cDenominator _                = c1 

-- | Determines the depth/height of maximum prime tower in the Canon.
cDepth :: Canon-> Integer
cDepth (Bare      _ _ ) = 1
cDepth (Canonical c _ ) = 1 + gcrDepth c

-- | Force the expression to be simplified.  This could potentially be very expensive.
cSimplify :: Canon -> Canon
cSimplify (Bare      n NotSimplified) = makeCanonFull n
cSimplify (Canonical c _ )            = gcrToC $ gcrSimplify c
cSimplify g                           = g  -- Bare number already simplified : Fix when expr come into play

-- | Compute the rth-root of a Canon.
cRoot :: Canon -> Canon -> Canon 
cRoot c r | cNegative r = error "r-th roots are not allowed when r <= 0" 
          | otherwise   = gcrToC $ gcrRootI (cToGCR c) (cToGCR r)

-- | This is used for tetration, etc.  It defaults to zero for non-integral reps.
cPrimeTowerLevel :: Canon -> Integer                  
cPrimeTowerLevel (Bare      _ Simplified) = 1
cPrimeTowerLevel (Canonical g IntegralC)  = case gcrPrimePower g of
                                              False -> 0
                                              True  -> cPrimeTowerLevelI (snd $ head g) (fst $ head g) (1 :: Integer)
cPrimeTowerLevel _                        = 0

-- | Internal workhorse function
cPrimeTowerLevelI :: Canon -> Integer -> Integer -> Integer
cPrimeTowerLevelI (Bare b _ )             n l | b == n    = l + 1 
                                              | otherwise = 0
cPrimeTowerLevelI (Canonical g IntegralC) n l | gcrPrimePower g == False = 0 
                                              | n /= (fst $ head g)      = 0
                                              | otherwise                = cPrimeTowerLevelI (snd $ head g) n (l+1)
cPrimeTowerLevelI _                       _ _ = 0

-- | Functions to convert Canon to generalized canon rep
canonToGCR, cToGCR :: Canon -> GCR_
canonToGCR (Canonical x _) = x
canonToGCR (Bare x NotSimplified) = canonToGCR $ makeCanon x -- ToDo: Thread in CycloMap?
canonToGCR (Bare x Simplified)    | x == 1    = gcr1 
                                  | otherwise = [(x, c1)]
cToGCR = canonToGCR

-- Warning: Don't call this for 0 or +/- 1.  The value type will not change by negating the value     
gcrNegateCanonical :: GCR_ -> CanonValueType -> Canon    
gcrNegateCanonical g  v | gcrNegative g = case gcrPrime (tail g) of
                                            True  -> Bare (fst $ head $ tail g) Simplified
                                            False -> Canonical (tail g) v             
                        | otherwise     = Canonical (gcreN1 : g) v -- just prepend

gcrNegate :: GCR_ -> GCR_
gcrNegate Pg0               = gcr0
gcrNegate x | gcrNegative x = tail x 
            | otherwise     = gcreN1 : x 

gcrNegative :: GCR_ -> Bool
gcrNegative PgNeg = True
gcrNegative _     = False

gcrPositive :: GCR_ -> Bool
gcrPositive PNeg  = False
gcrPositive PZero = False
gcrPositive _     = True

gcrMult :: GCR_ -> GCR_ -> CycloMap -> (GCR_, CycloMap)
gcrMult x                 POne              m = (x, m)
gcrMult POne              y                 m = (y, m)
gcrMult _                 Pg0               m = (gcr0, m)
gcrMult Pg0               _                 m = (gcr0, m)
gcrMult x@(xh@(xp,xe):xs) y@(yh@(yp,ye):ys) m = case compare xp yp of
                                                LT -> (xh:g, m') 
                                                      where (g, m') = gcrMult xs y m
                                                EQ -> if gcrNegative x || expSum == c0 
                                                      then gcrMult xs ys m -- cancel double negs/exponents adding to zero
                                                      else ((xp, expSum):gf, mf) 
                                                      where (expSum, m') = cAdd xe ye m 
                                                            (gf, mf)     = gcrMult xs ys m'
                                                GT -> (yh:g, m') 
                                                      where (g, m') = gcrMult x ys m
gcrMult x                 y                 _ = error e 
                                                where e = "Non-exhaustive pattern error in gcrMult.  Params: " ++ (show x) ++ "*" ++ (show y)

gcr1, gcr0 :: GCR_
gcr1 = []
gcr0 = [(0, c1)]   

gcreN1 :: GCRE_
gcreN1 = (-1, c1)

gcrToI :: GCR_ -> Integer
gcrToI g = product $ map f g
           where f (p, e)  | ce > 0    = p ^ ce 
                           | otherwise = error negExpErr
                           where ce = cToI e 
                 negExpErr = "gcrToI: Negative exponent found trying to convert " ++ (show g)

gcrToD :: GCR_ -> Double
gcrToD g = product $ map (\(p,e) -> (fromIntegral p) ** cToD e) g
                        
gcrCmp :: GCR_ -> GCR_ -> Ordering
gcrCmp POne y            = gcrCmpTo1 y True
gcrCmp x    POne         = gcrCmpTo1 x False
gcrCmp x y | x == y      = EQ            
           | xN && yN    = compare (gcrToC $ tail y) (gcrToC $ tail x)
           | xN          = LT
           | yN          = GT         
           | gcrIsZero x = LT
           | gcrIsZero y = GT
           | otherwise   = case compare (gcrLogDouble x) (gcrLogDouble y) of
                              -- If equal: we have to break out the big guns, both evaluate to infinity
                             EQ  -> compare (gcrLog'' x) (gcrLog'' y) 
                             cmp -> cmp

           where xN          = gcrNegative x
                 yN          = gcrNegative y  

                 -- This is much more expensive but accurate. You have an "infinity" result issue potentially with gcrLogDouble
                 gcrLog'' g = sum $ map f g
                 f (p,e)    = (toRational $ logDouble $ fromIntegral p) * (toRational e)
                 logDouble :: Double -> Double
                 logDouble n = log n
                
gcrCmpTo1 :: GCR_ -> Bool -> Ordering
gcrCmpTo1 PNeg b = if b then GT else LT
gcrCmpTo1 Pg0  b = if b then GT else LT
gcrCmpTo1 _    b = if b then LT else GT 

gcrLog :: GCR_ -> Rational
gcrLog g = crLog $ gcrToCR g   

-- | These internal functions should not be called directly.  The definition of GCD and LCM are extended to handle non-Integers.
gcrGCD, gcrLCM :: GCR_ -> GCR_ -> GCR_
gcrGCD POne _    = gcr1
gcrGCD _    POne = gcr1
gcrGCD x    y    = case compare xp yp of
                      LT -> gcrGCD xs y
                      EQ -> (xp, min xe ye) : gcrGCD xs ys                    
                      GT -> gcrGCD x ys
                    where ((xp,xe):xs) = x
                          ((yp,ye):ys) = y    
gcrLCM POne y    = y
gcrLCM x    POne = x        
gcrLCM x    y    = case compare xp yp of
                      LT -> xh : gcrLCM xs y
                      EQ -> (xp, max xe ye) : gcrLCM xs ys
                      GT -> yh : gcrLCM x ys
                    where (xh@(xp,xe) : xs)  = x
                          (yh@(yp,ye) : ys)  = y  

gcrLogDouble :: GCR_ -> Double
gcrLogDouble g = sum $ map (\(p,e) -> (log $ fromIntegral p) * (cToD e)) g

divisionError :: String
divisionError = "gcrDiv: As requested per param, the dividend must be a multiple of the divisor." 

divByZeroError :: String
divByZeroError = "gcrDiv: Division by zero error!"

zeroDivZeroError :: String
zeroDivZeroError = "gcrDiv: Zero divided by zero is undefined!"

gcrDivStrict :: GCR_ -> GCR_ -> GCR_
gcrDivStrict x y = case (gcrDiv x y) of
                       Left errorMsg -> error errorMsg
                       Right results -> results

gcrDiv :: GCR_ -> GCR_ -> Either String GCR_
gcrDiv Pg0 Pg0 = Left zeroDivZeroError 
gcrDiv Pg0 _   = Right gcr0
gcrDiv _   Pg0 = Left divByZeroError
gcrDiv n   d   = g' n d 
                 where g' x     POne = Right x
                       g' POne  _    = Left divisionError
                       g' x     y 
                                     | gcrNegative y  = g' (gcrNegate x) (gcrAbs y)
                                     | otherwise      = case compare xp yp of      
                                                        LT           -> case (g' xs y) of
                                                                        Left _    -> Left divisionError
                                                                        Right res -> Right ((xp, xe) : res)
                                                        EQ | xe > ye -> case (g' xs ys) of
                                                                        Left _    -> Left divisionError
                                                                        Right res -> Right ((xp, xe - ye) : res)
                                                        EQ | xe == ye -> gcrDiv xs ys
                                                        _             -> Left divisionError                     
                                                        where ((xp,xe):xs) = x
                                                              ((yp,ye):ys) = y 

-- GCR functions (GCR is an acronym for generalized canonical representation)
gcrAbs :: GCR_ -> GCR_
gcrAbs x | gcrNegative x = tail x
         | otherwise     = x

gcrToCR :: GCR_ -> CR_
gcrToCR c = map (\(p,e) -> (p, cToI e)) c

gcrBare :: GCR_ -> Bool
gcrBare PBare = True
gcrBare POne  = True
gcrBare _     = False

gcrPrime :: GCR_ -> Bool
gcrPrime PgPrime = True
gcrPrime _       = False   

gcrPrimePower :: GCR_ -> Bool
gcrPrimePower PgPPower = True
gcrPrimePower _        = False 

gcrIsZero :: GCR_ -> Bool
gcrIsZero Pg0 = True;
gcrIsZero _   = False  

gcrOdd, gcrEven :: GCR_ -> Bool
gcrOdd Pg0  = False
gcrOdd POne = True
gcrOdd c    | gcrNegative c  = gcrOdd (gcrAbs c)
            | otherwise      = cp /= 2 
              where (cp,_):_ = c

gcrEven g   = not (gcrOdd g)

gcrEqCheck :: GCR_ -> GCR_ -> Bool
gcrEqCheck POne         POne         = True
gcrEqCheck POne         _            = False
gcrEqCheck _            POne         = False 
gcrEqCheck ((xp,xe):xs) ((yp,ye):ys) | xp /= yp || xe /= ye = False 
                                     | otherwise            = gcrEqCheck xs ys
gcrEqCheck x            y            = error e
                                     where e = "Non-exhaustive patterns in gcrEqCheck comparing " ++ (show x) ++ " to " ++ (show y)

gcrDepth :: GCR_ -> Integer
gcrDepth g = maximum $ map (\(_,e) -> cDepth e) g

gcrSimplified :: GCR_ -> Bool
gcrSimplified g = all (\(_,e) -> cSimplified e) g               

gcrSimplify :: GCR_ -> GCR_
gcrSimplify g = map (\(p,e) -> (p, cSimplify e)) g

gcrRootI :: GCR_ -> GCR_ -> GCR_
gcrRootI POne _ = gcr1   
gcrRootI c    r | not $ gcrNegative c = case gcrDiv (cToGCR ce) r of
                                          Left  _        -> error e 
                                          Right quotient -> (cp, gcrToC quotient) : gcrRootI cs r
                | gcrEven r           = error "Imaginary numbers not allowed: Even root of negative number requested."
                | otherwise           = gcreN1 : gcrRootI (gcrAbs c) r
                where ((cp,ce):cs) = c  
                      e            = "gcrRootI: All expnts must be multiples of " ++ (show r) ++ ".  Not so with " ++ (show c)

-- | Check if the number is simplified rather than factoring it.  Simplified is equivalent to having one term in the list.
getBareStatus :: Integer -> BareStatus
getBareStatus n | n < -1              = NotSimplified 
                | n <= 1 || isPrime n = Simplified 
                | otherwise           = NotSimplified

-- | Instance of CanonConv class 
instance CanonConv Canon where
  toSC c = toSC $ cToCR c
  toRC c = toRC $ cToCR c
                                                                   
-- | Canon of form x^1. (Does not match on 1 itself)
pattern PBare :: forall t. [(t, Canon)]
pattern PBare <- [(_, Bare 1 _)] 

-- | Canon of form p^e where e >= 1. p has already been verified to be prime.
pattern PgPPower :: forall t a. (Num a, Ord a) => [(a, t)]
pattern PgPPower <- [(compare 1 -> LT, _ )]

-- | Canon of form p^1 where p is prime
pattern PgPrime :: forall a. (Num a, Ord a) => [(a, Canon)]
pattern PgPrime <- [(compare 1 -> LT, Bare 1 _)] 

-- | Pattern looks for Canons beginning with negative 1
pattern PgNeg :: forall a. (Num a, Eq a) => [(a, Canon)]
pattern PgNeg <- ((-1, Bare 1 _):_) 

-- | Pattern for "generalized" zero
pattern Pg0 :: forall a. (Num a, Eq a) => [(a, Canon)]
pattern Pg0 <- [(0, Bare 1 _)]  -- internal pattern for zero

-- | Patterns for 0 and 1
pattern Pc0 :: Canon
pattern Pc0 <- Bare 0 _

pattern Pc1 :: Canon
pattern Pc1 <- Bare 1 _ 

pattern Pc2 :: Canon
pattern Pc2 <- Bare 2 _

-- ToDo: Fix this Mod function.  "Proper" rewrite has terrible performance
{-
pattern PcN1 :: Canon  -- this pattern is only used in the "bad" function
pattern PcN1 <- Canonical [(-1, Bare 1 _)] _

cModBAD :: Canon -> Canon -> CycloMap -> (Canon, CycloMap)
cModBAD c m cm | cIntegral c && cIntegral m = f c m cm
            | otherwise                  = error "cModBAD: Must both parameters must be integral"
     where f _   Pc0  _   = error "cModBAD: Divide by zero error when computing n mod 0"
           f _   Pc1  cm' = (0, cm')
           f _   PcN1 cm' = (0, cm')
           f Pc0 _    cm' = (0, cm')
           f c'  m'   cm' | m' == c0         = error "cModBAD: Divide by zero error when computing n mod 0"
                          | ma == c1         = (c0, cm')
                          | ca == ma         = (c0, cm')
                          | cn && mn         = (cNegate mrn, cmn) -- both (n)egative
                          | (not cn) && (not mn) &&
                            ca < ma          = (ca, cm')
                          | (cn && not mn) ||
                            (mn && not cn) = ((cSignum m') * (makeC $ maI - mrm), cmm) -- (m)ixed sign: TODO: CycloMap threading
                          | otherwise        = (makeC io, mo)
                          where (cn, mn)     = (cNegative c', cNegative m')
                                (ca, ma)     = (cAbs c', cAbs m')
                                (mrn, cmn)   = f ca ma cm'
                                (mrm, cmm)   = f' ca maI cm'
                                maI          = cToI ma
                                (io, mo)     = f' c' (cToI m') cm'
           f' (Bare      n  _           ) mI cm' = (mod n mI, cm')
           f' ic@(Canonical c' IntegralC) mI cm' | cNegative ic = error "The canon must be positive here"
                                                 | otherwise    = (mod ip mI, cmf)
                                                 where (ip, cmf) = i c' cm'' (1 :: Integer) -- performs fold-like product
                                                       i []     cmi pri = (pri, cmi)          -- with CycloMap threading
                                                       i (l:ls) cmi pri | pri == 0   = (pri, cmi)
                                                                        | otherwise = i ls cmv (pri * v)
                                                                        where (v, cmv) = pf l cmi
                                                       pf (p,e) mp      = (pmI p (cToI v) mI, cmv)
                                                                          where (v, cmv) = f e tm mp
                                                       (tm, cm'')       = cTotient ic cm'
           f' (Canonical _  _           ) _  _   = error "cModBAD: Logic error:  Canonical var has to be integral at this point"
-}

