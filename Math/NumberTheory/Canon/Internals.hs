-- |
-- Module:      Math.NumberTheory.Canon.Internals
-- Copyright:   (c) 2015-2019 Frederick Schneider
-- Licence:     MIT
-- Maintainer:  Frederick Schneider <fws.nyc@gmail.com>
-- Stability:   Provisional
--
-- This module defines the internal canonical representation of numbers (CR_), a product of pairs (prime and exponent). 
-- PLEASE NOTE: It's not meant to be called directly.  The Canon and SimpleCanon modules should be used instead.

{-# LANGUAGE PatternSynonyms, ViewPatterns, ScopedTypeVariables, DataKinds, RankNTypes #-}

module Math.NumberTheory.Canon.Internals (
  CanonRep_,       CR_,                        CanonElement_,
  crValidIntegral, crValidIntegralViaUserFunc,
  crValidRational, crValidRationalViaUserFunc,
  crExp,
  crRoot, 
  crMaxRoot,
  crShow,
  ceShow,
  crFromInteger,   crFromI,
  crToInteger,     crToI,
  crCmp, 
  crMult,
  crNegate,
  crAbs,
  crDivStrict,
  crSignum,
  crNumer,
  crDenom,
  crSplit,
  crDivRational,
  crIntegral,
  crShowRational,
  crToRational,
  crGCD,
  crLCM,
  crNegative,
  crPositive,
  crLog,
  crLogDouble,
  crDiv,
  crRadical,
  integerApply,
  crSimpleApply,
  crPrime,
  crHasSquare,
  crRecip,
  crMin,
  crMax,
  crValid,
  crMod, crModI,
  crSimplified,
  
  crDivisors,
  crNumDivisors,
  crWhichDivisor,
  crNthDivisor,
  crDivsPlus,
  crTau,
  crTotient,
  crPhi,
   
  crN1,
  cr0,
  cr1,
  creN1,
   
  crFactCutoff, crSmallFactCutoff,
 
  pattern PZero,
  pattern PZeroBad,
  pattern POne,
  pattern PNeg,
  pattern PNotPos,
  pattern PN1,
  
  pattern PIntNeg,
  pattern PIntNPos,
  pattern PIntPos,

  -- Functions deprecated from arithmoi that needed to be included here
  totient,
  pmI -- Short for powerModInteger
) 
where

{- Canon or canon rep is short for canonical representation.

   In this context, it refers to the prime factorization of a number.
   Example: 250 = 2 * 5^3.  It would be represented internally here as: [(2,1),(5,3)]

   So, this library along with Canon.hs can be used as shorthand for extremely large numbers.
   Multiplicative actions are cheap.  But, addition and subtraction is potentially very expensive 
   as any "raw" sums or differences are factorized. There are optimizations for sums/differences
   including those with special forms (algebraic, Aurifeuillean).

   Here are the possibilities:
   
   Zero:             [(0,1)]
   
   One               [] 
   
   Other Positive 
   Numbers:          A set of (p,e) pairs where the p(rime)s are in ascending order. 
                     For "integers",  the e(xponents) must be positive
                     For "rationals", the e(xponents) must not be zero
                     All "integers" are "rationals" but not vice-versa.
   
   Negative Numbers: (-1,1):P where P is a canon rep for any positive number


   Note: Much of the code is spent on handling these special cases (Zero, One, Negatives).   
      
   Each integer and rational will have a unique "canon rep".
   
   Caveats: The behavior is undefined when directly working with "canon reps" which are not valid.
            The behavior of using rational CRs directly (when integral CRs are specified) is also undefined.
   
   The Canon library should be used as it hides these internal details.
-}

import Data.List (intersperse, partition)
import Math.NumberTheory.Primes.Factorisation (smallFactors, stdGenFactorisation, factorise') 
import System.Random (mkStdGen)
import Data.Bits (xor)
import Data.List (sortBy)
import Math.NumberTheory.Primes.Testing (isPrime)
import GHC.Real (Ratio(..))

-- | Canon element: prime and exponent pair
type CanonElement_ = (Integer,Integer)

-- | Canonical representation: list of canon elements
type CanonRep_     = [CanonElement_]

-- | Shorthand for canonical representation
type CR_           = CanonRep_

-- | Pattern to match the CR_ equivalent of 1
pattern POne :: forall t. [t]
pattern POne      = []

-- | Pattern to match the CR_ equivalent of zero
pattern PZero :: forall a a1. (Num a, Num a1, Eq a, Eq a1) => [(a1, a)]
pattern PZero     = [(0,1)]

-- | Pattern to match the CR_ equivalent of -1
pattern PN1 :: forall a a1. (Num a, Num a1, Eq a, Eq a1) => [(a1, a)]
pattern PN1       = [(-1,1)]

-- | Pattern to match a badly formed zero, meaning it's an invalid CR_
pattern PZeroBad :: forall t a. (Num a, Eq a) => [(a, t)]
pattern PZeroBad <- ((0,_):_) -- MUST check after PZero

-- No longer necessary
-- pattern PNotIntegral :: forall a t. (Num a, Ord a) => [(t, a)]
-- pattern PNotIntegral <- ( (_, compare 0 -> GT):_ ) -- negative exponent in the 2nd member of pair

-- | Pattern to match a non-positive CR_
pattern PNotPos :: forall t a. (Num a, Ord a) => [(a, t)]
pattern PNotPos      <- ( (compare 1 -> GT, _):_ ) -- first term is 0, -1 and so not positive

-- | Pattern to match a negative number
pattern PIntNeg :: forall a. (Num a, Ord a) => a
pattern PIntNeg  <- (compare 0 -> GT)

-- | Pattern to match a positive number
pattern PIntPos :: forall a. (Num a, Ord a) => a
pattern PIntPos  <- (compare 0 -> LT)

-- | Pattern to match a non-positive number
pattern PIntNPos :: forall a. (Num a, Ord a) => a
pattern PIntNPos <- (compare 1 -> GT)

-- | Canonical values for a few special numbers
creN1, cre0 :: CanonElement_
creN1 = (-1,1)
cre0  = (0,1)

crN1, cr0, cr1 :: CanonRep_

-- | Canon rep for -1 
crN1  = [creN1]

-- | Canon rep for 0
cr0   = [cre0]

-- | Canon rep for 1 
cr1   = []        -- Yes, a canonical "1" is just an empty list.

-- | Pattern for a negative CR_
pattern PNeg :: forall a a1. (Num a, Num a1, Eq a, Eq a1) => [(a1, a)]
pattern PNeg <- ((-1,1):_) 

crNegative, crPositive :: CR_ -> Bool

-- | Check if a CR_ is negative.
crNegative PNeg = True
crNegative _    = False

-- | Check if a CR_ is positive.
crPositive PZero = False
crPositive x     = not $ crNegative x

-- | Canon rep validity check:  
--   The 2nd param checks the validity of the base, the 3rd of the exponent.
--   The base pred should be some kind of prime or psuedo-prime test unless you knew for 
--   certain the bases are prime.  There are two choices for the exp pred: 
--   positiveOnly (True) or nonZero  (False) (which allows for "rationals").  
crValid :: CR_ -> (Integer -> Bool) -> Bool -> Bool
crValid POne     _  _          = True
crValid PZero    _  _          = True
crValid PZeroBad _  _          = False
crValid c        bp ef 
                | crNegative c = f (tail c) 1
                | otherwise    = f c        1
                                 where f POne         _ = True
                                       f ((cp,ce):cs) n | cp <= n || not (expPred ef ce) || not (bp cp) = False
                                                        | otherwise                                     = f cs cp
                                       f _            _ = error "Logic error in crValid'.  Issue with pattern matching?"
                                       expPred b e      = if b then (e > 0) else (e /= 0)

crValidIntegral, crValidRational :: CR_ -> Bool
crValidIntegralViaUserFunc, crValidRationalViaUserFunc :: CR_ -> (Integer -> Bool) -> Bool

-- | Checks if a CR_ represents an integral number.
crValidIntegral n = crValid n isPrime True

-- | Checks if a CR_ is Integral and valid per user-supplied criterion.
crValidIntegralViaUserFunc  n f = crValid n f True

-- | Checks if a CR_ is represents a rational number (inclusive of integral numbers).
crValidRational n = crValid n isPrime False

-- | Checks if a CR_ is Rational and valid per user-supplied criterion.
crValidRationalViaUserFunc  n f = crValid n f False

crFromInteger, crFromI :: Integer -> (CR_, Bool)

-- | Factor the number to convert it to a canonical rep.  This is of course can be extremely expensive.
--   (This now also returns a flag indicating True if the number was completely factored.)
crFromInteger n | n == 0    = (cr0,    True)
                | n == 1    = (cr1,    True)
                | n == -1   = (crN1,   True)
                | n < 0     = (creN1:cr, ff)  -- in case arithmoi excludes -1 as a factor in the future
                | otherwise = (cr,       ff) 
                where cr                 = crSort cr'
                      -- the prime factors must be in ascending order
                      (cr', ff)          = factorize (abs n) -- ToDo: pass to fcn

crSort :: CR_ -> CR_ 
crSort = sortBy prd 
         where prd (p1, _) (p2, _) | p1 < p2   = LT
                                   | otherwise = GT

-- Note: if crFactCutoff is <= 0, complete factorization is attempted 
-- and all of the cutoff / spFactor logic is not used.
crFactCutoff, crTrialDivCutoff, crSmallFactCutoff, crTrialDivCutoffSq :: Integer
crFactCutoff = (10 :: Integer) ^ (80 :: Int) -- Note: if this is <= 0, complete factorization is attempted
crTrialDivCutoff      = 100000
crSmallFactCutoff     = 10000000 -- use this higher cutoff if the number is beyond the factorization cutoff
crTrialDivCutoffSq    = crTrialDivCutoff * crTrialDivCutoff 

-- factorize and deftStdGenFact were adapted from arithmoi
factorize :: Integer -> ([(Integer,Integer)], Bool)
factorize n = (map (\(p,e) -> (p, toInteger e)) f, b)
              where (f, b) = if crFactCutoff > 0 
                             then defStdGenFact (mkStdGen $ fromInteger n `xor` 0xdeadbeef)
                             else (factorise' n, True) -- call underlying routine from arithmoi
                    defStdGenFact sg 
                           = let (sfs,mb) = smallFactors (if n <= crFactCutoff 
                                            then crTrialDivCutoff 
                                            else crSmallFactCutoff) n
                             in (sfs ++ case mb of
                                        Nothing -> []
                                        Just m  -> if m > crFactCutoff 
                                                   then [(m, 1)]
                                                   else stdGenFactorisation (Just crTrialDivCutoffSq) sg Nothing m,
                                 case mb of
                                 Nothing -> True 
                                 Just m  -> m < crFactCutoff || isPrime m -- if less, do a complete factorization
                                )

-- | Shorthand for crFromInteger function
crFromI n = crFromInteger n 

crToInteger, crToI :: CR_ -> Integer

-- | Convert a canon rep back to an Integer.
crToInteger POne                  = 1
crToInteger PZero                 = 0
crToInteger c | (head c) == creN1 = -1 * (crToInteger $ tail c)    -- negative number
              | otherwise         = product $ map (\(x,y) -> x ^ y) c

-- | Alias to crToInteger.
crToI = crToInteger

-- | Compute the modulus between a CR_ and Integer and return an Integer.
crModI :: CR_ -> Integer -> Integer
crModI _     0       = error "Divide by zero error when computing n mod 0"
crModI _     1       = 0
crModI _     (-1)    = 0
crModI POne  PIntPos = 1
crModI PZero _       = 0
crModI c     m | cn && mn         = -1 * crModI (crAbs c) am
               | (cn && not mn) ||
                 (mn && not cn) = (signum m) * (am - f (crAbs c) am)
               | otherwise        = f c m
               where cn           = crNegative c
                     mn           = m < 0
                     am           = abs m
                     f c' m'      = mod (product $ map (\(x,y) -> if (mod x m' == 0) then 0 else (pmI x (mmt y) m')) c') m'
                     mmt e        | e >= 1    = mod e $ totient m -- optimization
                                  | otherwise =  error "Negative exponents are not allowed in crModI" 

-- | Compute modulus with all CR_ parameters.  This wraps crModI.
crMod :: CR_ -> CR_ -> (CR_, Bool)
crMod c m = crFromI $ crModI c (crToI m)
           
-- | Display a Canon Element (as either p^e or p).
ceShow :: CanonElement_ -> String
ceShow (p,e) = show p ++ if e == 1 then "" 
                                   else "^" ++ (if e < 0 then "(" ++ se ++ ")" else se)
               where se = show e

crShow, crShowRational :: CR_ -> String

-- | Display a canonical representation.
crShow POne = show (1 :: Integer)
crShow x    | null (tail x) = ceShow $ head x
            | otherwise     = concat $ intersperse " * " $ map ceShow x 

-- | Display a CR_ rationally, as a quotient of its numerator and denominator.
crShowRational c | d == cr1  = crShow n
                 | otherwise = crShow n ++ "\n/\n" ++ crShow d
                 where (n, d) = crSplit c  

crNegate, crAbs, crSignum :: CR_ -> CR_

-- | Negate a CR_.
crNegate PZero            = cr0
crNegate x | crNegative x = tail x 
           | otherwise    = creN1 : x 

-- | Take the absolute value of a CR_.
crAbs x | crNegative x = tail x
        | otherwise    = x

-- | Compute the signum and return as CR_.
crSignum PZero            = cr0;
crSignum x | crNegative x = crN1
           | otherwise    = cr1

-- | CR_ Compare Function       
crCmp :: CR_ -> CR_ -> Ordering
crCmp POne y    = crCmp1 y True
crCmp x    POne = crCmp1 x False
crCmp x y | x == y    = EQ            
          | xN && yN  = crCmp (tail y) (tail x)
          | xN        = LT
          | yN        = GT         
          | eqZero x  = LT
          | eqZero y  = GT
          | otherwise = case compare (crLogDouble x) (crLogDouble y) of
                          EQ  -> compare (crLog x) (crLog y) -- We have to break out the big guns, both evaluate to infinity
                          cmp -> cmp
          where xN           = crNegative x
                yN           = crNegative y  
                eqZero PZero = True;
                eqZero _     = False

-- Internal: Compare when either term is 1.
crCmp1 :: CR_ -> Bool -> Ordering
crCmp1 PNeg  b = if b then GT else LT
crCmp1 PZero b = if b then GT else LT
crCmp1 _     b = if b then LT else GT 

crMin, crMax :: CR_ -> CR_ -> CR_

-- | Min function
crMin x y = case crCmp x y of
              GT -> y
              _  -> x

-- | Max functon                 
crMax x y = case crCmp x y of
              LT -> y
              _  -> x                                         
                 
divisionError, divByZeroError, zeroDivZeroError, negativeLogError :: String
divisionError    = "For this function, the dividend must be a multiple of the divisor." 
divByZeroError   = "Division by zero error!"
zeroDivZeroError = "Zero divided by zero is undefined!"
negativeLogError = "The log of a negative number is undefined!"

-- | Strict division: Generate error if exact division is not possible.
crDivStrict :: CR_ -> CR_ -> CR_
crDivStrict x y = case crDiv x y of
                    Left errorMsg  -> error errorMsg
                    Right quotient -> quotient

-- | Attempt to take the quotient.
crDiv :: CR_ -> CR_ -> Either String CR_
crDiv PZero PZero = Left zeroDivZeroError 
crDiv PZero _     = Right cr0
crDiv _     PZero = Left divByZeroError
crDiv x'    y'     = f x' y'
                     where -- call this after handling zeroes above, then division just occurs within here
                           f x     POne  = Right x
                           f POne  _     = Left divisionError
                           f x     y     | crNegative y = f (crNegate x) (crAbs y)
                                         | otherwise    = case compare xp yp of      
                                                            LT             -> case f xs y of
                                                                                Left _  -> Left divisionError
                                                                                Right r -> Right ((xp, xe):r)
                                                            EQ| (xe > ye)  -> case f xs ys of
                                                                                Left _  -> Left divisionError
                                                                                Right r -> Right ((xp,xe-ye):r)
                                                            EQ| (xe == ye) -> f xs ys
                                                            _              -> Left divisionError
                                         where ((xp,xe):xs) = x
                                               ((yp,ye):ys) = y                      

crMult, crDivRational, crGCD, crLCM :: CR_ -> CR_ -> CR_

-- | Multiply two crs by summing the exponents for each prime.
crMult PZero _     = cr0
crMult _     PZero = cr0
crMult POne  y     = y
crMult x     POne  = x
crMult x     y     = case compare xp yp of
                       LT -> xh : crMult xs y
                       -- cancel double negs or expnts adding to zero
                       EQ -> if crNegative x || expSum == 0 then r
                                                            else (xp, expSum) : r
                             where r = crMult xs ys
                       GT -> yh : crMult x ys
                     where (xh@(xp,xe):xs) = x
                           (yh@(yp,ye):ys) = y
                           expSum          = xe + ye

-- | Division of rationals is equivalent to multiplying with negated exponents.
crDivRational x y = crMult (crRecip y) x -- multiply by the reciprocal

-- | For the GCD (Greatest Common Divisor), take the lesser of two exponents for each prime encountered.
crGCD PZero y     = y
crGCD x     PZero = x
crGCD x     y     | crNegative x || crNegative y       = f (crAbs x) (crAbs y)
                  | crFactCutoff > 0 &&
                    ((spIncompFact x && spUnsmooth y) || -- either has an imcomplete factorization and the other
                     (spIncompFact y && spUnsmooth x)) = f spx spy -- in case of unfactored bits
                  | otherwise                          = f x   y
                  where f POne _    = cr1
                        f _    POne = cr1
                        f x'   y'   = case compare xp yp of
                                        LT -> f xs y'
                                        EQ -> (xp, min xe ye) : f xs ys                    
                                        GT -> f x' ys
                                      where ((xp,xe):xs) = x'
                                            ((yp,ye):ys) = y'    
                        (spx, spy)  = spFactor x y

-- | For the LCM (Least Common Multiple), take the max of two exponents for each prime encountered.
crLCM PZero _     = cr0
crLCM _     PZero = cr0 
crLCM x     y     | crNegative x || crNegative y       = f (crAbs x) (crAbs y)
                  | crFactCutoff > 0 &&
                    ((spIncompFact x && spUnsmooth y) || -- either has an imcomplete factorization and the other
                     (spIncompFact y && spUnsmooth x)) = f spx spy -- in case of unfactored bits 
                  | otherwise                          = f x   y
                  where f POne y'   = y'
                        f x'   POne = x'
                        f x'   y'   = case compare xp yp of
                                        LT -> xh : f xs y'
                                        EQ -> (xp, max xe ye) : f xs ys
                                        GT -> yh : f x' ys
                                      where (xh@(xp,xe):xs) = x'
                                            (yh@(yp,ye):ys) = y' 
                        (spx, spy)  = spFactor x y

-- special factor: This covers the case where we have unfactored large components but on comparison with another
-- cr we can see that the component can be reduced.  We partition the cr into 
-- three pieces: small factor cutoff, prime, composite (implying it's > factor. cutoff)
spFactor :: CR_ -> CR_ -> (CR_, CR_)
spFactor x y = (sx ++ (grp $ crSort $ px ++ spF cx (py ++ cy)), 
                sy ++ (grp $ crSort $ py ++ spF cy (px ++ cx)) )  
               where spl n           = (s, p, c)
                                       where (s, r) = partition spSmooth n
                                             (p, c) = partition (\ce -> not $ spBigComposite ce) r 
                     (sx, px, cx)    = spl x
                     (sy, py, cy)    = spl y                  
                     grp (n:ns)      = g' n ns
                     grp _           = error "The list to be grouped in spFactor must have at least one element"
                     g' (b,e) (r:rs) = if b == b' then g' (b, e + e') rs  -- group by common base on sorted list
                                                  else (b,e):g' (b', e') rs
                                       where (b', e') = r
                     g' ce    _      = [ce]
                      
                     -- take each entry in f and compute the gcd.  ToDo: replace with fold
                     spF n (f:fs)    = spF (concat $ map (proc f) n) fs -- this is quadratic but likely with very short lists
                                       where proc (pf, _) (pn, en) = if g == 1 || g == pn then [(pn, en)] 
                                                                     else [(g, en), (div pn g, en)]
                                                                     where g = gcd pn pf
                     spF n _         = n

-- Predicates used for special cases of GCD and LCM
spUnsmooth, spIncompFact :: CR_ -> Bool
spUnsmooth    = any (\ce -> not $ spSmooth ce)
spIncompFact  = any spBigComposite

spBigComposite, spSmooth :: CanonElement_ -> Bool
spSmooth    (b,_) = b <= crSmallFactCutoff
spBigComposite (b,_) = b > crFactCutoff && (not $ isPrime b)

-- | Take the reciprocal by raising a CR to the -1 power (equivalent to multiplying exponents by -1).
crRecip :: CR_ -> CR_
crRecip x = crExp x (-1) True

rootError :: CR_ -> Integer -> String
rootError c r = "crRoot: All exponents must be multiples of " ++ (show r) ++ ".  Not so with " ++ (show c)

-- | Attempt to compute a particular root of a CR_.
crRoot :: CR_ -> Integer -> CR_ 
crRoot _    PIntNeg = error "r-th roots are not allowed when r <= 0" 
crRoot POne _       = cr1   
crRoot c    r
  | crNegative c = if mod r 2 == 1  then creN1 : crRoot (crAbs c) r 
                                    else error "Imaginary numbers not allowed: Even root of negative number requested"
  | otherwise    = if mod ce r == 0 then (cp, div ce r) : crRoot cs r
                                    else  error $ rootError c r
  where ((cp,ce):cs) = c                             

-- | Takes the maximum root of the number.  Generally, the abs value would be passed to the function.
crMaxRoot :: CR_ -> Integer
crMaxRoot c = foldr (\x -> flip gcd $ snd x) 0 c

-- | Exponentiation.  Note: this does allow for negative exponentiation if bool flag is True.
crExp :: CR_ -> Integer -> Bool -> CR_
crExp _     PIntNeg  False = error "Per param flag, negative exponentiation is not allowed here."
crExp PZero PIntNPos _     = error "0^e where e <= 0 is either undefined or illegal"
crExp PZero _        _     = cr0
crExp POne  _        _     = cr1
crExp _     0        _     = cr1
crExp c     em       _     = ce c 
                             where ce c' | crNegative c' = if mod em 2 == 1 then creN1 : absTail
                                                                            else absTail
                                         | otherwise     = map (\(p,e) -> (p, e * em)) c'
                                                           where absTail  = ce $ crAbs c'

-- | This log function is much more expensive but accurate.  You have an "infinity" problem potentially with crLogDouble.
crLog :: CR_ -> Rational
crLog PNeg = error negativeLogError
crLog c    = sum $ map (\(p,e) -> (toRational $ logDouble $ fromIntegral p) * (fromIntegral e)) c
             where logDouble :: Double -> Double
                   logDouble n = log n

-- | Returns log of CR_ as a Double.
crLogDouble :: CR_ -> Double
crLogDouble PNeg  = error negativeLogError
crLogDouble c     = sum $ map (\(x,y) -> log (fromIntegral x) * fromIntegral y) c
    
crNumer, crDenom, crRadical :: CR_ -> CR_
    
-- | Compute numerator (by filtering on positive exponents).
crNumer c = filter (\(_,e) -> e > 0) c

-- | Compute denominator. (Grab the primes with negative exponents and then flip the sign of the exponents.)
crDenom c = map (\(p,e) -> (p, (-1) * e)) $ filter (\(_,e) -> e < 0) c

-- | Check if a CR_ represents an integer.
crIntegral :: CR_ -> Bool
crIntegral x = all (\(_,e) -> e > 0) x -- all exponents must be positive

-- | Split a CR_ into its Numerator and Denominator.
crSplit :: CR_ -> (CR_, CR_)
crSplit c = (crNumer c, crDenom c)

-- | Convert a CR_ to a Rational number.
crToRational :: CR_ -> Rational
crToRational c = (crToI $ crNumer c) :% (crToI $ crDenom c)

-- | Compute the Radical of a CR_ (http://en.wikipedia.org/wiki/Radical_of_an_integer).
--   Its the product of the unique primes in its factorization.
crRadical n = map (\(p,_) -> (p, 1)) n 

-- | The Op(eration) is intended to be plus or minus.
integerApply :: (Integer -> Integer -> Integer) -> CR_ -> CR_ -> Integer
integerApply op x y  = op (crToI x) (crToI y)

-- | Calls integerApply and returns a CR_.
crSimpleApply :: (Integer -> Integer -> Integer) -> CR_ -> CR_ -> (CR_, Bool)
crSimpleApply op x y = crFromI $ integerApply op x y

{- No longer needed.  Different criteria used now
pattern PPrime :: forall a a1. (Eq a, Num a, Num a1, Ord a1) => [(a1, a)]
pattern PPrime <- [(compare 1 -> LT, 1)] -- of form x^1 where x > 1 -- prime (assumption p has already been verified to be prime)
-}

crPrime, crHasSquare :: CR_ -> Bool

-- | Check if a number is a prime.
crPrime cr | length cr > 1 || null cr = False
           | e == 1 && b > 1 && (crFactCutoff == 0 || b <= crFactCutoff || (b > crFactCutoff && isPrime b))
                                      = True
           | otherwise                = False
           where (b,e) = head cr

-- | Check if a number has a squared (or higher) factor.
crHasSquare    = any (\(_,e) -> e > 1) 
                    
-- | Divisor functions should be called with integral CRs (no negative exponents).
crNumDivisors, crTau, crTotient, crPhi  :: CR_ -> Integer

crNumDivisors cr = product $ map (\(_,e) -> 1 + e) cr -- does return 1 for cr1
crTau            = crNumDivisors
crTotient     cr = product $ map (\(p,e) -> (p-1) * p^(e-1)) cr
crPhi            = crTotient

-- | Compute the nth divisor. This is zero based. 
--   Note: This is deterministic but it's not ordered by the value of the divisor.
crNthDivisor :: Integer -> CR_ -> CR_
crNthDivisor 0 _    = cr1
crNthDivisor _ POne =  error "Bad div num requested"
crNthDivisor n c    | m == 0    = r
                    | otherwise = (cb,m) : r
                    where (cb,ce):cs = c
                          r          = crNthDivisor (div n (ce + 1)) cs -- first param is the next n
                          m          = mod n (ce + 1)          

-- | Consider this to be the inverse of the crNthDivisor function.
crWhichDivisor :: CR_ -> CR_ -> Integer
crWhichDivisor d c | crPositive d == False ||
                     crPositive c == False = error "crWhichDivisor: Both params must be positive"
                   | otherwise             = f d c 
                                             where f POne _    = 0
                                                   f _    POne = error "Not a valid divisor"  
                                                   f d'   c' | dp < cp  || 
                                                               (dp == cp && de > ce) = error "Not a valid divisor"
                                                             | dp == cp              = de + (ce + 1) * (f ds cs)
                                                             | otherwise             = (ce + 1) * (f d  cs)
                                                                                       where ((dp, de):ds)  = d'
                                                                                             ((cp, ce):cs)  = c'   

-- | Efficiently compute all of the divisors based on the canonical representation.
crDivisors :: CR_ -> [CR_]
crDivisors c = foldr1 cartProd $ map pwrDivList c
               where cartProd xs ys   = [x ++ y | y <- ys, x <- xs]
                     pwrDivList (n,e) = [if y == 0 then cr1 else [(n,y)] | y <- [0..(fromInteger e)]]

-- | Like the crDivisors function, except that it returns pairs of the CR_ and resp. numeric value, instead of just the CR_.
crDivsPlus :: CR_ -> [(CR_, Integer)]
crDivsPlus c = foldr1 cartProd (map pwrDivList c)
               where cartProd xs ys   = [(xl ++ yl, xv * yv) | (yl, yv) <- ys, (xl, xv) <- xs] 
                     pwrDivList (e,n) = map tr $ pwrList e n
                     powers x         = 1 : map (* x) (powers x)
                     pwrList n e      = [(n,y) | y <- zip [0..e] (take (e'+1) $ powers n)] 
                                        where e' = fromInteger e
                     tr (a,b)         = (if fb == 0 then cr1 else [(a, fb)], sb) -- this just transforms the data structure
                                        where (fb, sb) = b

-- | Check if underlying rep is simplified
crSimplified :: CR_ -> Bool
crSimplified POne  = True
crSimplified PZero = True
crSimplified PN1   = True
crSimplified c     = crPrime c

-- | Compute totient: Logic from deprecated arithmoi function used here.
totient :: Integer -> Integer
totient n
    | n < 1       = error "Totient only defined for positive numbers"
    | n == 1      = 1
    | ff == False = error "Totient not computable.  The number could not be totally factored based on the factorizaton cutoff."
    | otherwise   = product $ map (\(p,e) -> (p-1) * p ^ (e-1)) cr 
    where (cr, ff) = factorize n -- ToDo: pass the param to function

-- | powerModInteger adapted here from deprecated arithmoi function.
pmI :: Integer -> Integer -> Integer -> Integer
pmI x p m | x < 1 || p < 0 || m < 1 = error "pmI (powerModInteger) requires: x >= 1 &&, p >= 0, m >= 1"
          | otherwise               = f p 1 (mod x m) -- last is the running exp of mod initially
          where f q w e | w == 0 || q == 0 = w
                        | q == 1           = mod (w*e) m
                        | otherwise        = f (div q 2) nw (mod (e*e) m) 
                                               where nw | mod q 2 == 1 = mod (w*e) m 
                                                        | otherwise    = w

