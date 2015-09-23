{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns    #-}
{-# LANGUAGE ScopedTypeVariables #-}

module CanonInternals (
  CanonRep_,       CR_,
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
  crOdd,
  crValid,
  crMod, crModI,
  
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
    
  pattern PZero,
  pattern PZeroBad,
  pattern POne,
  pattern PNeg,
  pattern PNotPos,
  pattern PN1,
  
  pattern PIntNeg,
  pattern PIntNPos,
  pattern PIntPos
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
   Numbers:          A set of (p,e) pairs where the p's are prime and in ascending order. 
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

import Data.List (intersperse)
import Math.NumberTheory.Primes.Factorisation (factorise, totient)
import Math.NumberTheory.Primes.Testing (isPrime)
import Math.NumberTheory.Moduli(powerModInteger)
import GHC.Real ( Ratio(..) )

-------------------------------------------
type CanonElement_ = (Integer,Integer)
type CanonRep_     = [CanonElement_]
type CR_           = CanonRep_

-------------------------------------------
pattern POne      = []
pattern PZero     = [(0,1)]
pattern PN1       = [(0,1)]
pattern PZeroBad <- ((0,_):_) -- MUST check after PZero


pattern PNotIntegral <- ( (_, compare 0 -> GT):_ ) -- negative exponent in the 2nd member of pair
pattern PNotPos      <- ( (compare 1 -> GT, _):_ ) -- first term is 0, -1 and so not positive

pattern PIntNeg  <- (compare 0 -> GT)
pattern PIntPos  <- (compare 0 -> LT)
pattern PIntNPos <- (compare 1 -> GT)

crIsZero :: CR_ -> Bool
crIsZero PZero = True;
crIsZero _     = False

-------------------------------------------
-- canonical values for a few special numbers
creN1 :: CanonElement_
creN1 = (-1,1)

crN1 :: CanonRep_
crN1  = [creN1]

cre0 :: CanonElement_
cre0  = (0,1)

cr0 :: CanonRep_
cr0   = [cre0]

cr1 :: CanonRep_
cr1   = []        -- Yes, a canonical "1" is just an empty list.

-------------------------------------------
if' :: Bool -> a -> a -> a
if' True  x _ = x
if' False _ y = y

-------------------------------------------
pattern PNeg <- ((-1,1):_) 

crNegative :: CR_ -> Bool
crNegative PNeg = True
crNegative _    = False

crPositive :: CR_ -> Bool
crPositive PNeg  = False
crPositive PZero = False
crPositive _     = True

-- add entries to allow for preds

{- The 2nd param checks the validity of the base, the 3rd of the exponent.
   The base pred should be some kind of prime or psuedo-prime test unless you knew for 
   certain the bases are prime.  There are two choices for the exp pred: 
   positiveOnly (True) or nonZero  (False) (which allows for "rationals").  
-}
crValid :: CR_ -> (Integer -> Bool) -> Bool -> Bool
crValid POne     _  _          = True
crValid PZero    _  _          = True
crValid PZeroBad _  _          = False
crValid c        bp ef 
                | crNegative c = crValid' (tail c) bp ef 1
                | otherwise    = crValid' c        bp ef 1

crValid' :: CR_ -> (Integer -> Bool) -> Bool -> Integer -> Bool
crValid' POne   _  _  _ = True
crValid' (c:cs) bp ef n = if (cp <= n || not (expPred ef ce) || not (bp cp)) 
                             then False 
                             else (crValid' cs bp ef cp)
                          where (cp, ce)    = c
                                expPred b e = if' (b == True) (e > 0) $ (e /= 0)
crValid' _      _  _  _ = error "Logic error in crValid'.  Issue with pattern matching?"

crValidIntegral :: CR_ -> Bool
crValidIntegral n = crValid n isPrime True

crValidIntegralViaUserFunc :: CR_ -> (Integer -> Bool) -> Bool
crValidIntegralViaUserFunc  n f = crValid n f True

crValidRational :: CR_ -> Bool
crValidRational n = crValid n isPrime False

crValidRationalViaUserFunc :: CR_ -> (Integer -> Bool) -> Bool
crValidRationalViaUserFunc  n f = crValid n f False

-- basically, we have to factor the number to convert it to a canonical rep
crFromInteger :: Integer -> CR_
crFromInteger 0 = cr0
crFromInteger n = map (\t -> (fst t, toInteger (snd t))) $ factorise n

crFromI :: Integer -> CR_
crFromI n = crFromInteger n 

crToInteger :: CR_ -> Integer
crToInteger POne                  = 1
crToInteger PZero                 = 0
crToInteger c | (head c) == creN1 = -1 * (crToInteger (tail c))    -- negative number
              | otherwise         = product $ map (\x -> (fst x) ^ (snd x)) c

crToI :: CR_ -> Integer
crToI = crToInteger

crModI :: CR_ -> Integer -> Integer
crModI _     0       = error "Divide by zero error when computing n mod 0"
crModI _     1       = 0
crModI _     (-1)    = 0
crModI POne  PIntPos = 1
crModI PZero _       = 0
crModI c     m | cn && mn         = -1 * crModI (crAbs c) (abs m)
               | (cn && (not mn)) ||
                 ((not cn) && mn) = (signum m) * ( (abs m) - (crModI' (crAbs c) (abs m)) )
               | otherwise        = crModI' c m
               where cn           = crNegative c
                     mn           = m < 0

crModI' :: CR_ -> Integer -> Integer                     
crModI' c m = mod (product $ map (\x -> powerModInteger (mod (fst x) m) (mmt $ snd x) m) c) m
             where tm    = totient m
                   mmt e = if (e >= 1) then (mod e tm) -- optimization
                                       else (error "Negative exponents are not allowed in crModI'") 
crMod :: CR_ -> CR_ -> CR_
crMod c m = crFromI $ crModI c (crToI m)
           
---------------------------------------------
-- different show utilities
ceShow :: CanonElement_ -> String
ceShow ce = show (fst ce) ++ (if' (snd ce == 1) "" $ "^" ++ show (snd ce))

crShow :: CR_ -> Bool -> String
crShow POne _  = show (1 :: Integer)
crShow x    wp = if' (null (tail x)) (ceShow (head x)) $ 
                                     if' wp ( "(" ++ concatedList ++ ")") $ concatedList
                 where concatedList = concat $ intersperse " * " (map ceShow x)

---------------------------------------------

crShowRational :: CR_ -> String
crShowRational c = if' (d == cr1) (crShow n False) $ 
                                  (crShow n True) ++ " / " ++ (crShow d True)
                   where (n, d) = crSplit c  

crNegate :: CR_ -> CR_
crNegate PZero            = cr0
crNegate x | crNegative x = tail x 
           | otherwise    = creN1 : x 

crAbs :: CR_ -> CR_
crAbs x | crNegative x = tail x
        | otherwise    = x

crOdd :: CR_ -> Bool
crOdd PZero = False
crOdd POne  = True
crOdd c     | crNegative c = crOdd (crAbs c)
            | otherwise    = cp == 2 
              where (cp,_):_ = c

crSignum :: CR_ -> CR_
crSignum PZero            = cr0;
crSignum x | crNegative x = crN1
           | otherwise    = cr1
       
crCmp :: CR_ -> CR_ -> Ordering
crCmp POne y    = crCmp' y True
crCmp x    POne = crCmp' x False
crCmp x y | x == y     = EQ            
          | xN && yN   = crCmp (tail y) (tail x)
          | xN         = LT
          | yN         = GT         
          | crIsZero x = LT
          | crIsZero y = GT
          | otherwise  = case compare (crLogDouble x) (crLogDouble y) of
                         EQ  -> compare (crLog'' x) (crLog'' y) -- we have to break out the big guns, both evaluate to infinity
                         cmp -> cmp
                         
          where xN          = crNegative x
                yN          = crNegative y  

crCmp' :: CR_ -> Bool -> Ordering
crCmp' PNeg  b = if' b GT $ LT
crCmp' PZero b = if' b GT $ LT
crCmp' _     b = if' b LT $ GT 
     
crMin :: CR_ -> CR_ -> CR_
crMin x y = case crCmp x y of
                 GT -> y
                 _  -> x
                 
crMax :: CR_ -> CR_ -> CR_
crMax x y = case crCmp x y of
                 LT -> y
                 _  -> x                                         
                 
------------------------------------------------
divisionError :: String
divisionError = "For this function, the dividend must be a multiple of the divisor." 

divByZeroError :: String
divByZeroError = "Division by zero error!"

zeroDivZeroError :: String
zeroDivZeroError = "Zero divided by zero is undefined!"

crDivStrict :: CR_ -> CR_ -> CR_
crDivStrict x y = case (crDiv x y) of
                       Left errorMsg -> error errorMsg
                       Right results -> results

crDiv :: CR_ -> CR_ -> Either String CR_
crDiv PZero PZero = Left zeroDivZeroError 
crDiv PZero _     = Right cr0
crDiv _     PZero = Left divByZeroError
crDiv x     y     = crDiv' x y

-- call this after handling zeroes above
crDiv' :: CR_ -> CR_ -> Either String CR_
crDiv' x     POne  = Right x
crDiv' POne  _     = Left divisionError
crDiv' x y 
  | crNegative y = crDiv' (crNegate x) (crAbs y)
  | otherwise    = case compare xp yp of      
                   LT             -> case (crDiv' xs y) of
                                       Left _        -> Left divisionError
                                       Right results -> Right ((xp, xe) : results)
                   EQ| (xe > ye)  -> case (crDiv' xs ys) of
                                       Left _        -> Left divisionError
                                       Right results -> Right ((xp, xe - ye) : results)
                   EQ| (xe == ye) -> crDiv xs ys
                   _              -> Left divisionError
                         
   where ((xp,xe):xs) = x
         ((yp,ye):ys) = y                      

-- division of rationals is equivalent to multiplying with negated exponents
crDivRational :: CR_ -> CR_ -> CR_
crDivRational x y = crMult (crRecip y) x -- multiply by the reciprocal

crRecip :: CR_ -> CR_
crRecip x = crExp x (-1) True

------------------------------------------------

crGCD :: CR_ -> CR_ -> CR_
crGCD PZero y     = y
crGCD x     PZero = x
crGCD x     y     | crNegative x || 
                    crNegative y = crGCD' (crAbs x) (crAbs y)
                  | otherwise    = crGCD' x y

crGCD' :: CR_ -> CR_ -> CR_
crGCD' POne _    = cr1
crGCD' _    POne = cr1
crGCD' x    y    = case compare xp yp of
                        LT -> crGCD' xs y
                        EQ -> (xp, min xe ye) : crGCD' xs ys                    
                        GT -> crGCD' x ys
                   where ((xp,xe):xs) = x
                         ((yp,ye):ys) = y    

crLCM :: CR_ -> CR_ -> CR_
crLCM PZero y     = y
crLCM x     PZero = x
crLCM x     y     | crNegative x || 
                    crNegative y = crLCM' (crAbs x) (crAbs y)
                  | otherwise    = crLCM' x y
           
crLCM' :: CR_ -> CR_ -> CR_   
crLCM' POne y    = y
crLCM' x    POne = x        
crLCM' x    y    = case compare xp yp of
                               LT -> xh : crLCM' xs y
                               EQ -> (xp, max xe ye) : crLCM' xs ys
                               GT -> yh : crLCM' x ys
                   where (xh:xs)  = x
                         (yh:ys)  = y  
                         (xp, xe) = xh
                         (yp, ye) = yh

crMult :: CR_ -> CR_ -> CR_                                                    
--crMult x y | trace ("crMult trace: Getting " ++ (show x) ++ " and " ++ (show y)) False = undefined
crMult PZero _     = cr0
crMult _     PZero = cr0
crMult POne  y     = y
crMult x     POne  = x
crMult x     y     = case compare xp yp of
                          LT -> xh : crMult xs y
                          -- cancel double negs or expnts adding to zero
                          EQ -> if' ((crNegative x) || expSum == 0) 
                                (crMult xs ys) $ ((xp, expSum) : crMult xs ys) 
                          GT -> yh : crMult x ys
                     where (xh:xs)  = x
                           (yh:ys)  = y  
                           (xp, xe) = xh
                           (yp, ye) = yh                           
                           expSum   = xe + ye

-- to do: Add Either
--crRoot c r | trace ("crRoot trace: Getting " ++ (show r) ++ "-th root of " ++ (show c)) False = undefined
rootError :: CR_ -> Integer -> String
rootError c r = "crRoot: All exponents must be multiples of " ++ (show r) ++ ".  Not so with " ++ (show c)

crRoot :: CR_ -> Integer -> CR_ 
crRoot _    PIntNeg = error "r-th roots are not allowed when r <= 0" 
crRoot POne _       = cr1   
crRoot c    r
  | crNegative c    = if' ((mod r 2) == 1) (creN1 : crRoot (crAbs c) r) 
                      $ error "Imaginary numbers not allowed: Even root of negative number requested"                           
  | otherwise       = if' (mod ce r == 0) ((cp, div ce r) : crRoot cs r)
                      $ error $ rootError c r
  where ((cp,ce):cs) = c                             

-- FIX? Does this only return an odd number if the number is negative
crMaxRoot :: CR_ -> Integer
crMaxRoot c = foldr (\x -> flip gcd $ snd x) 0 $ crAbs c

-- this does allow for negative exponentiation if bool flag is True
crExp :: CR_ -> Integer -> Bool -> CR_
crExp _     PIntNeg  False = error "Per param flag, negative exponentiation is not allowed here."
crExp PZero PIntNPos _     = error "0^e where e <= 0 is either undefined or illegal"
crExp PZero _        _     = cr0
crExp POne  _        _     = cr1
crExp _     0        _     = cr1
crExp c     e        _     = crExp' c e

crExp' :: CR_ -> Integer -> CR_ 
crExp' c e | crNegative c = if' ((mod e 2) == 1) (creN1 : absTail) $ absTail
           | otherwise    = map (\x -> ((fst x), e * (snd x))) c
           where absTail  = crExp' (crAbs c) e

negativeLogError :: String
negativeLogError = "The log of a negative number is undefined!"
        
crLog :: CR_ -> Rational
crLog PNeg = error negativeLogError
crLog c    = crLog'' c
                        
-- this is much more expensive but accurate.  You have an "infinity" problem potentially with crLogDouble
crLog'' :: CR_ -> Rational              
crLog'' c = sum $ map (\x -> (toRational $ logDouble (fromIntegral $ fst x)) * (fromIntegral $ snd x) ) c
            where logDouble :: Double -> Double
                  logDouble n = log n

crLogDouble :: CR_ -> Double
crLogDouble PNeg  = error negativeLogError
crLogDouble c     = crLogDouble' c

crLogDouble' :: CR_ -> Double
crLogDouble' c = sum $ map (\x -> log (fromIntegral (fst x)) * (fromIntegral (snd x))) c
        
-- for processing "rational" canon reps
crNumer :: CR_ -> CR_
crNumer c = filter (\x -> snd x > 0) c

crDenom :: CR_ -> CR_
crDenom c = map (\t -> (fst t, (-1) * snd t)) $ filter (\x -> snd x < 0) c -- negate negative expnts

crIntegral :: CR_ -> Bool
crIntegral POne         = True
crIntegral PNotIntegral = False
crIntegral (_:cs)       = crIntegral cs
crIntegral _            = error "Logic error when calling crIntegral! Conditions should have been exhaustive"

crSplit :: CR_ -> (CR_, CR_)
crSplit c = (crNumer c, crDenom c)

crToRational :: CR_ -> Rational
crToRational c = (crToI (crNumer c)) :% (crToI (crDenom c))

-- http://en.wikipedia.org/wiki/Radical_of_an_integer
crRadical :: CR_ -> CR_
crRadical n = map (\x -> (fst x, 1)) n 

-- op : intended to be plus or minus
integerApply :: (Integer -> Integer -> Integer) -> CR_ -> CR_ -> Integer
integerApply op x y  = op (crToI x) (crToI y)

crSimpleApply :: (Integer -> Integer -> Integer) -> CR_ -> CR_ -> CR_
crSimpleApply op x y = crFromI $ integerApply op x y

pattern PPrime <- [(compare 1 -> LT, 1)] -- of form x^1 where x > 1 -- prime (assumption p has already been verified to be prime)
crPrime :: CR_ -> Bool
crPrime PPrime = True
crPrime _      = False

pattern PHasSquare <- ( (_, compare 1 -> LT):_ )  -- exp > 1 in the 2nd member of pair
crHasSquare :: CR_ -> Bool
crHasSquare POne       = False;
crHasSquare PHasSquare = True;
crHasSquare (_:xs)     = crHasSquare xs
crHasSquare _          = error "Logic error in hasSquare: Pattern should be exhaustive"

                    
-- =============================================================================                            
-- Divisor functions -- should be called with integral CRs (no negative exponents)

crNumDivisors  :: CR_ -> Integer
crNumDivisors cr  = product $ map (\x -> (snd x+1)) cr -- does return 1 for cr1

crTau :: CR_ -> Integer
crTau = crNumDivisors

crTotient :: CR_ -> Integer
crTotient POne   = 1
crTotient (c:cs) = (fst c -1) * (fst c)^(snd c -1) * crTotient cs
crTotient _      = error "Logic error in crTotient.  Checks above should be exhaustive"

crPhi :: CR_ -> Integer
crPhi = crTotient

-- this is zero based: this is an ordering but it's not by value of the divisor
crNthDivisor :: Integer -> CR_ -> CR_
crNthDivisor 0 _    = cr1
crNthDivisor _ POne =  error "Bad div num requested"
crNthDivisor n c    = if' (m == 0) (crNthDivisor nextn cs) $ (cb,m):(crNthDivisor nextn cs)
                      where (cb,ce):cs = c
                            m          = mod n (ce + 1)          
                            nextn      = div n (ce + 1)

-- consider this an inverse of crNthDivisor above
crWhichDivisor :: CR_ -> CR_ -> Integer
crWhichDivisor d c | (crPositive d == False) ||
                     (crPositive c == False) = error "crWhichDivisor: Both params must be positive"
                   | otherwise               = crWhichDivisor' d c 

crWhichDivisor' :: CR_ -> CR_ -> Integer
crWhichDivisor' POne _    = 0
crWhichDivisor' _    POne = error "Not a valid divisor"  
crWhichDivisor' d    c    
  | dp < cp  || 
    (dp == cp && de > ce) = error "Not a valid divisor"
  | dp == cp              = de + (ce + 1) * (crWhichDivisor' ds cs)
  | otherwise             = (ce + 1) * (crWhichDivisor' d  cs)
   where ((dp, de):ds)  = d
         ((cp, ce):cs)  = c   

crDivisors :: CR_ -> [CR_]
crDivisors c = foldr1 cartProd (map pwrDivList c)
               where cartProd xs ys   = [x ++ y | y <- ys, x <- xs]
                     pwrDivList (n,e) = [if (y == 0) then cr1 else [(n,y)] | y <- [0..(fromInteger e)]]

-- Like the crDivisors function, except that it returns 
-- pairs of the cr and numeric value instead of just the cr
crDivsPlus :: CR_ -> [(CR_, Integer)]
crDivsPlus c = foldr1 cartProd (map pwrDivList c)
               where cartProd xs ys   = [(xl ++ yl, xv * yv) | (yl, yv) <- ys, (xl, xv) <- xs] 
                     pwrDivList (e,n) = map tr (pwrList e n)
                     powers x         = 1 : map (* x) (powers x)
                     pwrList n e      = [(n,y) | y <- (zip [0..e] (take (e'+1) (powers n)))] 
                                        where e' = fromInteger e
                     tr s             = ( (if (fst (snd s) == 0) then cr1 else [(fst s, fst (snd s))]),
                                          snd (snd s))  -- this just transforms the data structure

