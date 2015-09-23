{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns    #-}

module Canon ( 
               makeCanon, makeC,
               canonToGCR, cToGCR,

               cReciprocal,
               cGCD, cLCM, cMod, 
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

--import Debug.Trace (trace) -- remove
import Math.NumberTheory.Primes.Testing (isPrime)
import Math.NumberTheory.Primes.Factorisation (totient)
import Math.NumberTheory.Moduli (powerModInteger)
import Data.List (intersperse)
import GHC.Real ( Ratio(..) )
import CanonInternals
import CanonAdditive

-----------------------------------------------------------------------------
data CanonValueType = IntegralC | NonIntRationalC | IrrationalC deriving (Eq, Ord, Show)

type GCRE_ = (Integer, Canon)
type GCR_  = [GCRE_]

data Canon = Bare Integer Bool | Canonical GCR_ CanonValueType 

-- A "Bare True" number means a prime number, +/-1 or 0.  The code must set the flag properly
-- A "Bare False" number is an integer that has not been checked (to see if it can be factored)
---------------------------------------------------------------------------

makeCanon :: Integer -> Canon
makeCanon n = makeCanon' n False

makeC :: Integer -> Canon
makeC = makeCanon

makeCanonFull :: Integer -> Canon
makeCanonFull n = makeCanon' n True

makeCanon' :: Integer -> Bool -> Canon
makeCanon' n b = crToC (crFromI n) b 
-- next step: enhance this once we can reaching and partially factor numbers

cCutoff :: Integer
cCutoff = 1000000

makeDefCanonForExpnt :: Integer -> Canon
--makeDefCanonForExpnt e | trace ("makeDefCanonForExpnt trace: Processing " ++ (show e)) False = undefined
makeDefCanonForExpnt e = if (e > cCutoff) then (Bare e (isSimplified e)) else (makeCanonFull e)

-- dips back to original underlying data structure
crToC :: CR_ -> Bool -> Canon
crToC POne _                  = Bare 1              True
crToC c    b | crSimplified c = Bare (fst $ head c) True -- a little ugly
             | otherwise      = Canonical g (gcrCVT g)
                                where g          = map (\x -> ((fst x), convPred $ snd x)) c
                                      convPred e = if b then (makeCanonFull e) -- do complete factorization
                                                        else (makeDefCanonForExpnt e)
                                                        -- Leave exponents "Bare" with flag based on if whether it's "simplified"
                                                        -- (can't be reduced any further)

-------------------------------------------
instance Eq Canon where
  x == y = cEq x y

-------------------------------------------                                                             
instance Show Canon where 
  show (Bare n False) = "(" ++ (show n) ++ ")" -- note: the extra characters.  Doesn't mean the figure is negative
  show (Bare n True)  = show n
  show c              = if (denom == c1) then (cShow' numer False) 
                                         else ( (cShow' numer True) ++ " / " ++ (cShow' denom True) )
                                         
                        where (numer, denom)      = cSplit c  
                              cShow' (Bare n f) _ = show $ Bare n f
                              cShow' v          w = if w then ("(" ++ catList ++ ")") else catList -- w = with(out) parens
                                                    where catList            = concat $ intersperse " * " (map showElement (cToGCR v))              
                                                          showElement (p, e) = if (ptLevel > 2)
                                                                               then (show p) ++ " <^> " ++ (cShow' (makeCanonFull $ ptLevel) True)
                                                                               else (
                                                                                 case e of
                                                                                   Bare 1 _ -> show p
                                                                                   Bare _ _ -> (show p) ++ "^" ++ (show e)                         
                                                                                   _        -> (show p) ++ " ^ (" ++ (show e) ++ ")"
                                                                               )
                                                                               where ptLevel = cPrimeTowerLevel' e p 1 
                                                                                     -- to do: try for add'l collapse into <<^>>
                                                                                     --ptc     = makeCanonFull ptLevel
                                                                                     
-------------------------------------------
instance Enum Canon where
  toEnum   n = makeCanon $ fromIntegral n
  fromEnum c = fromIntegral $ cToI c

-------------------------------------------  
instance Ord Canon where
  compare x y = cCmp x y 

-------------------------------------------
instance Real Canon where
  toRational c = if   (cIrrational c) 
                 then (toRational $ cToD c)
                 else ( (cToI $ cNumerator c) :% (cToI $ cDenominator c) )

-------------------------------------------
instance Integral Canon where
  toInteger c = if (cIntegral c) then (cToI c) else (floor $ cToD c)
  quotRem n m = cQuotRem n m
  mod n m     = cMod n m
            
-------------------------------------------
instance Fractional Canon where
  fromRational (n :% d) = (makeCanon n) / (makeCanon d)                    
  (/) x y               = cDiv x y

-------------------------------------------
instance Num Canon where
  fromInteger n = makeCanon n
  x + y         = cAdd x y
  x - y         = cSubtract x y
  x * y         = cMult x y
  
  negate x      = cNegate x
  abs x         = cAbs    x
  signum x      = cSignum x

-------------------------------------------
cCanonical :: Canon -> Bool
cCanonical (Canonical _ _ ) = True
cCanonical _                = False

cBare :: Canon -> Bool
cBare (Bare _ _ ) = True
cBare _           = False

cBareStatus :: Canon -> Bool
cBareStatus (Bare _ b) = b
cBareStatus _          = error "cBareStatus: Can only checked for 'Bare' Canons"

cValueType :: Canon -> CanonValueType
cValueType (Bare      _ _ ) = IntegralC
cValueType (Canonical _ v ) = v

cSplit :: Canon -> (Canon, Canon)
cSplit c = (cNumerator c, cDenominator c)

cEq:: Canon -> Canon -> Bool  
cEq (Bare x _ )      (Bare y _ )      = x == y
cEq (Bare _ True)    (Canonical _ _ ) = False
cEq (Canonical _ _ ) (Bare _ True)    = False
cEq (Bare x False)   y                = if ((cValueType y) /= IntegralC ) then False else (cEq (makeCanon x) y)
cEq x                (Bare y False)   = if ((cValueType x) /= IntegralC ) then False else (cEq x (makeCanon y))
cEq (Canonical x a ) (Canonical y b ) = if (a /= b) then False else (gcrEqCheck x y)

cOdd :: Canon -> Bool
cOdd (Bare x _)               = mod x 2 == 1
cOdd (Canonical c IntegralC ) = gcrOdd c
cOdd (Canonical _ _ )         = False

cGCD :: Canon -> Canon -> Canon
cGCD x y = cLGApply gcrGCD' x y

cLCM :: Canon -> Canon -> Canon
cLCM x y = cLGApply gcrLCM' x y

cLog :: Canon -> Rational
cLog x = gcrLog $ cToGCR x 

cLogDouble :: Canon -> Double
cLogDouble x = gcrLogDouble $ cToGCR x 

cCmp :: Canon -> Canon -> Ordering
cCmp (Bare x _) (Bare y _) = compare x y
cCmp x          y          = gcrCmp (cToGCR x) (cToGCR y)

cQuotRem :: Canon -> Canon -> (Canon, Canon)
cQuotRem x y = if ((cIntegral x) && (cIntegral y)) then (gcrToC q', m')
                                                   else (error "cQuotRem: Must both parameters must be integral")
               where (q', m') = case gcrDiv (cToGCR x) gy of
                                  Left  _        -> (q,        m)
                                  Right quotient -> (quotient, c0)
                                where gy = cToGCR y
                                      m = cMod x y  -- Better to compute quotient this way .. to take adv. of alg. forms
                                      q = gcrDivStrict (cToGCR $cSubtract x m) gy  -- equivalent to: (x - (x%y)) / y.

cMod :: Canon -> Canon -> Canon
cMod c m = if ((cIntegral c) && (cIntegral m)) then (makeCanon $ cModI c (cToI m))
                                               else error "cMod: Must both parameters must be integral"

cModI :: Canon -> Integer -> Integer
cModI _   0       = error "cModI: Divide by zero error when computing n mod 0"
cModI _   1       = 0
cModI _   (-1)    = 0
cModI Pc1 PIntPos = 1
cModI Pc0 _       = 0
cModI c   m       | cn && mn         = -1 * cModI (cAbs c) (abs m)
                  | (cn && (not mn)) ||
                    ((not cn) && mn) = (signum m) * ( (abs m) - (cModI' (cAbs c) (abs m)) )
                  | otherwise        = cModI' c m
                    where cn         = cNegative c
                          mn         = m < 0

cModI' :: Canon -> Integer -> Integer                     
cModI' (Bare      n _         ) m = mod n m
cModI' (Canonical c IntegralC ) m = mod (product $ map (\x -> powerModInteger (fst x) (mmt $ snd x) m) c) m
                                    where tm    = totient m
                                          mmt e = cModI e tm -- optimization
cModI' (Canonical _ _         ) _ = error "cModI': Logic error:  Canonical var has to be integral at this point"                                    

------------------------------------------------------------------------------
-- Tetration and Hyperoperations: https://en.wikipedia.org/wiki/Hyperoperation
-- The thinking around the operators is that they should look progressively scarier :)

infixr 9 <^>

(<^>) :: Canon -> Integer -> Canon
a <^> b = cTetration a b

infixr 9 <<^>>

(<<^>>) :: Canon -> Integer -> Canon
a <<^>> b = cPentation a b

infixr 9 <<<^>>>

(<<<^>>>) :: Canon -> Integer -> Canon
a <<<^>>> b = cHexation a b

---------------------

cTetration :: Canon -> Integer -> Canon
cTetration a b = cHyperOp 4 a b

cPentation :: Canon -> Integer -> Canon
cPentation a b = cHyperOp 5 a b

cHexation :: Canon -> Integer -> Canon
cHexation a b = cHyperOp 6 a b

-- Question: (Ir)rational Canons allowed?
cHyperOp :: Integer -> Canon -> Integer -> Canon
cHyperOp n a b = if (b < -1) 
                 then (error "Hyperoperations not defined when b < -1")
                 else (if (a /= c0 && a /= c1 && b > 1) then (cHyperOp' n cb) else (cHyperOpSp' n a b))

                 where cb = makeCanon b
                       -- Function for regular cases
                       cHyperOp' 1  b' = a +  b' -- addition
                       cHyperOp' 2  b' = a *  b' -- multiplication
                       cHyperOp' 3  b' = a <^ b' -- exponentiation
                        -- tetration and beyond
                       cHyperOp' _  Pc1 = a
                       cHyperOp' n' b'  = cHyperOp' (n'-1) (cHyperOp' n' (b'-1))

                       -- Function for special cases:                 
                       -- Note: When n (first param) is zero, that is known as "succession"
                       -- a is zero
                       cHyperOpSp' 0 Pc0 b'   = makeCanon (b' + 1)
                       cHyperOpSp' 1 Pc0 b'   = makeCanon b'
                       cHyperOpSp' 2 Pc0 _    = c0
                       cHyperOpSp' 3 Pc0 b'   = if (b' == 0) then c1 else c0
                       cHyperOpSp' _ Pc0 b'   = if ((mod b' 2) == 1) then c0 else c1
                       -- b is zero
                       cHyperOpSp' 0 _   0    = c1 
                       cHyperOpSp' 1 a'  0    = a'
                       cHyperOpSp' 2 _   0    = c0 
                       cHyperOpSp' _ _   0    = c1 
                        -- b is -1
                       cHyperOpSp' 0 _   (-1) = c0
                       cHyperOpSp' 1 a'  (-1) = a' - 1
                       cHyperOpSp' 2 a'  (-1) = cNegate a'
                       cHyperOpSp' 3 a'  (-1) = cReciprocal a'
                       cHyperOpSp' _ _   (-1) = c0

                       cHyperOpSp' _ Pc1 _    = c1
                       cHyperOpSp' _ a'  1    = a'
                       cHyperOpSp' _ _   _    = error "Can't compute this hyperoperation.  b must be >= -1"                

infixl 7 %
(%) :: (Integral a) => a -> a -> a
n % m = mod n m 

infixr 9 <^

class CanonExpnt a b c | a b -> c where -- are there defaults
  (<^) :: a -> b -> c

instance CanonExpnt Canon Canon Canon where
  p <^ e = cExp p e True
  
instance CanonExpnt Integer Integer Canon where
  p <^ e = cExp (makeCanon p) (makeDefCanonForExpnt e) True

instance CanonExpnt Canon Integer Canon where
  p <^ e = cExp p (makeDefCanonForExpnt e) True

instance CanonExpnt Integer Canon Canon where
  p <^ e = cExp (makeCanon p) e True

-------------------------------------------------------------  
infixr 9 >^ -- r >^ n means attempt to take the rth root of n

class CanonRoot a b c | a b -> c where -- are there defaults?
  (>^) :: a -> b -> c

instance CanonRoot Canon Canon Canon where
  r >^ n = cRoot n r
  
instance CanonRoot Integer Integer Canon where
  r >^ n = cRoot (makeCanon n) (makeCanon r)
  
instance CanonRoot Integer Canon Canon where
  r >^ n = cRoot n (makeCanon r) 

instance CanonRoot Canon Integer Canon where
  r >^ n = cRoot (makeCanon n) r 

------------------------------------------------------------- 
crSimplified :: CR_ -> Bool
crSimplified POne  = True
crSimplified PZero = True                                                        
crSimplified PN1   = True  
crSimplified c     = crPrime c
                                                        
cToCR :: Canon -> CR_
cToCR (Canonical c v) = if (v /= IrrationalC) then (gcrToCR c) else error "cToCR: Cannot convert irrational Canons to underlying data structure"
cToCR (Bare 1 _ )     = cr1
cToCR (Bare n False)  = crFromI n
cToCR (Bare n True)   = [(n,1)] -- not ideal

gcrToC :: GCR_ -> Canon
gcrToC g | gcrBare g = Bare (gcrToI g) True
         | otherwise = Canonical g (gcrCVT g)

-- CVT means CanonValueType   
gcrCVT :: GCR_ -> CanonValueType         
gcrCVT POne = IntegralC
gcrCVT g    = gcrCVT' g IntegralC -- start Integral, can only get "worse"
              where gcrCVT' _           IrrationalC = IrrationalC
                    gcrCVT' POne        v           = v
                    gcrCVT' ((_,ce):cs) v           = gcrCVT' cs (dcv v ce) -- check the exponents for expr's value type
                    gcrCVT' _           _           = error "gcrCVT : Logic error. Patterns should have been exhaustive"

                    -- checking exponents
                    dcv IrrationalC _                             = IrrationalC
                    dcv _           (Canonical _ IrrationalC)     = IrrationalC
                    dcv _           (Canonical _ NonIntRationalC) = IrrationalC
                    dcv IntegralC   (Bare      n _ )              = if (n < 0) then NonIntRationalC else IntegralC
                    dcv v           (Bare      _ _ )              = v
                    dcv v           c                             = if (cNegative c) then NonIntRationalC else v                    
     
c1 :: Canon
c1 = makeCanon 1

c0 :: Canon
c0 = makeCanon 0

cN1 :: Canon
cN1 = makeCanon (-1)

cToI :: Canon -> Integer
--cToI c | trace ("cToI trace: Processing " ++ (show c)) False = undefined
cToI (Bare i _ )     = i
cToI (Canonical c v) = if (v == IntegralC) then (gcrToI c) else (error "Can't convert non-integral canon to an integer")

cToD :: Canon -> Double
cToD (Bare i _ )      = fromIntegral i
cToD (Canonical c _ ) = gcrToD c 

cMult :: Canon -> Canon -> Canon                                                    
cMult Pc0              _                = 0
cMult _                Pc0              = 0
cMult Pc1              y                = y
cMult x                Pc1              = x
cMult x                y                = gcrToC $ gcrMult (cToGCR x) (cToGCR y)

cApplyAdtvOp :: Bool -> Canon -> Canon -> Canon
cApplyAdtvOp _     x   Pc0 = x
cApplyAdtvOp True  Pc0 y   = y         -- True -> (+)
cApplyAdtvOp False Pc0 y   = negate y  -- False -> (-) 
cApplyAdtvOp b     x   y    = gcd' * r
                               where gcd' = cGCD x y 
                                     x'   = x / gcd'
                                     y'   = y / gcd'
                                     r    = crToC (crApplyAdtvOpt' b (cToCR x') (cToCR y')) False -- costly bit

cAdd :: Canon -> Canon -> Canon
cAdd x y = cApplyAdtvOp True x y

cSubtract :: Canon -> Canon -> Canon
cSubtract x y = cApplyAdtvOp False x y

-- this does allow for negative exponentiation if bool flag is True
cExp :: Canon -> Canon -> Bool -> Canon
cExp c e b | cNegative e && (not b) 
                       = error "Per param flag, negative exponentiation is not allowed here."
           | cIrrational c && cIrrational e 
                       = error "cExp: Raising an irrational number to an irrational power is not currently supported."
           | otherwise = cExp' c e

cExp' :: Canon -> Canon -> Canon           
cExp' Pc0 e'   = if (cPositive e') then c0 else error "0^e where e <= 0 is either undefined or illegal"
cExp' Pc1 _    = c1
cExp' _   Pc0  = c1
cExp' c'   e'  = gcrToC $ gcrExp' (cToGCR c') e'

cNegative :: Canon -> Bool
cNegative (Bare n      _ ) = n < 0
cNegative (Canonical c _ ) = gcrNegative c

cPositive:: Canon -> Bool
cPositive (Bare n _      ) = n > 0
cPositive (Canonical c _ ) = gcrPositive c

cNegate :: Canon -> Canon
cNegate (Bare 0 _)      = c0
cNegate (Bare 1 _)      = cN1
cNegate (Bare x False)  = Bare (-1 * x) False
cNegate (Bare x True)   = Canonical (gcreN1 : [(x, c1)]) IntegralC -- not ideal
cNegate (Canonical x v) = gcrNegateCanonical x v
      
cAbs :: Canon -> Canon
cAbs x | cNegative x = cNegate x
       | otherwise   = x

cSignum :: Canon -> Canon
cSignum (Bare 0 _)      = c0
cSignum g | cNegative g = cN1
          | otherwise   = c1

-- works for either gcrGCD' or gcrLCM'
cLGApply :: (GCR_ -> GCR_ -> GCR_) -> Canon -> Canon -> Canon
cLGApply _ Pc0 y   = y
cLGApply _ x   Pc0 = x
cLGApply f x   y   | cNegative x || 
                     cNegative y = gcrToC $ f (cToGCR $ cAbs x) (cToGCR $ cAbs y)
                   | otherwise   = gcrToC $ f (cToGCR x)        (cToGCR y)

cDiv :: Canon -> Canon -> Canon
cDiv _ Pc0 = error "cDiv: Division by zero error"
cDiv x y   = cMult (cReciprocal y) x -- multiply by the reciprocal

cReciprocal :: Canon -> Canon
cReciprocal x = cExp x cN1 True  -- raise number to (-1)st power

cIntegral :: Canon -> Bool
cIntegral (Bare      _ _ ) = True
cIntegral (Canonical _ v ) = v == IntegralC

-- for processing "rational" canon reps
cNumerator :: Canon -> Canon
cNumerator (Canonical c _ ) = gcrToC $ filter (\x -> cPositive $ snd x) c -- filter positive exponents
cNumerator b                = b 

cDenominator :: Canon -> Canon
cDenominator (Canonical c _ ) = gcrToC $ map (\t -> (fst t, cN1 * snd t)) $ filter (\x -> cNegative $ snd x) c -- negate negative expnts
cDenominator _                = c1 

cIrrational :: Canon -> Bool
cIrrational (Canonical _ IrrationalC ) = True
cIrrational _                          = False

cRational :: Canon -> Bool
cRational c = not $ cIrrational c

cDepth :: Canon-> Integer
cDepth (Bare      _ _ ) = 1
cDepth (Canonical c _ ) = 1 + gcrDepth c

cSimplified :: Canon -> Bool
cSimplified (Bare      _ b )  = b
cSimplified (Canonical c _ ) = gcrSimplified c

cSimplify :: Canon -> Canon
cSimplify (Bare      n False) = makeCanonFull n
cSimplify (Canonical c _ )    = gcrToC $ gcrSimplify c
cSimplify g                   = g  -- Bare number already simplified : Fix when expr come into play

cRoot :: Canon -> Canon -> Canon 
cRoot  c  r  | cNegative r = error "r-th roots are not allowed when r <= 0" 
             | otherwise   = gcrToC $ gcrRoot' (cToGCR c) (cToGCR r)

cIsPrimeTower :: Canon -> Bool
cIsPrimeTower c = (cPrimeTowerLevel c) > 0 -- x^x would not be, but x^x^x

cPrimeTowerLevel :: Canon -> Integer                  
cPrimeTowerLevel (Bare      _ True)      = 1
cPrimeTowerLevel (Canonical g IntegralC) = case gcrPrimePower g of
                                             False -> 0
                                             True  -> cPrimeTowerLevel' (snd $ head g) (fst $ head g) (1 :: Integer)
cPrimeTowerLevel _                       = 0

cPrimeTowerLevel' :: Canon -> Integer -> Integer -> Integer
cPrimeTowerLevel' (Bare b _ )             n l = if (b == n) then (l + 1) else 0
cPrimeTowerLevel' (Canonical g IntegralC) n l = case gcrPrimePower g of
                                                   False -> 0
                                                   True  -> if (n /= (fst $ head g)) then 0
                                                            else (cPrimeTowerLevel' (snd $ head g) n (l+1))
cPrimeTowerLevel' _                       _ _ = 0

-------------------------------------------------------------
-------------------------------------------------------------
cToGCR :: Canon -> GCR_
cToGCR = canonToGCR

canonToGCR :: Canon -> GCR_
canonToGCR (Canonical x _) = x
canonToGCR (Bare x False)  = canonToGCR $ makeCanon x
canonToGCR (Bare x True)   = if (x == 1) then gcr1 else [(x, c1)]

-------------------------------------------------------------
-------------------------------------------------------------
gcrExp' :: GCR_ -> Canon -> GCR_
gcrExp' c e | gcrNegative c = case cValueType e of 
                              IntegralC       -> if (cOdd e) then (gcreN1:absTail) else absTail
                              NonIntRationalC -> if (cOdd d) then (gcreN1:absTail)
                                                             else (error "gcrExp': Imaginary numbers are not supported")
                              IrrationalC     -> error "gcrExp': Raising negative numbers to irrational powers is not supported"
            | otherwise     = map (\x -> ((fst x), e * (snd x))) c
            where absTail   = gcrExp' (gcrAbs c) e
                  (_, d)    = cSplit e
                  
-- Warning: Don't call this for 0 or +/- 1.  The value type will not change by negating the value     
gcrNegateCanonical :: GCR_ -> CanonValueType -> Canon    
gcrNegateCanonical g  v | gcrNegative g = case gcrPrime (tail g) of
                                            True  -> Bare (fst $ head $ tail g) True
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

gcrMult :: GCR_ -> GCR_ -> GCR_
--gcrMult x y | trace ("gcrMult trace: Processing " ++ (show x) ++ " * " ++ (show y)) False = undefined     
gcrMult x    POne = x
gcrMult POne y    = y
gcrMult _    Pg0  = gcr0
gcrMult Pg0  _    = gcr0
gcrMult x    y    = case compare xp yp of
                    LT -> xh : gcrMult xs y                          
                    EQ -> if ((gcrNegative x) || expSum == c0) 
                          then (gcrMult xs ys)    -- cancel double negs or expnts adding to zero
                          else ((xp, expSum) : gcrMult xs ys)                                                   
                    GT -> yh : gcrMult x ys
                    where (xh:xs)  = x
                          (yh:ys)  = y  
                          (xp, xe) = xh
                          (yp, ye) = yh                           
                          expSum   = xe + ye                             
gcr1 :: GCR_
gcr1 = []
           
gcr0 :: GCR_
gcr0 = [(0, c1)]   

gcreN1 :: GCRE_
gcreN1 = (-1, c1)

gcrToI :: GCR_ -> Integer
--gcrToI g | trace ("gcrToI trace: Processing " ++ (show g)) False = undefined
gcrToI g = product $ map (\x -> f x) g
           where f (p, e)  = if (ce > 0) then (p ^ ce)
                             else (error negExpErr)
                             where ce = cToI $ e 
                 negExpErr = "gcrToI: Negative exponent found trying to convert " ++ (show g)

gcrToD :: GCR_ -> Double
gcrToD g = product $ map (\x -> (fromIntegral $ fst x) ** (cToD $ snd x)) g
                        
gcrCmp :: GCR_ -> GCR_ -> Ordering
gcrCmp POne y            = gcrCmp' y True
gcrCmp x    POne         = gcrCmp' x False
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
           where xN      = gcrNegative x
                 yN      = gcrNegative y  

gcrCmp' :: GCR_ -> Bool -> Ordering
gcrCmp' PNeg b = if b then GT else LT
gcrCmp' Pg0  b = if b then GT else LT
gcrCmp' _    b = if b then LT else GT 

gcrLog :: GCR_ -> Rational
gcrLog g = crLog $ gcrToCR g   

----------------------------------------------------------------------------
-- the definition of gcd and lcm are extended t0 handle non-integers
----------------------------------------------------------------------------
 
-- don't call this directly
gcrGCD' :: GCR_ -> GCR_ -> GCR_
gcrGCD' POne _    = gcr1
gcrGCD' _    POne = gcr1
gcrGCD' x    y    = case compare xp yp of
                      LT -> gcrGCD' xs y
                      EQ -> (xp, min xe ye) : gcrGCD' xs ys                    
                      GT -> gcrGCD' x ys
                    where ((xp,xe):xs) = x
                          ((yp,ye):ys) = y    

-- don't call this directly
gcrLCM' :: GCR_ -> GCR_ -> GCR_   
gcrLCM' POne y    = y
gcrLCM' x    POne = x        
gcrLCM' x    y    = case compare xp yp of
                      LT -> xh : gcrLCM' xs y
                      EQ -> (xp, max xe ye) : gcrLCM' xs ys
                      GT -> yh : gcrLCM' x ys
                    where (xh:xs)  = x
                          (yh:ys)  = y  
                          (xp, xe) = xh
                          (yp, ye) = yh

gcrLogDouble :: GCR_ -> Double
gcrLogDouble g = sum $ map (\x -> (log $ fromIntegral $ fst x) * (cToD $ snd x)) g

-- This is much more expensive but accurate.  You have an "infinity" problem potentially with gcrLogDouble
gcrLog'' :: GCR_ -> Rational              
gcrLog'' g = sum $ map (\x -> (toRational $ logDouble $ fromIntegral $ fst x) * (toRational $ snd x)) g
             where logDouble :: Double -> Double
                   logDouble n = log n

-------------------------------------------------------------
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
-- gcrDiv a b | trace ("gcrDiv trace: Processing " ++ (show a) ++ " / " ++ (show b)) False = undefined

gcrDiv Pg0 Pg0 = Left zeroDivZeroError 
gcrDiv Pg0 _   = Right gcr0
gcrDiv _   Pg0 = Left divByZeroError
gcrDiv x   y   = gcrDiv' x y

-- call this after handling zeroes above
gcrDiv' :: GCR_ -> GCR_ -> Either String GCR_
gcrDiv' x     POne = Right x
gcrDiv' POne  _    = Left divisionError
gcrDiv' x     y 
  | gcrNegative y  = gcrDiv' (gcrNegate x) (gcrAbs y)
  | otherwise      = case compare xp yp of      
                     LT           -> case (gcrDiv' xs y) of
                                       Left _        -> Left divisionError
                                       Right results -> Right ((xp, xe) : results)
                     EQ | xe > ye -> case (gcrDiv' xs ys) of
                                       Left _        -> Left divisionError
                                       Right results -> Right ((xp, xe - ye) : results)
                     EQ | xe == ye -> gcrDiv xs ys
                     _             -> Left divisionError                     
   where ((xp,xe):xs) = x
         ((yp,ye):ys) = y 

---------------------------------------------------------------------
-- GCR functions (GCR is an acronym for generalized canonical representation)
---------------------------------------------------------------------

gcrAbs :: GCR_ -> GCR_
gcrAbs x | gcrNegative x = tail x
         | otherwise     = x

gcrToCR :: GCR_ -> CR_
gcrToCR c = map (\x -> ((fst x), cToI $ snd x)) c

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

gcrOdd :: GCR_ -> Bool
gcrOdd Pg0  = False
gcrOdd POne = True
gcrOdd c    | gcrNegative c  = gcrOdd (gcrAbs c)
            | otherwise      = cp == 2 
              where (cp,_):_ = c

gcrEven :: GCR_ -> Bool
gcrEven g = not (gcrOdd g)

gcrEqCheck :: GCR_ -> GCR_ -> Bool
gcrEqCheck POne POne = True
gcrEqCheck POne _    = False
gcrEqCheck _    POne = False 
gcrEqCheck x    y    = if (xp /= yp || xe /= ye) then False else (gcrEqCheck xs ys)
                        where (xp, xe):xs = x
                              (yp, ye):ys = y

gcrDepth :: GCR_ -> Integer
gcrDepth g = maximum $ map (\x -> cDepth $ snd x) g

gcrSimplified :: GCR_ -> Bool
gcrSimplified g = foldr1 (&&) (map (\x -> cSimplified $ snd x) g)               

gcrSimplify :: GCR_ -> GCR_
gcrSimplify g = map (\x -> (fst x, cSimplify $ snd x)) g

rootError :: GCR_ -> GCR_ -> String
rootError c r = "gcrRoot': All exponents must be multiples of " ++ (show r) ++ ".  Not so with " ++ (show c)

gcrRoot' :: GCR_ -> GCR_ -> GCR_
gcrRoot' POne _   = gcr1   
gcrRoot' c    r
  | gcrNegative c = if (gcrEven r) then (error "Imaginary numbers not allowed: Even root of negative number requested.")
                                   else (gcreN1 : gcrRoot' (gcrAbs c) r)                           
  | otherwise     = case gcrDiv (cToGCR ce) r of
                      Left  _        -> error $ rootError c r
                      Right quotient -> (cp, gcrToC quotient) : gcrRoot' cs r
                    where ((cp,ce):cs) = c   

------------------------------------------------------------------------------------------------------------
-- check if the number is simplified rather than factoring it
isSimplified :: Integer -> Bool
isSimplified n = if (n < -1) then False else (if (n > 1) then (isPrime n) else True)
                                                                   
------------------------------------------------------------------------------------------------------------
-- of form x^1 where x > 1 -- prime (assumption p has already been verified to be prime)
pattern PBare   <- [(_, Bare 1 _)] 

-- of form x^1 where x > 1 -- prime (assumption p has already been verified to be prime) 
pattern PgPPower <- [(compare 1 -> LT, _ )]
pattern PgPrime  <- [(compare 1 -> LT, Bare 1 _)] 
pattern PgNeg    <- ((-1, Bare 1 _):_) 

pattern Pg0     <- [(0, Bare 1 _)]  -- internal pattern for zero
pattern Pc0     <- Bare 0 _         -- pattern for zero
pattern Pc1     <- Bare 1 _         -- pattern for 1
                                     