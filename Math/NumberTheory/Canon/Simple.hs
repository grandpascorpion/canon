-- |
-- Module:      Math.NumberTheory.Canon.Simple
-- Copyright:   (c) 2015-2018 Frederick Schneider
-- Licence:     MIT
-- Maintainer:  Frederick Schneider <frederick.schneider2011@gmail.com>
-- Stability:   Provisional
--
-- This a wrapper for the Canonical Representation type found in the Internals module.  
-- If you want to work with arbitrarily nested prime towers, you can use the Math.NumberTheory.Canon module.

{-# LANGUAGE MultiParamTypeClasses,FunctionalDependencies, FlexibleInstances, PatternSynonyms, ViewPatterns #-}

module Math.NumberTheory.Canon.Simple ( 
  SimpleCanon(..),  SC,
  toSimpleCanon,    toSC,   toSimpleCanonViaUserFunc,
  fromSimpleCanon,  fromSC,
  CanonConv,

  scGCD, scLCM,
  scLog, scLogDouble,
  scNegative, scPositive,
  scToInteger, scToI,
   
  RationalSimpleCanon(..), RC,
  toRationalSimpleCanon,   toRC,   toRationalSimpleCanonViaUserFunc,
  fromRationalSimpleCanon, fromRC, 
  rcNegative, rcPositive,              
  
  getNumer,     getDenom,     getNumerDenom,
  getNumerAsRC, getDenomAsRC, getNumerDenomAsRCs,  
  rcLog,        rcLogDouble,
                                
  (>^), (<^), (%)         
)
where

import GHC.Real (Ratio(..))
import Math.NumberTheory.Canon.Internals
import Math.NumberTheory.Canon.Additive
import Math.NumberTheory.Canon.AurifCyclo (crCycloInitMap)

-- | SimpleCanon is a new type wrapping a canonical representation.
newtype SimpleCanon = MakeSC CR_ deriving (Eq)

-- | This function allow you to specify a user function when converting a canon rep to an SC.
toSimpleCanonViaUserFunc :: CR_ -> (Integer -> Bool) -> SimpleCanon
toSimpleCanonViaUserFunc c f | crValidIntegralViaUserFunc c f == False = error $ invalidError 
                             | otherwise                               = MakeSC c
                             where invalidError = "toSimpleCanonViaUserFunc: Invalid integral canonical rep passed to constructor: " ++ (show c) 

-- | Grab the canon rep from a SimpleCanon.
fromSimpleCanon, fromSC :: SimpleCanon -> CR_
fromSimpleCanon (MakeSC i) = i
fromSC = fromSimpleCanon

-- | Shorthand type declaration
type SC = SimpleCanon

-- | Define various instances
instance Show SimpleCanon where 
  show c = crShow $ fromSC c
           
instance Enum SimpleCanon where
  toEnum   n = toSimpleCanon $ crFromI $ fromIntegral n
  fromEnum c = fromIntegral $ crToI $ fromSC c

instance Ord SimpleCanon where
  compare x y = crCmp (fromSC x) (fromSC y)

instance Real SimpleCanon where
  toRational c = scToI c :% 1

instance Integral SimpleCanon where
  toInteger c = scToI c
  quotRem n m = (MakeSC n', MakeSC m') 
                where (n', m') = fst $ crQuotRem (fromSC n) (fromSC m) crCycloInitMap
  mod n m     = MakeSC $ crMod (fromSC n) (fromSC m)
            
instance Fractional SimpleCanon where
  fromRational (n :% d) | m == 0    = MakeSC $ crFromI q
                        | otherwise = error "Modulus not zero.  Use Rational SimpleCanons for non-integers."
                        where (q, m) = quotRem n d
  (/) x y               = MakeSC $ crDivStrict (fromSC x) (fromSC y)

instance Num SimpleCanon where
  fromInteger n = MakeSC $ crFromI n    -- to do: check where called?
  x + y         = MakeSC $ fst $ crAdd      (fromSC x) (fromSC y) crCycloInitMap -- discard the map info
  x - y         = MakeSC $ fst $ crSubtract (fromSC x) (fromSC y) crCycloInitMap -- discard the map info
  x * y         = MakeSC $ crMult     (fromSC x) (fromSC y)
  
  negate x      = MakeSC $ crNegate $ fromSC x
  abs x         = MakeSC $ crAbs    $ fromSC x
  signum x      = MakeSC $ crSignum $ fromSC x

-- | Convert a SimpleCanon back to an Integer.
scToInteger, scToI :: SimpleCanon -> Integer
scToI c     = crToI $ fromSC c
scToInteger = scToI

-- | SimpleCanon GCD and LCM functions
scGCD, scLCM :: SimpleCanon -> SimpleCanon -> SimpleCanon
scGCD x y = MakeSC $ crGCD (fromSC x) (fromSC y)
scLCM x y = MakeSC $ crLCM (fromSC x) (fromSC y)

-- | Wrappers for underlying canon rep functions
scNegative, scPositive :: SimpleCanon -> Bool
scNegative c = crNegative $ fromSC c
scPositive c = crPositive $ fromSC c

-- | Wrapper for underlying CR function
scLog :: SimpleCanon -> Rational
scLog x = crLog $ fromSC x 

-- | Wrapper for underlying CR function
scLogDouble :: SimpleCanon -> Double
scLogDouble x = crLogDouble $ fromSC x 

-- | Newtype for RationalSimpleCanon.  The underlying canon rep is the same.
newtype RationalSimpleCanon = MakeRC CR_ deriving (Eq)

-- | Convert canon rep to RationalSimpleCanon via a user-supplied criterion function.
toRationalSimpleCanonViaUserFunc :: CR_ -> (Integer -> Bool) -> RationalSimpleCanon
toRationalSimpleCanonViaUserFunc c f | crValidRationalViaUserFunc c f == False = error $ invalidError 
                               | otherwise                               = MakeRC c
                               where invalidError = 
                                       "toRationalSimpleCanonViaUserFunc: Invalid rational canonical rep passed to constructor: " 
                                       ++ (show c) ++ " (user predicate supplied)" 

-- | Convert RC back to underlying canon rep.
fromRationalSimpleCanon, fromRC :: RationalSimpleCanon -> CR_
fromRC (MakeRC i)       = i
fromRationalSimpleCanon = fromRC

-- | Shorthand type name 
type RC = RationalSimpleCanon

-- | Define various instances for RationSimpleCanon.
instance Show RationalSimpleCanon where 
  show rc = crShowRational $ fromRC rc
  
instance Enum RationalSimpleCanon where
  toEnum   n = toRC $ crFromI $ fromIntegral n
  fromEnum c = fromIntegral $ toInteger c -- if not integral, this will fail

-- | Caveat: These functions will error out (in)directly if there are any negative exponents.
instance Integral RationalSimpleCanon where
  toInteger rc = crToI $ fromRC rc
  quotRem n m  | crIntegral $ fromRC n = (MakeRC n', MakeRC m') 
               | otherwise             = error "Can't perform 'quotRem' on non-integral RationalSimpleCanon"
               where (n', m') = fst $ crQuotRem (fromRC n) (fromRC m) crCycloInitMap
  mod n m      | crIntegral $ fromRC n = MakeRC $ crMod (fromRC n) (fromRC m) 
               | otherwise             = error "Can't perform 'mod' on non-integral RationalSimpleCanon"

instance Fractional RationalSimpleCanon where
  fromRational (n :% d) = MakeRC $ crDivRational (crFromI n) (crFromI d)
  (/) x y               = MakeRC $ crDivRational (fromRC x)  (fromRC y)

instance Ord RationalSimpleCanon where
  compare x y = crCmp (fromRC x) (fromRC y)
  
instance Real RationalSimpleCanon where
  toRational rc  = crToRational $ fromRC rc
                  
instance Num RationalSimpleCanon where
  fromInteger n = MakeRC $ crFromI n
  x + y         = MakeRC $ fst $ crAddR      (fromRC x) (fromRC y) crCycloInitMap
  x - y         = MakeRC $ fst $ crSubtractR (fromRC x) (fromRC y) crCycloInitMap
  x * y         = MakeRC $ crMult      (fromRC x) (fromRC y) 
  
  negate x      = MakeRC $ crNegate $ fromRC x
  abs x         = MakeRC $ crAbs    $ fromRC x 
  signum x      = MakeRC $ crSignum $ fromRC x

-- | Calls underlying canon rep function.
rcLog :: RationalSimpleCanon -> Rational
rcLog c = crLog $ fromRC c 

-- | Calls underlying canon rep function. 
rcLogDouble :: RationalSimpleCanon -> Double
rcLogDouble c = crLogDouble $ fromRC c

-- | Calls underlying canon rep function. 
getNumerAsRC :: RationalSimpleCanon -> RationalSimpleCanon
getNumerAsRC c = MakeRC $ crNumer $ fromRC c
          
-- | Calls underlying canon rep function. 
getDenomAsRC :: RationalSimpleCanon -> RationalSimpleCanon
getDenomAsRC c = MakeRC $ crDenom $ fromRC c

-- | Pulls numerator or denominator from RC and converts it to a SimpleCanon.
getNumer, getDenom :: RationalSimpleCanon -> SimpleCanon
getNumer c = MakeSC $ crNumer $ fromRC c
getDenom c = MakeSC $ crDenom $ fromRC c          

-- | Wraps crSplit function and returns a pair of SimpleCanons.
getNumerDenom :: RationalSimpleCanon -> (SimpleCanon, SimpleCanon)
getNumerDenom c = (MakeSC n, MakeSC d) 
                  where (n, d) = crSplit $ fromRC c
                 
-- | Wraps crSplit function and returns a pair of RationalSimpleCanons. 
getNumerDenomAsRCs :: RationalSimpleCanon -> (RationalSimpleCanon, RationalSimpleCanon)
getNumerDenomAsRCs c = (MakeRC n, MakeRC d) 
                        where (n, d) = crSplit $ fromRC c                                         

-- | Wraps underlying canon rep functions.
rcNegative, rcPositive :: RationalSimpleCanon -> Bool
rcNegative x = crNegative $ fromRC x
rcPositive x = crPositive $ fromRC x                         

-- | Modulus operator
infixl 7 %
(%) :: (Integral a) => a -> a -> a
n % m = mod n m 


-- | Multi-param typeclass for exponentiation
infixr 9 <^

class SimpleCanonExpnt a b c | a b -> c where 
  -- | Exponentiation Operator
  (<^) :: a -> b -> c

instance SimpleCanonExpnt Integer Integer SimpleCanon where
  p <^ e = MakeSC $ crExp (crFromI p) e False

instance SimpleCanonExpnt SimpleCanon Integer SimpleCanon where
  p <^ e = MakeSC $ crExp (fromSC p) e False

instance SimpleCanonExpnt RationalSimpleCanon Integer RationalSimpleCanon where
  p <^ e = MakeRC $ crExp (fromRC p) e True

instance SimpleCanonExpnt RationalSimpleCanon SimpleCanon RationalSimpleCanon where
  p <^ e = MakeRC $ crExp (fromRC p) (crToI $ fromSC e) True

-- | Multi-param typeclass for radical/root operator
infixr 9 >^ -- r >^ n means attempt to take the rth root of n

class SimpleCanonRoot a b c | a b -> c where
  -- | Root Operator
  (>^) :: a -> b -> c

instance SimpleCanonRoot SimpleCanon SimpleCanon SimpleCanon where
  r >^ n = MakeSC $ crRoot (fromSC n) (toInteger r)
  
instance SimpleCanonRoot Integer Integer SimpleCanon where
  r >^ n = MakeSC $ crRoot (crFromI n) r
  
instance SimpleCanonRoot Integer SimpleCanon SimpleCanon where
  r >^ n = MakeSC $ crRoot (fromSC n) r

instance SimpleCanonRoot SimpleCanon Integer SimpleCanon where
  r >^ n = MakeSC $ crRoot (crFromI n) (toInteger r)  
  
instance SimpleCanonRoot Integer RationalSimpleCanon RationalSimpleCanon where
  r >^ n = MakeRC $ crRoot (fromRC n) r

-- | Convert CanonConv types to SimpleCanon.
toSimpleCanon :: (CanonConv a) => a -> SimpleCanon
toSimpleCanon = toSC

-- | Convert CanonConv types to RationalSimpleCanon.
toRationalSimpleCanon :: (CanonConv a) => a -> RationalSimpleCanon
toRationalSimpleCanon = toRC

-- | Typeclass for converting to SimpleCanon and RationalSimpleCanon 
class CanonConv c where
  -- | Convert a type to a SimpleCanon.
  toSC          :: c -> SimpleCanon 

  -- | Convert a type to a RationalSimpleCanon.
  toRC                  :: c -> RationalSimpleCanon 
  
instance CanonConv SimpleCanon where  
  toSC c = c
  toRC c = MakeRC $ fromSC c

instance CanonConv CR_ where  
  toSC cr | crValidIntegral cr = MakeSC cr
          | otherwise          = error invalidError
          where invalidError = "Invalid integral canonical rep passed to constructor: " ++ (show cr) 
           
  toRC cr | crValidRational cr = MakeRC cr
          | otherwise          = error invalidRepRatioError 
          where invalidRepRatioError = "toRC: Invalid canonical rep passed to constructor: " ++ (show cr) 
  
instance CanonConv RationalSimpleCanon where  
  toSC rc | crValidIntegral frc = MakeSC frc
          | otherwise           = error invalidError
          where frc          = fromRC rc
                invalidError = "Invalid integral canonical rep passed to constructor: " ++ (show rc) 
  toRC rc = rc
        
