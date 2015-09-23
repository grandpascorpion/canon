{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns    #-}

module SimpleCanon ( SimpleCanon(..),  SC,
               toSimpleCanon,    toSC,   toSimpleCanonViaUserFunc,
               fromSimpleCanon,  fromSC,
               scGCD, scLCM,
               scLog, scLogDouble,
               scNegative, scPositive,
               
               RationalSimpleCanon(..), RC,
               toRationalSimpleCanon,   toRC,   toRationalSimpleCanonViaUserFunc,
               fromRationalSimpleCanon, fromRC, 
               rcNegative, rcPositive,              
               
               getNumer,     getDenom,     getNumerDenom,
               getNumerAsRC, getDenomAsRC, getNumerDenomAsRCs,  
               rscLog,        rscLogDouble,
                                
               (>^), (<^), (%)         
             )
where

import Data.List (intersperse)
import GHC.Real ( Ratio(..) )
import CanonInternals
import CanonAdditive

newtype SimpleCanon = MakeC CR_ deriving (Eq)

toSimpleCanonViaUserFunc :: CR_ -> (Integer -> Bool) -> SimpleCanon
toSimpleCanonViaUserFunc c f | crValidIntegralViaUserFunc c f == False = error $ invalidError 
                             | otherwise                                = MakeC c
                             where invalidError = "toSimpleCanonViaUserFunc: Invalid integral canonical rep passed to constructor: " ++ (show c) 

fromSimpleCanon :: SimpleCanon -> CR_
fromSimpleCanon (MakeC i) = i

type SC = SimpleCanon

fromSC :: SimpleCanon -> CR_
fromSC = fromSimpleCanon

-------------------------------------------
instance Show SimpleCanon where 
  show c = crShow (fromSC c) False
           
-------------------------------------------
instance Enum SimpleCanon where
  toEnum   n = toSimpleCanon $ crFromI $ fromIntegral n
  fromEnum c = fromIntegral $ crToI $ fromSC c

-------------------------------------------  
instance Ord SimpleCanon where
  compare x y = crCmp (fromSC x) (fromSC y)

-------------------------------------------
instance Real SimpleCanon where
  toRational c = cToI c :% 1

-------------------------------------------
instance Integral SimpleCanon where
  toInteger c = cToI c
  quotRem n m = (MakeC n', MakeC m') 
                where (n', m') = crQuotRem (fromSC n) (fromSC m)
  mod n m     = MakeC $ crMod (fromSC n) (fromSC m)
            
-------------------------------------------
instance Fractional SimpleCanon where
  fromRational (n :% d) = if (m == 0) then (MakeC $ crFromI q)
                          else (error "Modulus not zero.  Use Rational SimpleCanons for non-integers.")
                          where (q, m) = quotRem n d
                          
  (/) x y               = MakeC $ crDivStrict (fromSC x) (fromSC y)

-------------------------------------------
instance Num SimpleCanon where
  fromInteger n = MakeC $ crFromI n    -- to do: check where called?
  x + y         = MakeC $ crAdd      (fromSC x) (fromSC y)
  x - y         = MakeC $ crSubtract (fromSC x) (fromSC y)
  x * y         = MakeC $ crMult     (fromSC x) (fromSC y)
  
  negate x      = MakeC $ crNegate $ fromSC x
  abs x         = MakeC $ crAbs    $ fromSC x
  signum x      = MakeC $ crSignum $ fromSC x

-------------------------------------------

cToI :: SimpleCanon -> Integer
cToI c = crToI $ fromSC c

scGCD :: SimpleCanon -> SimpleCanon -> SimpleCanon
scGCD x y = MakeC $ crGCD (fromSC x) (fromSC y)

scLCM :: SimpleCanon -> SimpleCanon -> SimpleCanon
scLCM x y = MakeC $ crLCM (fromSC x) (fromSC y)

scNegative :: SimpleCanon -> Bool
scNegative c = crNegative $ fromSC c

scPositive :: SimpleCanon -> Bool
scPositive c = crPositive $ fromSC c

scLog :: SimpleCanon -> Rational
scLog x = crLog $ fromSC x 

scLogDouble :: SimpleCanon -> Double
scLogDouble x = crLogDouble $ fromSC x 

--------------------------------------------------
--------------------------------------------------
newtype RationalSimpleCanon = MakeRC CR_ deriving (Eq)

toRationalSimpleCanonViaUserFunc :: CR_ -> (Integer -> Bool) -> RationalSimpleCanon
toRationalSimpleCanonViaUserFunc c f | crValidRationalViaUserFunc c f == False = error $ invalidError 
                               | otherwise                               = MakeRC c
                               where invalidError = 
                                       "toRationalSimpleCanonViaUserFunc: Invalid rational canonical rep passed to constructor: " 
                                       ++ (show c) ++ " (user predicate supplied)" 

fromRC :: RationalSimpleCanon -> CR_
fromRC (MakeRC i) = i

fromRationalSimpleCanon :: RationalSimpleCanon -> CR_
fromRationalSimpleCanon = fromRC

type RC = RationalSimpleCanon
-------------------------------------------
instance Show RationalSimpleCanon where 
  show rc = crShowRational $ fromRC rc
  
  
-------------------------------------------
instance Enum RationalSimpleCanon where
  toEnum   n = toRC $ crFromI $ fromIntegral n
  fromEnum c = fromIntegral $ toInteger c -- if not integral, this will fail

-------------------------------------------
-- caveat: These functions will error out (in)directly if there are any negative exponents
instance Integral RationalSimpleCanon where
  toInteger rc = crToI $ fromRC rc
  quotRem n m  = if   (crIntegral $ fromRC n) 
                 then (MakeRC n', MakeRC m') 
                 else (error "Can't perform 'quotRem' on non-integral RationalSimpleCanon")
                  where (n', m') = crQuotRem (fromRC n) (fromRC m) 
  mod n m      = if   (crIntegral $ fromRC n) 
                 then (MakeRC $ crMod (fromRC n) (fromRC m))
                 else error "Can't perform 'mod' on non-integral RationalSimpleCanon"

-------------------------------------------
instance Fractional RationalSimpleCanon where
  fromRational (n :% d) = MakeRC $ crDivRational (crFromI n) (crFromI d)
  (/) x y               = MakeRC $ crDivRational (fromRC x)  (fromRC y)

-------------------------------------------
instance Ord RationalSimpleCanon where
  compare x y = crCmp (fromRC x) (fromRC y)
  
-------------------------------------------
instance Real RationalSimpleCanon where
  toRational rc  = crToRational $ fromRC rc
                  
-------------------------------------------
instance Num RationalSimpleCanon where
  fromInteger n = MakeRC $ crFromI n
  x + y         = MakeRC $ crAddR      (fromRC x) (fromRC y)
  x - y         = MakeRC $ crSubtractR (fromRC x) (fromRC y)
  x * y         = MakeRC $ crMult      (fromRC x) (fromRC y)
  
  negate x      = MakeRC $ crNegate $ fromRC x
  abs x         = MakeRC $ crAbs    $ fromRC x 
  signum x      = MakeRC $ crSignum $ fromRC x

rscLog :: RationalSimpleCanon -> Rational
rscLog c = crLog $ fromRC c 

rscLogDouble :: RationalSimpleCanon -> Double
rscLogDouble c = crLogDouble $ fromRC c

getNumerAsRC :: RationalSimpleCanon -> RationalSimpleCanon
getNumerAsRC c = MakeRC $ crNumer $ fromRC c
           
getDenomAsRC :: RationalSimpleCanon -> RationalSimpleCanon
getDenomAsRC c = MakeRC $ crDenom $ fromRC c

getNumer :: RationalSimpleCanon -> SimpleCanon
getNumer c = MakeC $ crNumer $ fromRC c
           
getDenom :: RationalSimpleCanon -> SimpleCanon
getDenom c = MakeC $ crDenom $ fromRC c          
  
-- could this be          
getNumerDenom :: RationalSimpleCanon -> (SimpleCanon, SimpleCanon)
getNumerDenom c = (MakeC n, MakeC d) 
                  where (n, d) = crSplit $ fromRC c
                  
getNumerDenomAsRCs :: RationalSimpleCanon -> (RationalSimpleCanon, RationalSimpleCanon)
getNumerDenomAsRCs c = (MakeRC n, MakeRC d) 
                        where (n, d) = crSplit $ fromRC c                                         

rcNegative :: RationalSimpleCanon -> Bool
rcNegative x = crNegative $ fromRC x

rcPositive :: RationalSimpleCanon -> Bool
rcPositive x = crPositive $ fromRC x                         

---------------------------------------------------
infixl 7 %
(%) :: (Integral a) => a -> a -> a
n % m = mod n m 

infixr 9 <^

class SimpleCanonExpnt a b c | a b -> c where -- are there defaults
  (<^) :: a -> b -> c

instance SimpleCanonExpnt Integer Integer SimpleCanon where
  p <^ e = MakeC $ crExp (crFromI p) e False

instance SimpleCanonExpnt SimpleCanon Integer SimpleCanon where
  p <^ e = MakeC $ crExp (fromSC p) e False

instance SimpleCanonExpnt RationalSimpleCanon Integer RationalSimpleCanon where
  p <^ e = MakeRC $ crExp (fromRC p) e True

instance SimpleCanonExpnt RationalSimpleCanon SimpleCanon RationalSimpleCanon where
  p <^ e = MakeRC $ crExp (fromRC p) (crToI $ fromSC e) True

-------------------------------------------------------------  
infixr 9 >^ -- r >^ n means attempt to take the rth root of n

class CanonRoot a b c | a b -> c where -- are there defaults?
  (>^) :: a -> b -> c

instance CanonRoot SimpleCanon SimpleCanon SimpleCanon where
  r >^ n = MakeC $ crRoot (fromSC n) (toInteger r)
  
instance CanonRoot Integer Integer SimpleCanon where
  r >^ n = MakeC $ crRoot (crFromI n) r
  
instance CanonRoot Integer SimpleCanon SimpleCanon where
  r >^ n = MakeC $ crRoot (fromSC n) r

instance CanonRoot SimpleCanon Integer SimpleCanon where
  r >^ n = MakeC $ crRoot (crFromI n) (toInteger r)  
  
instance CanonRoot Integer RationalSimpleCanon RationalSimpleCanon where
  r >^ n = MakeRC $ crRoot (fromRC n) r
 
------------------------------------------ 
class CanonConv c where
  toSC          :: c -> SimpleCanon 
  toSimpleCanon :: c -> SimpleCanon 
  toSimpleCanon = toSC

  toRC                  :: c -> RationalSimpleCanon 
  toRationalSimpleCanon :: c -> RationalSimpleCanon
  toRationalSimpleCanon = toRC
  
------------------------------------------ 
instance CanonConv SimpleCanon where  
  toSC  c = c
  toRC c = MakeRC $ fromSC c

------------------------------------------   
instance CanonConv CR_ where  
  toSC cr | crValidIntegral cr == False = error $ invalidError 
          | otherwise                    = MakeC cr
          where invalidError = "Invalid integral canonical rep passed to constructor: " ++ (show cr) 
           
  toRC cr | crValidRational cr == False = error $ invalidRepRatioError
          | otherwise                   = MakeRC cr
          where invalidRepRatioError = "toRC: Invalid canonical rep passed to constructor: " ++ (show cr) 
  
------------------------------------------                     
instance CanonConv RationalSimpleCanon where  
  toSC rc | crValidIntegral frc == False = error $ invalidError 
          | otherwise                    = MakeC frc
          where frc          = fromRC rc
                invalidError = "Invalid integral canonical rep passed to constructor: " ++ (show rc) 
  toRC rc = rc
        