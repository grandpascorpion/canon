-- |
-- Module:      Math.NumberTheory.Canon.Additive
-- Copyright:   (c) 2015-2018 Frederick Schneider
-- Licence:     MIT
-- Maintainer:  Frederick Schneider <frederick.schneider2011@gmail.com>
-- Stability:   Provisional
--
-- Mostly functions for the addition and subtraction of CRs (Canonical Representations of numbers)

module Math.NumberTheory.Canon.Additive (
  crAdd,
  crSubtract,
  crAddR,
  crSubtractR,  
  crApplyAdtvOpt,
  crApplyAdtvOptConv,  
  crApplyAdtvOptR,
  crQuotRem 
)
where

import Math.NumberTheory.Canon.Internals
import Math.NumberTheory.Canon.AurifCyclo (crCycloAurifApply, CycloMap)

-- | Functions for computing sums and differences
crAdd, crSubtract, crAddR, crSubtractR :: CR_ -> CR_ -> CycloMap -> (CR_, CycloMap)
crAdd       = crApplyAdtvOpt  True 
crSubtract  = crApplyAdtvOpt  False
crAddR      = crApplyAdtvOptR True
crSubtractR = crApplyAdtvOptR False

-- | crApplyAdtvOptR performs addition/subtraction on two rational canons. 
{-
   Like the nonR version, we take the GCD to try to simplify the expression we need to 
   convert to an integer and back.  Here's a breakdown of the steps ...
   
                 nx      ny        nx*dy op ny*dx    nf1 op nf2
     x op y  =>  --  op  --   =>   -------------- =  ----------  => 
                 dx      dy            dx * dy        dx * dy

     ngcd * (nf1r op nf2r)     ngcd * nf     n
     --------------------  =>  --------- =>  -
           dx * dy              dx * dy      d

-}              
crApplyAdtvOptR :: Bool -> CR_ -> CR_ -> CycloMap -> (CR_, CycloMap)
crApplyAdtvOptR _     x     PZero m = (x, m)
crApplyAdtvOptR True  PZero y     m = (y, m)           -- True -> (+)
crApplyAdtvOptR False PZero y     m = (crNegate y, m)  -- False -> (-)    
crApplyAdtvOptR b     x     y     m = (crDivRational n d, m')
                                      where (nx, dx) = crSplit x
                                            (ny, dy) = crSplit y 
                                            nf1      = crMult nx dy
                                            nf2      = crMult ny dx                                
                                            ngcd     = crGCD nf1 nf2
                                            nf1r     = crDivStrict nf1 ngcd
                                            nf2r     = crDivStrict nf2 ngcd                                              
                                            (nf, m') = crApplyAdtvOpt b nf1r nf2r m -- costly bit
                                            n        = crMult ngcd nf
                                            d        = crMult dx dy  

-- | Simplify / Factorize expressions of the form: x +/- y.
crApplyAdtvOpt :: Bool -> CR_ -> CR_ -> CycloMap -> (CR_, CycloMap)
crApplyAdtvOpt _     x     PZero m = (x, m)
crApplyAdtvOpt True  PZero y     m = (y, m)           -- True -> (+)
crApplyAdtvOpt False PZero y     m = (crNegate y, m)  -- False -> (-) 
crApplyAdtvOpt b     x     y     m = (crMult gcd' r, m')
                                   where gcd'    = crGCD x y 
                                         xres    = crDivStrict x gcd'
                                         yres    = crDivStrict y gcd'
                                         (r, m') = crApplyAdtvOptConv b xres yres m -- costly bit                            
 
logThreshold :: Double
logThreshold = 10 * (log 10) -- 'n' digit number

-- | Convert different sign / operator cases in a standard manner.  All 8 combinations are covered here.
{-
  p1 + p2 => p1 + p2,     p1 - p2 => p1 - p2
  p1 + n2 => p1 - p2,     p1 - n2 => p1 + p2

  n1 + n2 => -(p1 + p2),  n1 - n2 =>  (p2 - p1) 
  n1 + p2 =>  (p2 - p1),  n1 - p2 => -(p2 + p1) 
-}  
crApplyAdtvOptConv :: Bool -> CR_ -> CR_ -> CycloMap -> (CR_, CycloMap)
crApplyAdtvOptConv b x y m 
   | gi < 2 || mL <= logThreshold 
                             = (crSimpleApply op x y, m) -- no algebraic optimization we can perform
   | crPositive x            = if crPositive y then crCycloAurifApply b       ax ay g gi m
                                               else crCycloAurifApply (not b) ax ay g gi m
   | (crNegative y) && b     = (crNegate c1, m1)
   | (crNegative y) && not b = crCycloAurifApply b ay ax g gi m
   | b                       = crCycloAurifApply (not b) ay ax g gi m
   | otherwise               = (crNegate c2, m2) 
    where op       = if b then (+) else (-)
          (ax, ay) = (crAbs x, crAbs y)
          gi       = gcd (crMaxRoot ax) (crMaxRoot ay)
          g        = crFromInteger $ fromIntegral gi
          mL       = max (crLogDouble ax) (crLogDouble ay)
          (c1, m1) = crCycloAurifApply b       ax ay g gi m
          (c2, m2) = crCycloAurifApply (not b) ax ay g gi m -- corresponds to "otherwise"

-- | Quot Rem function for CR_.  Optimization: Check first if q is a multiple of r.  If so, we avoid the potentially expensive conversion.
crQuotRem :: CR_ -> CR_ -> CycloMap -> ((CR_, CR_), CycloMap)
crQuotRem x y m = case (crDiv x y) of
                    Left  _        -> ((q,        md), m') 
                    Right quotient -> ((quotient, cr0), m)
                  where md      = crMod x y  -- Better to compute quotient this way .. to take adv. of alg. forms
                        q       = crDivStrict d y -- (x - x%y) / y. 
                        (d, m') = crSubtract x md m
