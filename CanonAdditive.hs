module CanonAdditive (
  crAdd,
  crSubtract,
  crAddR,
  crSubtractR,  
  crApplyAdtvOpt,
  crApplyAdtvOpt',  
  crApplyAdtvOptR,
  crQuotRem 
)
where

--import Debug.Trace (trace) -- remove
import CanonInternals
import AurifCyclo (crCycloAurifApply')

crAdd :: CR_ -> CR_ -> CR_
crAdd x y = crApplyAdtvOpt True x y

crSubtract :: CR_ -> CR_ -> CR_
crSubtract x y = crApplyAdtvOpt False x y

crAddR :: CR_ -> CR_ -> CR_
crAddR x y = crApplyAdtvOpt True x y

crSubtractR :: CR_ -> CR_ -> CR_
crSubtractR x y = crApplyAdtvOptR False x y


-------------------------------------------
if' :: Bool -> a -> a -> a
if' True  x _ = x
if' False _ y = y
-------------------------------------------
  
{- crApplyAdtvOptR performs addition/subtraction on two rational canons. 
 
   Like the nonR version, we take the GCD to try to simplify the expression we need to 
   convert to an integer and back.  Here's a breakdown of the steps ...
   
                 nx      ny        nx*dy op ny*dx    nf1 op nf2
     x op y  =>  --  op  --   =>   -------------- =  ----------  => 
                 dx      dy            dx * dy        dx * dy

     ngcd * (nf1r op nf2r)     ngcd * nf     n
     --------------------  =>  --------- =>  -
           dx * dy              dx * dy      d

-}              
crApplyAdtvOptR :: Bool -> CR_ -> CR_ -> CR_ 
crApplyAdtvOptR _     x     PZero = x
crApplyAdtvOptR True  PZero y     = y           -- True -> (+)
crApplyAdtvOptR False PZero y     = crNegate y  -- False -> (-)    
crApplyAdtvOptR b     x     y     = crDivRational n d
                                    where (nx, dx) = crSplit x
                                          (ny, dy) = crSplit y 
                                          nf1      = crMult nx dy
                                          nf2      = crMult ny dx                                
                                          ngcd     = crGCD nf1 nf2
                                          nf1r     = crDivStrict nf1 ngcd
                                          nf2r     = crDivStrict nf2 ngcd                                              
                                          nf       = crApplyAdtvOpt' b nf1r nf2r -- costly bit
                                          n        = crMult ngcd nf
                                          d        = crMult dx dy  

---------------------------------------------------------------
---------------------------------------------------------------
-- Finally, we have the logic used simplify/factorise expressions x +/- y
----------------------------------------------
crApplyAdtvOpt :: Bool -> CR_ -> CR_ -> CR_ 
--crApplyAdtvOpt b x y | trace ("  crApplyAdtvOpt trace: Processing " ++ (show b) ++ " -> " ++ (show x) ++ " -> " ++ (show y)) False = undefined     

crApplyAdtvOpt _     x     PZero = x
crApplyAdtvOpt True  PZero y     = y           -- True -> (+)
crApplyAdtvOpt False PZero y     = crNegate y  -- False -> (-) 
crApplyAdtvOpt b     x     y     = crMult gcd' r
                                   where gcd' = crGCD x y 
                                         xres = crDivStrict x gcd'
                                         yres = crDivStrict y gcd'
                                         r    = crApplyAdtvOpt' b xres yres -- costly bit                            
 
logThreshold :: Double
logThreshold = 10 * (log 10) -- 'n' digit number

{-
  crApplyAdtvOpt' is setup to deal with positive numbers.  All 8 combinations of signs and operators are here
  p1 + p2 => p1 + p2,     p1 - p2 => p1 - p2
  p1 + n2 => p1 - p2,     p1 - n2 => p1 + p2

  n1 + n2 => -(p1 + p2),  n1 - n2 =>  (p2 - p1) 
  n1 + p2 =>  (p2 - p1),  n1 - p2 => -(p2 + p1) 
-}  

crApplyAdtvOpt' :: Bool -> CR_ -> CR_ -> CR_ 
--crApplyAdtvOpt' b x y | trace ("  crApplyAdtvOpt' trace: Processing " ++ (show b) ++ " -> " ++ (show x) ++ " -> " ++ (show y)) False = undefined     
crApplyAdtvOpt' b x y 
   | gi < 2 || mL <= logThreshold 
                             = crSimpleApply op x y -- no algebraic optimization we can perform
   | crPositive x            = if' (crPositive y) (crCycloAurifApply' b       x y         g gi) $    
                                                  (crCycloAurifApply' (not b) x (crAbs y) g gi)
   | (crNegative y) && b     = crNegate $ crCycloAurifApply' b (crAbs x) (crAbs y) g gi
   | (crNegative y) && not b = crCycloAurifApply' b (crAbs y) (crAbs x) g gi
   | b                       = crCycloAurifApply' (not b) y (crAbs x) g gi
   | otherwise               = crNegate $ crCycloAurifApply' (not b) (crAbs x) y g gi
   
    where op = if' (b) (+) $ (-)
          gi = gcd (crMaxRoot x) (crMaxRoot y)
          g  = crFromInteger $ fromIntegral gi
          mL = max (crLogDouble $ crAbs x) (crLogDouble $ crAbs y)


-- Optimization: Check first if q is a multiple of r.  If so, we avoid the potentially expensive conversion
crQuotRem :: CR_ -> CR_ -> (CR_, CR_)
crQuotRem x y = case (crDiv x y) of
                  Left  _        -> (q,        m)
                  Right quotient -> (quotient, cr0)
                  where m = crMod x y  -- Better to compute quotient this way .. to take adv. of alg. forms
                        q = crDivStrict (crSubtract x m) y -- (x - (x%y)) / y. 
