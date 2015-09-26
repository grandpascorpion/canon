{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns    #-}

module AurifCyclo (
  aurCandDec, 
  aurCandDecCr,
  aurCandDec',
  aurDecCr,
  aurDec,
  crCycloAurifApply',
  applyCrCycloPair,
  applyCycloPair,
  cyclo,
  cycloDivSet,
  chineseAurif,
  chineseAurifCr  
)
where

import CanonInternals
import Math.NumberTheory.Primes.Factorisation (totient)
import Math.NumberTheory.Moduli (jacobi)
import Data.Array(array, (!), Array(), elems) -- to do: convert to unboxed? https://wiki.haskell.org/Arrays
import GHC.Real (numerator, denominator)
import Math.Polynomial( Poly(), poly, multPoly, quotPoly, Endianness(..), polyCoeffs)
import Data.List (sortBy, (\\))
import qualified Data.Map as M

--import Debug.Trace(trace)

cr2 :: CR_
cr2 = crFromI 2

-------------------------------------------
if' :: Bool -> a -> a -> a
if' True  x _ = x
if' False _ y = y
-------------------------------------------

crCycloAurifApply' :: Bool -> CR_ -> CR_ -> CR_ -> Integer -> CR_
--crCycloAurifApply' b x y g gi | trace ("crCycloAurifApply' trace: Processing b = " ++ (show b) ++ ", x = " ++ (show x) ++ 
--                                ", y = " ++ (show y) ++ ", g = " ++ (show g) ++ ", gi = " ++ (show gi)) False = undefined   
crCycloAurifApply' b x y g gi
   -- Optimization for prime g: If g is a prime (and exp not of from x^2 + y^2) but not Aurifeullian (verify 
  | (crPrime g) && not (g == cr2 && b) 
                     = enrApply' [term1, termNM1] -- split into  (x +/- y) and (x^(n-1) ... -/+ y^(n-1))  

   -- Factorize: grtx^g - grty^g via cyclotomic polynomials                     
  | not b            = enrApply' (cycA grtx grty g)  

   -- Factorize x^n + y^n using cyclotomic polynomials (if n = 2^x*m where x >= 0 and m > 2)
  | b && not gpwr2   = enrApply' (cycA (oddRoot x) (-1 * oddRoot y) odd')

  | otherwise        = crSimpleApply op x y
  where op           = if' b (+) $ (-)
        ((gp, _):gs) = g
        gpwr2        = (gp == 2 && gs == [])                      
        gth_root v   = crToI $ crRoot v gi
        grtx         = gth_root x
        grty         = gth_root y
        
        -- used when factoring x^p +/- 1 where p is prime
        term1        = integerApply op (crRoot x gi) (crRoot y gi) -- a +/- b
        termNM1      = div (integerApply op x y) term1  -- divide a^g +/- b^g by the term above

        cycA x' y' n = applyCrCycloPair x' y' n
        enrApply' a  = foldr1 crMult (map crFromI $ vSet)              
                       where vSet = case (aurCandDec' x y gi g b) of
                                          Nothing       -> augList a   -- can't do anything Brent Aurif-wise, try Chinese method
                                          Just (a1, a2) -> augList (divvy a a1 a2) -- meld in the 2 Aurif factors with input array

        odd'         = if' (gp == 2) (tail g) $ g  -- grabs number sans any power of 2
        oddRoot v    = crToI $ crRoot v (crToI odd')

        augList al   = case chineseAurifCr x y b of
                         Nothing       -> al             -- just return what was passed in
                         Just (a3, a4) -> divvy al a3 a4 -- additional "Chinese" factors
                        
--Identity: x^n -1 = product of cyclo d where d | n.  This function will return cyclo n itself
-- e.g. 2 * 5^3 return (5, 2 * 5^2

{-
The following functions implement Richard Brent's algorithm for computing Aurifeullian factors.
His logic is used in conjuction with cyclotomic polynomial decomposition.

http://maths-people.anu.edu.au/~brent/pd/rpb127.pdf
http://maths-people.anu.edu.au/~brent/pd/rpb135.pdf

-}

-- Assumptions: x and y are relatively prime and g is a positive integral CR.
-- if it's an aurif candidate for decomposition, split it into two and evaluate it otherwise return nothing
aurCandDec :: Integer -> Integer -> Bool ->  Maybe (Integer, Integer)
aurCandDec xi yi b | (crGCD x y) == cr1 = aurCandDecCr x y b
                   | otherwise          = error "aurCandDec: The first two parameters must be relatively prime to call the underlying function"
                   where x = crFromI xi
                         y = crFromI yi

aurCandDecCr :: CR_ -> CR_ -> Bool ->  Maybe (Integer, Integer)
aurCandDecCr x y b | (crGCD x y) == cr1 = aurCandDec' x y n cr b      
                   | otherwise          = error "aurCandDecCr: The first two parameters must be relatively prime to call the underlying function"                                                                       
                   where n  = gcd (crMaxRoot x) (crMaxRoot y)
                         cr = crFromInteger $ fromIntegral n

-- add case where: a^(da) +/- 1
aurCandDec' :: CR_ -> CR_ -> Integer -> CR_ -> Bool -> Maybe (Integer, Integer)
--aurCandDec' x y n cr b| trace ("aurCandDec' trace: Processing x = " ++ (show x) ++ ", y = " ++ (show y) ++ 
--                               ", n = " ++ (show n) ++ " =  cr = " ++ (show cr) ++ ", b = " ++ (show b)) False = undefined     
aurCandDec' x y n cr b| (nm4 == 1 && b) || (nm4 /= 1 && not b) ||
                        (xdg == x && ydg == y)  || (m /= 0)
                                        = Nothing -- 
                      | otherwise       = case (aurDec' n' cr') of
                                                Nothing             -> Nothing
                                                Just (gamma, delta) -> apply gamma delta
                                     
                      where -- override of n, to attempt decomp for g = gcd when number of form: g^gd +/-1, 
                            -- this will only work when either x or y = 1 and not for any other divisor of g.  
                            -- If both terms are not 1, we just attempt an Aurif. decomp for n
  
-- need to integrate chineseAurif, it does something different                          
                            (n', cr')  = if (x /= cr1 && y /= cr1) then (n, cr) else (gcd1i, gcd1)
                                         where x1    = if (y /= cr1) then y else x
                                               gcd1  = crRadical $ crGCD x1 cr 
                                               gcd1i = crToI gcd1    
                                                                                           
                            nm4         = mod n' 4   
                              
                            divTry a    = case crDiv a (crExp cr' n' False) of -- check to divide by n^n, if not return original
                                                        Left _         -> a 
                                                        Right quotient -> quotient
                            xdg         = divTry x
                            ydg         = divTry y
                            mrGCD       = gcd (crMaxRoot xdg) (crMaxRoot ydg)
                            m           = mod mrGCD (2*n')

                            -- need to consider cyclotomic translations, order the terms                        
                            (x', ml)    | ydg /= y  = ( (crDivRational ydg x), if (not b) then (-1) else 1)
                                        | otherwise = ( (crDivRational xdg y), 1);                                        
                                            
                            {-
                                The more familar form of the below is (C(x)^2 - nxD(x)^2):
                                     gm(x)^2 -nx*dt(x)^2 => 
                                     gamma +/- sqrt(nx) * delta
                            -}
                                                            
                            xrtn        = crMult cr' (crRoot x' n')
                            xrtnr       = crToRational xrtn
                            sqrtnxr     = crToRational $ crRoot (crMult cr' xrtn) 2

                            apply gm dt = Just (ml * numerator (f1), numerator (f2))
                                          where f1 = c - sqrtnxr * d
                                                f2 = c + sqrtnxr * d
                                                c  = applyArray gm xrtnr
                                                d  = applyArray dt xrtnr     
                                                                                
-- Example Aurif. decomp: C5(x) = x^2 + 3x + 1, D5(x) = x + 1 => Cyclotomic5(x) = C5(x)^2 − 5x*D5(x)^2                                                                                                 

-- return a pair of polynomials (in array form) or Nothing (if it's squareful.)
aurDec :: Integer -> Maybe (Array Integer Integer, Array Integer Integer)
aurDec n | n <= 1    = error "aurifDecomp: n must be greater than 1"
         | otherwise = aurDec' n (crFromI n)
 
aurDecCr :: CR_ -> Maybe (Array Integer Integer, Array Integer Integer)                
aurDecCr cr = aurDec (crToI cr)

moebius :: CR_ -> Integer
moebius cr = if (crHasSquare cr) then 0 :: Integer else (if ((mod (length cr) 2) == 1) then (-1) else 1)

cosine' :: Integer -> Integer
cosine' n | m8 == 2 || m8 == 6 = 0
          | m8 == 4            = -1
          | m8 == 0            = 1
          | otherwise          = error $ cosError
            where m8       = mod n 8
                  cosError = "Logic error: bad/odd value passed to cosine': " ++ (show n)

aurDec' :: Integer -> CR_ -> Maybe (Array Integer Integer, Array Integer Integer) 
--aurDec' n cr| trace ("aurDec' trace: Processing " ++ (show n) ++ " => " ++ (show cr)) False = undefined
aurDec' n cr| crHasSquare cr || n < 2 || n' < 2
                         = Nothing
            | otherwise  = Just (gamma, delta)
               where nm4 = mod n 4   
                     n'  = if (nm4 == 1) then n else (2*n)
                     d   = div (totient n') 2
                     dm2 = mod d 2
                     
                     -- max gamma and delta subscripts to explicitly compute (add'l terms come from symmetry)
                     mg  = if (dm2 == 1) then (div (d-1) 2) else (div d     2)
                     md  = if (dm2 == 1) then (div (d-1) 2) else (div (d-2) 2)
                                              
                     -- create q array of size td2: q(2k+1) = jacobi n (2k+1),  q(2k+2  = mn * totient (2k+2)
                     q   = array (1, d) ([(i, 
                                          if (mod i 2 == 1) then (toInteger $ jacobi n i) else (eQ n i))| i <- [1..d]])                                                                                               
                           where eQ nr i = moebius (crFromI (div n' g)) * (totient g) * (cosine' ((nr-1)*i))                     
                                           where g = gcd n' i                                                                

                     gamma  = array (0, d) ([(0,1)] ++ [(i, gf i) | i <- [1..d]]) 
                              where gf k    = if (k > mg) then (gamma!(d-k)) 
                                                          else (div (gTerm k) (2*k))
                                    gTerm k = sum (map (\j -> n * q!(2*k-2*j-1) * delta!j - q!(2*k-2*j) * gamma!j) 
                                                       [0..k-1])
                                        
                     delta  = array (0, d-1) ([(0,1)] ++ [(i, df i) | i <- [1..d-1]])              
                              where df k    = if (k > md) then (delta!(d-k-1)) 
                                                              else (div (dTerm k) (2*k+1))
                                    dTerm k = gamma!k + 
                                              sum (map (\j -> q!(2*k-2*j+1) * gamma!j - q!(2*k-2*j) * delta!j) 
                                                       [0..k-1])

                    {- Compute gammas G and deltas D 
                       G(0) = 1
                       D(0) = 1

                       Evaluate G(k) for 1 .. floor(d/2)
                       G(k) = (1/2k) * sum(n*q(2k-2j-1)*D(j) - q(2k-2j)G(j)) [for j= 0 to k-1)

                       Evaluate D(k) for 1 .. floor(d-1/2)
                       D(k) = (1/2k+1) * ( G(k) + sum(q(2k+1-2j)*D(j) - q(2k-2j)D(j)) )

                       Evaluate G(k) for (floor(d/2)+1) to d => G(k) = G(d-k)
                       Evaluate D(k) for (floor(d+1/2)) to d-1 => D(k) = D(d-k)    
                       
                       Cyc(n) = C(x)^2 -nxD(x)^2 where gamma and delta are the coeffs for C(x) and D(x) respectively                               
                    -} 

-- array/lists are treated like polynomials (zero-base assumed)        
applyArray :: Array Integer Integer -> Rational -> Rational
applyArray a x    = applyList (elems $ a) 1 0 x

applyList :: [Integer] -> Rational -> Rational -> Rational -> Rational
applyList l m a x = if (l == []) then a else (applyList (tail l) (m*x) (a + (toRational (head l))*m) x)  

-----------------------------------------------------------------------
-- Pass two (Aurif) integers to an array of integers.  The product of the integers
-- must be a divisor of the array product otherwise an error will be returned
-- It's called divvy because it splits the 2 integers across the array using the gcd.
-- This will help factoring because the larger term(s) will be broken up into smaller pieces

divvy :: [Integer] -> Integer -> Integer -> [Integer]
--divvy a x y | trace ("divvy trace: Processing a = " ++ (show a) ++ ", x = " ++ (show x) ++ ", y =  " ++ (show y)) False = undefined     
divvy a x y = divvy' (sortBy rev a) (abs x) (abs y) 
              where rev a' b' = if (a' > b') then LT else GT    
       
divvy' :: [Integer] -> Integer -> Integer -> [Integer]                        
divvy' []     x y  | x == 1 && y == 1             = []
                   | (abs x) == 1 && (abs y) == 1 = [x*y]
                   | otherwise                    = error "Empty list but x and y weren't both 1"
divvy' (c:cs) x y  = if (x == 1 && y == 1) then (c:cs) else (v ++ divvy' cs (div x gnx) (div y gny))
                     where v   = filter (>1) $ [div q gny, gnx, gny]
                           gnx = gcd c x
                           q   = div c gnx
                           gny = gcd q y 
{-                
Test: Run divvy on this:
let x = 50031545486420197
let y = 50031544711579219
let a = [4,7,8401,62324358089100907319521,682969,61,374857981681,547]                        
-} 
-----------------------------------------------------------------------

{-
Cyclotomic factorizations for numbers of the form x^n +/- y^n

Example:
x^15-y^15 = (x-y) (x^2+x y+y^2) (x^4+x^3 y+x^2 y^2+x y^3+y^4) (x^8-x^7*y +x^5*y^3 - x^4*y^4 +x^3*y^5 -x*y^7+y^8)

C(15) is a form of the last term where y = 1

It's possible in some cases to do an additional Aurifeullian factorization (of the last term).
-}

type CycloPair = (Integer, Poly Float)
type CycloMap  =  M.Map CR_ CycloPair

-- create a starting map with the cyclo polynomials for 1 and 2
crCycloInitMap :: CycloMap
crCycloInitMap = M.insert cr1 (1, poly LE ([-1.0, 1.0] :: [Float])) M.empty

-- first I start with a map of one to one
-- then I check the radical and return the map: crCycloRad
-- if the cr doesn't equal the radical then I open it up to the other factors and the square free factors must be in the map
cyclo :: Integer -> CycloPair
cyclo n       = crCyclo       $ crFromI n

cycloDivSet :: Integer -> CycloMap
cycloDivSet n = crCycloDivSet $ crFromI n


-- return pair of expon. multiplier and radical's polynomial. 
crCyclo :: CR_ -> CycloPair
crCyclo cr | crPositive cr = (crToI (crDivStrict cr r), snd pr) 
           | otherwise     = error "cyclo: Positive integer needed"
           where r         = crRadical cr
                 (pr, _)   = crCycloRad r crCycloInitMap           

crCycloDivSet :: CR_ -> CycloMap
crCycloDivSet cr | crPositive cr = m
                 | otherwise     = error "cycloDivSet: Positive integer needed" 
                 where (_, m)    = crCyclo' cr crCycloInitMap

crCyclo' :: CR_ -> CycloMap -> (CycloPair, CycloMap)
crCyclo' cr m = case M.lookup cr m of 
                  Nothing       -> crCycloPre cr m -- need to compute it
                  Just p        -> (p, m)          -- found it

crCycloPre :: CR_ -> CycloMap -> (CycloPair, CycloMap)
crCycloPre cr m | r == cr       = (pr, pm)
                | otherwise     = crCycloMFN sqFulDivs pm
                where r         = crRadical cr
                      (pr, pm)  = crCycloRad r m
                      sqFulDivs = crDivisors cr \\ crDivisors r

crCycloMFN :: [CR_] -> CycloMap -> (CycloPair, CycloMap)     
crCycloMFN  (n:ns) m = if (ns == []) then (c, m') else (crCycloMFN ns m') where (c, m') = crCycloAll n m
crCycloMFN  []     _ = error "Bad value passed to crCycloMFN. Empty list forbidden" 

-- compute the "radical" divisors first and then the non-square free entries
crCycloRad :: CR_ -> CycloMap -> (CycloPair, CycloMap)
crCycloRad cr m = case M.lookup cr m of 
                  Nothing -> crCycloRad' cr m -- need to compute it
                  Just p  -> (p, m)           -- found it

crCycloRad' :: CR_ -> CycloMap -> (CycloPair, CycloMap)
crCycloRad' cr m | cs == []  = (cycpr, M.insert cr cycpr m)           
                 | otherwise = (cyc_n, M.insert cr cyc_n mp)
                 where (_ : cs)         = cr
                       -- for primes  
                       r                = fromInteger $ crToI $ crRadical cr                         
                       cycpr            = (1, poly LE (replicate r 1.0)) --prime 
                       -- for composites
                       xNm1             = poly LE ( (-1.0:(replicate (r-1) 0.0) ++ [1.0]) :: [Float] ) -- create poly of form: x^n -1
                       (cPrd, mp)       = crCycloMemoFold (init $ crDivisors cr) m
                       cyc_n            = (1, quotPoly xNm1 cPrd)

-- cycloMemoFold* takes a list of divisors and returns the pair: (cyclotomic product, memoized map)
crCycloMemoFold :: [CR_] -> CycloMap -> (Poly Float, CycloMap)
crCycloMemoFold  (n:ns) m   = crCycloMemoFold' ns (snd c) m'  where (c, m') = crCycloRad n m
crCycloMemoFold  []     _   = error "Logic error: Blank list can't be passed to crCycloMemoFold" 

crCycloMemoFold' :: [CR_] -> Poly Float -> CycloMap -> (Poly Float, CycloMap)
crCycloMemoFold' (n:ns) p m = crCycloMemoFold' ns (multPoly p (snd c)) m' 
                              where (c, m') = crCycloRad n m
crCycloMemoFold' []     p m = (p, m)

crCycloAll :: CR_ -> CycloMap -> (CycloPair, CycloMap)
--crCycloAll cr m | trace ("  crCycloAll trace: Processing " ++ (show cr) ++ " and " ++ (show m)) False = undefined  
crCycloAll cr m | p == cr1          = case M.lookup cr m of 
                                         Nothing -> error "Logic error: Radical value not found for crCycloAll"
                                         Just cb -> (cb, m)         -- found it                
                | otherwise         = (crp, M.insert cr crp md)
                where (p, d)        = crPullSq cr
                      (cd, md)      = case M.lookup d m of 
                                      Nothing -> crCycloAll d m -- need to compute it
                                      Just c  -> (c, m)          -- found it                
                      -- Optimization: (1, x + 1) => (4, x + 1) 
                      -- fst value is the exponential multiplier C8(x) = C2(x^4) = x^2 + 1
                      crp           = ((fst (head p)) * (fst cd), snd cd) 

crPullSq :: CR_ -> (CR_, CR_)
crPullSq  cr       = crPullSq' [] cr

crPullSq' :: CR_ -> CR_ -> (CR_, CR_)
crPullSq' h []     = (cr1, h)
crPullSq' h (c:cs) = if (ce > 1) then ([(cp, 1)], h ++ (cp, ce-1):cs) else (crPullSq' (h ++ [c]) cs)
                     where (cp, ce) = c

applyCrCycloPair :: Integer -> Integer -> CR_ -> [Integer]
applyCrCycloPair l r cr = applyCrCycloPair' l r cr cds
                          where cds = M.elems $ crCycloDivSet cr

applyCrCycloPair' :: Integer -> Integer -> CR_ -> [CycloPair] -> [Integer]
--applyCrCycloPair' l r cr cds | trace ("  applyCrCycloPair' trace: Processing " ++ (show l) ++ " -> " ++ (show r) ++ 
--                                      " -> " ++ (show cr) ++ " -> " ++ (show cds)) False = undefined                           
applyCrCycloPair' l r cr cds        = map applyPoly cds
                 where nd           = crTotient cr
                       pA v         = a where a = array (0,nd) ([(0,1)] ++ [(i, v*a!(i-1)) | i <- [1..nd]]) -- array of powers
                       lpa          = pA l
                       rpa          = pA r
                       applyPoly pp = foldr1 (+) 
                                             (map (\x -> if' (fst x == 0) 0 $ 
                                                             (fst x) * (lpa!(mult*(snd x)) * rpa!(mult*(maxExp - snd x))) )
                                             (zip fmtdCy [0..]))
                                      where mult   = fst pp
                                            fmtdCy = map ceiling (polyCoeffs LE (snd pp)) -- format poly from mult poly pair
                                            maxExp = toInteger $ length fmtdCy - 1

applyCycloPair :: Integer -> Integer -> Integer -> [Integer]                  
applyCycloPair x y e = applyCrCycloPair x y (crFromI e)

{- to do: update this: small change
showCyclo n b = showC $ map ceiling (polyCoeffs LE (crCyclo n))

-- "LE" endianness is assumed here
showC (c:cs) = (show c) ++ (showC' cs (1 :: Int))
showC _      = []

showC' (c:cs) s = if' (c == 0) (showC' cs (s+1)) $ h ++ (showC' cs (s+1))
                  where h = (if' (c > 0) " + " $ " - ") ++ (if' ((abs c) == 1) "" $ (show (abs c))) ++
                            "x" ++ (if' (s == 1) "" $ "^" ++ (show s))
showC' _      _ = []
-}

-- all the exponents must be even to return True
crSquareFlag :: CR_ -> Bool
crSquareFlag POne         = True
crSquareFlag ((_, ce):cs) = if (mod ce 2 == 1) then False else (crSquareFlag cs)
crSquareFlag _            = error "Logic error in crSquareFlag.  Pattern match should have been exhaustive"

chineseAurif :: Integer -> Integer -> Bool -> Maybe (Integer, Integer)
chineseAurif   x   y   b = chineseAurifCr (crFromI x) (crFromI y) b

chineseAurifCr :: CR_ -> CR_ -> Bool -> Maybe (Integer, Integer)
chineseAurifCr xcr ycr b = case chineseAurif' mbcrxy n mcrxy (crToI mcrxy) b of
                             Nothing       -> chineseAurif' mbcryx n mcryx (crToI mcryx) b 
                             Just (n1, n2) -> Just (n1, n2)
                           where n           = gcd (crMaxRoot xcr) (crMaxRoot ycr)  
                                 ncr         = crFromI n                         
                                 mbcrxy      = crRoot (crDivRational xcr ycr) n
                                 mcrxy       = crGCD (crNumer mbcrxy)  ncr   
                                                    
                                 mbcryx      = crRecip mbcrxy
                                 mcryx       = crGCD (crNumer mbcryx) ncr  
                                
-- go through the divisors of n, stop when you find a match (what about squares)


{-
The source for this algorithm is the paper by
Sun Qi, Ren Debin, Hong Shaofang, Yuan Pingzhi and Han Qing:

http://www.jams.or.jp/scm/contents/Vol-2-3/2-3-16.pdf

The formula at 2.7 there is implemented below.

This will handle a subset of the cases that the main Aurif. routines handle
-}

-- find factor of mb^n +/- 1 (mb would be M from paper, mb meaning m "big"
chineseAurif' :: CR_ -> Integer -> CR_ -> Integer -> Bool -> Maybe (Integer, Integer) -- to fix
--chineseAurif' mbcr n mcr m b| trace ("chineseAurif' trace: Processing p1 = " ++ (show mbcr) ++ ", p2 = " ++ (show n) ++ 
--                               ", p3 = " ++ (show mcr) ++ ", p4 = " ++ (show m) ++ ", p5 = " ++ (show b)) False = undefined     
chineseAurif' mbcr n mcr m b | mod n 2 == 0        || mod m 2 == 0 ||          -- n and m must both be odd
                               m < 3               || km /= 0      ||          -- m must be odd and > 1 and m | n
                               (mm4 == 1 && b)     || -- sign and modulus
                               (mm4 == 3 && not b) || -- must be in synch           
                               mbdm == cr0         || not (crSquareFlag mbdm)  -- mb/m must be a square and integral
                                         = Nothing
                             | otherwise = case cv - (gd1 * gd2) of
                                             0 -> Just (gd1, gd2)
                                             _ -> Nothing -- additional check since paper doesn't indicate rationals are supported
                                         where mm4     = mod m 4
                                               e       = toRational $ if (mm4 == 3) then (-1) else mm4
                                               (k, km) = quotRem n m
                                               mbdm    = case (crDiv mbcr mcr) of
                                                              Left  _ -> cr0 -- error condition if not a multiple
                                                              Right q -> q
                                               r       = crToRational $ crRoot (crMult mbcr mcr) 2 -- sqrt (m*M) from paper
                                               mb      = crToRational mbcr
                                               jR c    = toRational $ jacobi c m 
                                               eM      = e * mb
                                               v1      = (toRational m) * mb^(div (k * (m + 1)) 2)
                                               v2      = t * s
                                                         where t = (jR 2) * r * (mb ^ (div (k-1) 2))
                                                               s = sum $ map (\c -> (jR c) * eM^(k*c)) 
                                                                       $ filter (\c -> gcd c m == 1) [1..m] -- rel. prime
                                               delta1  = numerator $ v1 - v2
                                               delta2  = numerator $ v1 + v2
                                               eMn     = numerator   $ eM
                                               eMd     = denominator $ eM
                                               ncr     = crFromI n
                                               cv      = head $ 
                                                         applyCrCycloPair' eMn eMd ncr [crCyclo ncr] -- get cyclotomic value                                            
                                               gd1     = gcd cv delta1
                                               gd2     = gcd cv delta2