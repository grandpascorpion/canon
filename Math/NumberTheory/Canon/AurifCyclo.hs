-- |
-- Module:      Math.NumberTheory.Canon.AurifCyclo
-- Copyright:   (c) 2015-2018 Frederick Schneider
-- Licence:     MIT
-- Maintainer:  Frederick Schneider <frederick.schneider2011@gmail.com>
-- Stability:   Provisional
--
-- Aurifeullian and Cyclotomic factorization method functions.

{-# LANGUAGE PatternSynonyms, ViewPatterns #-}

module Math.NumberTheory.Canon.AurifCyclo (
  aurCandDec,     
  aurDec,         
  applyCycloPair, applyCycloPairWithMap,
  cyclo,          cycloWithMap,
  cycloDivSet,    cycloDivSetWithMap,
  chineseAurif,   chineseAurifWithMap, 

  crCycloAurifApply, applyCrCycloPair, divvy,
  CycloMap, fromCycloMap, fromCM, showCyclo, crCycloInitMap
)
where

import Math.NumberTheory.Canon.Internals
import Math.NumberTheory.Moduli.Jacobi (JacobiSymbol(..), jacobi)
import Data.Array (array, (!), Array(), elems) -- to do: convert to unboxed? https://wiki.haskell.org/Arrays
import GHC.Real (numerator, denominator)
import Math.Polynomial( Poly(), poly, multPoly, quotPoly, Endianness(..), polyCoeffs)
import Data.List (sort, sortBy, (\\))
import qualified Data.Map as M

-- CR_ Rep of 2
cr2 :: CR_
cr2 = crFromI 2

-- | This function checks if the inputs along with operator flag have a cyclotomic or Aurifeuillian form to greatly simplify factoring.
--   If they do not, potentially much more expesive simple factorization is used via crSimpleApply.
--   Note: The cyclotomic map is threaded into the functions
crCycloAurifApply :: Bool -> CR_ -> CR_ -> CR_ -> Integer -> CycloMap -> (CR_, CycloMap)
crCycloAurifApply b x y g gi m
   -- Optimization for prime g: If g is a prime (and exp not of from x^2 + y^2) but not Aurifeullian (verify 
  | (crPrime g) && not (g == cr2 && b) 
                     = eA ([term1, termNM1], m) -- split into  (x +/- y) and (x^(n-1) ... -/+ y^(n-1))  

   -- Factorize: grtx^g - grty^g via cyclotomic polynomials                     
  | not b            = eA (cycA grtx grty g)  

   -- Factorize x^n + y^n using cyclotomic polynomials (if n = 2^x*m where x >= 0 and m > 2)
  | b && not gpwr2   = eA (cycA (oddRoot x) (-1 * oddRoot y) odd') 

  | otherwise        = (crSimpleApply op x y, m)
  where op            = if b then (+) else (-)
        ((gp, _):gs)  = g
        gpwr2         = gp == 2 && gs == []                      
        gth_root v    = crToI $ crRoot v gi
        grtx          = gth_root x
        grty          = gth_root y
        
        -- used when factoring x^p +/- 1 where p is prime
        term1         = integerApply op (crRoot x gi) (crRoot y gi) -- a +/- b
        termNM1       = div (integerApply op x y) term1  -- divide a^g +/- b^g by the term above

        cycA x' y' n  = (sort ia, m') -- sort the integers returned from low to high, should help if there are larger terms
                        where (ia, m') = applyCrCycloPair x' y' n m
        eA (a,mp)     = (foldr1 crMult $ map crFromI v, m') -- eA stands for "enriched apply"
                        where (v, m')   = case aurCandDecI x y gi g b of
                                            Nothing       -> auL a mp  -- can't do anything Brent Aurif-wise, try Chinese method
                                            Just (a1, a2) -> auL (divvy a a1 a2) mp -- meld in the 2 Aurif factors with input array
                              auL al ma = case c of -- aL stands for "augmented list)
                                            Nothing       -> (al, mp')             -- just return what was passed in
                                            Just (a3, a4) -> (divvy al a3 a4, mp') -- additional "Chinese" factors
                                          where (c, mp') = chineseAurifCr x y b ma 

        odd'          | gp == 2   = tail g  -- grabs number sans any power of 2
                      | otherwise = g
        oddRoot v     = crToI $ crRoot v (crToI odd')
                        
{-
The following functions implement Richard Brent's algorithm for computing Aurifeullian factors.
His logic is used in conjuction with cyclotomic polynomial decomposition.

http://maths-people.anu.edu.au/~brent/pd/rpb127.pdf
http://maths-people.anu.edu.au/~brent/pd/rpb135.pdf
-}

-- | This function checks if the input is a candidate for Aurifeuillian decomposition.
--   If so, split it into two and evaluate it.  Otherwise, return nothing.
--   The code will "prep" the input params for the internal function so they will be relatively prime.
aurCandDec :: Integer -> Integer -> Bool -> Maybe (Integer, Integer)
aurCandDec xi yi b = f (crFromI xi) (crFromI yi)
                     where f xp yp = aurCandDecI x y n (crFromI n) b 
                                     where n      = gcd (crMaxRoot $ crAbs x) (crMaxRoot $ crAbs y)
                                           gxy    = crGCD xp yp 
                                           (x, y) = (crDivStrict xp gxy, crDivStrict yp gxy) -- this will fix the input to be relatively prime

-- Don't call this I(nternal) function directly.  The function assumes that x and y are relatively prime.  Currently uses Brent logic only.
aurCandDecI :: CR_ -> CR_ -> Integer -> CR_ -> Bool -> Maybe (Integer, Integer)
aurCandDecI x y n cr b| (nm4 == 1 && b) || (nm4 /= 1 && not b) ||
                        (xdg == x && ydg == y)  || (m /= 0)
                                        = Nothing -- 
                      | otherwise       = case aurDecI n' cr' of
                                            Nothing             -> Nothing
                                            Just (gamma, delta) -> apply gamma delta
                      where                
                            -- override of n, to attempt decomp for g = gcd when number of form: g^gd +/-1, 
                            -- this will only work when either x or y = 1 and not for any other divisor of g.  
                            -- If both terms are not 1, we just attempt an Aurif. decomp for n
  
                            -- TODO: Need to integrate chineseAurif as it does something different                          
                            (n', cr') | x /= cr1 && y /= cr1 = (n, cr) 
                                      | otherwise            = (gcd1i, gcd1)
                                      where x1    = if y /= cr1 then y else x
                                            gcd1  = crRadical $ crGCD x1 cr 
                                            gcd1i = crToI gcd1    
                            nm4       = mod n' 4   
                            divTry a  = case crDiv a (crExp cr' n' False) of -- check to divide by n^n, if not return original
                                          Left _         -> a 
                                          Right quotient -> quotient
                            xdg       = divTry x
                            ydg       = divTry y
                            mrGCD     = gcd (crMaxRoot $ crAbs xdg) (crMaxRoot $ crAbs ydg)
                            m         = mod mrGCD (2*n')

                            -- need to consider cyclotomic translations, order the terms                        
                            (x', ml)  | ydg /= y  = ( (crDivRational ydg x), if (not b) then (-1) else 1)
                                      | otherwise = ( (crDivRational xdg y), 1);                                        
                                            
                            {-  The more familar form of the below is (C(x)^2 - nxD(x)^2):
                                     gm(x)^2 -nx*dt(x)^2 => 
                                     gamma +/- sqrt(nx) * delta     -}
                            xrtn      = crMult cr' (crRoot x' n')
                            xrtnr     = crToRational xrtn
                            sqrtnxr   = crToRational $ crRoot (crMult cr' xrtn) 2

                            apply gm dt = Just (ml * numerator f1, numerator f2)
                                          where f1                  = c - sqrtnxr * d
                                                f2                  = c + sqrtnxr * d
                                                c                   = aA gm xrtnr
                                                d                   = aA dt xrtnr     
                            -- aA means applyArray. array/lists are treated like polynomials (zero-base assumed)    
                            aA a   x''  = f (elems a) 1 0 
                                          where f []     _  a' = a'
                                                f (c:cs) m' a' = f cs (m'*x'') (a' + (toRational c)*m') 
                                                                                
-- Example Aurif. decomp: C5(x) = x^2 + 3x + 1, D5(x) = x + 1 => Cyclotomic5(x) = C5(x)^2 − 5x*D5(x)^2                                                                                                 

-- | This function returns a pair of polynomials (in array form) or Nothing (if it's squareful). 
--   An illogical n (n <= 1) will generate an error.
aurDec :: Integer -> Maybe (Array Integer Integer, Array Integer Integer)
aurDec n | n <= 1    = error "aurifDecomp: n must be greater than 1"
         | otherwise = aurDecI n (crFromI n)

-- | Internal Aurifeullian Decomposition Workhorse Function
aurDecI :: Integer -> CR_ -> Maybe (Array Integer Integer, Array Integer Integer) 
aurDecI n cr | crHasSquare cr || n < 2 || n' < 2
                         = Nothing
             | otherwise = Just (gamma, delta)
             where nm4 = mod n 4   
                   n'  = if (nm4 == 1) then n else (2*n)
                   d   = div (totient n') 2
                   dm2 = mod d 2
                     
                   -- max gamma and delta subscripts to explicitly compute (add'l terms come from symmetry)
                   mg | dm2 == 1  = div (d-1) 2
                      | otherwise = div d     2
                   md | dm2 == 1  = div (d-1) 2
                      | otherwise = div (d-2) 2
                                              
                   -- create q array of size td2: q(2k+1) = jacobi n (2k+1),  q(2k+2  = mn * totient (2k+2)
                   q   = array (1, d) ([(i, f i) | i <- [1..d]])  
                         where f i  | mod i 2 == 1 = convJacobi $ jacobi n i
                                    | otherwise    = eQ
                                    where eQ       = moeb (crFromI $ div n' g) * (totient g) * (cos' $ (n-1)*i)                     
                                          g        = gcd n' i                                                                

                                          -- moebius fcn: 0 if has square, otherwise based on number of distinct prime factors
                                          moeb cr' | crHasSquare cr'         = 0 
                                                   | mod (length cr') 2 == 1 = -1 
                                                   | otherwise               = 1

                                          cos' c   | m8 == 2 || m8 == 6 = 0   -- "cosine" function
                                                   | m8 == 4            = -1
                                                   | m8 == 0            = 1
                                                   | otherwise          = error "Logic error: bad/odd value passed to cos'"  
                                                   where m8 = mod c 8

                   -- These two arrarys have mutually recursive definitions
                   gamma = array (0, d) ([(0,1)] ++ [(i, gf i) | i <- [1..d]]) 
                           where gf k | k > mg    = gamma!(d-k) 
                                      | otherwise = div gTerm (2*k)
                                      where gTerm = sum $ map f [0..k-1]
                                                    where f j = n * q!(2*k-2*j-1) * delta!j - q!(2*k-2*j) * gamma!j

                   delta = array (0, d-1) ([(0,1)] ++ [(i, df i) | i <- [1..d-1]])              
                           where df k | k > md    = delta!(d-k-1) 
                                      | otherwise = div dTerm (2*k+1)
                                      where dTerm = gamma!k + sum (map f [0..k-1]) 
                                                    where f j = q!(2*k-2*j+1) * gamma!j - q!(2*k-2*j) * delta!j

                  {- Pseudocode for computing gammas G and deltas D 
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

-- | Internal function requires two integers (computed via Aurif. methods) along with a list of Integers.  The product of 
--   the Integers must be a divisor of the list's product otherwise an error will be generated.
--   It's called divvy because it splits the 2 integers across the array using the gcd.
--   This will help factoring because the larger term(s) will be broken up into smaller pieces.
divvy :: [Integer] -> Integer -> Integer -> [Integer]
divvy a x y = d (sortBy rev a) (abs x) (abs y) 
              where rev a' b'       = if (a' > b') then LT else GT    
                    d []     x' y'  | x' == 1 && y' == 1             = []
                                    | abs x' == 1 && abs y' == 1 = [x' * y']
                                    | otherwise                    = error "Empty list passed as first param but x' and y' weren't both 1"
                    d (c:cs) x' y'  | x' == 1 && y' == 1 = c:cs 
                                    | otherwise          = v ++ d cs (div x' gnx) (div y' gny)
                                    where v   = filter (>1) $ [div q gny, gnx, gny]
                                          gnx = gcd c x'
                                          q   = div c gnx
                                          gny = gcd q y' 
{-  Test: Run divvy on this:
    let a = [4,7,8401,62324358089100907319521,682969,61,374857981681,547]
    let x = 50031545486420197
    let y = 50031544711579219     -}

{-  Cyclotomic factorizations for numbers of the form x^n +/- y^n
    Example:
      x^15-y^15 = (x-y) (x^2+x y+y^2) (x^4+x^3 y+x^2 y^2+x y^3+y^4) (x^8-x^7*y +x^5*y^3 - x^4*y^4 +x^3*y^5 -x*y^7+y^8)

    C(15) is a form of the last term where y = 1
    It's possible in some cases to do an additional Aurifeullian factorization (of the last term).   -}

-- | CycloPair: Pair of an Integer and its corresponding cyclotomic polynomial
type CycloPair         = (Integer, Poly Float)

-- | CycloMapInternal: Map internal to CycloMap newtype
type CycloMapInternal  = M.Map CR_ CycloPair

-- | CycloMap is a newtype hiding the details of a map of CR_ to pairs of integers and corresponding cyclotomic polynomials.
newtype CycloMap       = MakeCM CycloMapInternal deriving (Eq, Show)

-- | Unwrap the CycloMap newtype.
fromCM, fromCycloMap :: CycloMap -> CycloMapInternal
fromCM (MakeCM cm) = cm
fromCycloMap       = fromCM

-- | This is an initial map with the cyclotomic polynomials for 1 and 2.
crCycloInitMap :: CycloMap
crCycloInitMap = MakeCM $ M.insert cr1 (1, poly LE ([-1.0, 1.0] :: [Float])) M.empty

-- Two internal functions for the map internals
cmLookup :: CR_ -> CycloMap -> Maybe CycloPair 
cmLookup c m = M.lookup c (fromCM m)

cmInsert :: CR_ -> CycloPair -> CycloMap -> CycloMap
cmInsert c p m = MakeCM $ M.insert c p (fromCM m)

-- Computing the cyclotomic polynomials for the divisor set of a number:
--   Begin with with a map of 2 elements to the cylotomic polynomial for 1 and 2
--   Check the radical and return the map: crCycloRad
--   If the cr doesn't equal the radical,  then open it up to the other factors and the square-free factors must be in the map
--   Identity: x^n -1 is the product of cyclotomic polynomial for each  d where d | n.  

-- | Integer wrapper for crCyclo with default CycloMap parameter
cyclo :: Integer -> (CycloPair, CycloMap)
cyclo n = crCyclo (crFromI n) crCycloInitMap

-- | Integer wrapper for crCyclo 
cycloWithMap :: Integer -> CycloMap -> (CycloPair, CycloMap)
cycloWithMap n m = crCyclo (crFromI n) m

-- | Integer wrapper for crCycloDivSet with default CycloMap parameter
cycloDivSet :: Integer -> CycloMap
cycloDivSet n = fst $ crCycloDivSet (crFromI n) crCycloInitMap

-- | Integer wrapper for crCycloDivSet
cycloDivSetWithMap :: Integer -> CycloMap -> (CycloMap, CycloMap)
cycloDivSetWithMap n m  = crCycloDivSet (crFromI n) m

-- | Return pair of expon. multiplier and radical's polynomial along with working cyclotomic map.
crCyclo :: CR_ -> CycloMap -> (CycloPair, CycloMap)
crCyclo cr m | crPositive cr   = ((crToI $ crDivStrict cr r, p), m')
             | otherwise       = error "crCyclo: Positive integer needed"
             where r           = crRadical cr
                   ((_,p), m') = crCycloRad r m 

-- | Return a pair of cyclo maps just for the divisors and then a master map.
crCycloDivSet :: CR_ -> CycloMap -> (CycloMap, CycloMap)
crCycloDivSet cr m | crPositive cr = m2
                   | otherwise     = error "crCycloDivSet: Positive integer needed" 
                   where (_,m2) = c
                         crd = crDivisors cr
                         c   = case cmLookup cr m of 
                                 Nothing -> c' -- need to compute it
                                 Just p  -> (p, (mf, m))       -- found it.  add a filtered version.  ToDo: optimize this
                               where mf = MakeCM $ M.fromList $ filter (\(n,_) -> elem n crd) $ M.toList $ fromCM m

                            {- Performance note: The filter version above tended to be somewhat faster than the lookup
                                                 version below so I used that
                               where mf = MakeCM $ M.fromList $ map l crd     -- "lookup version"
                                          where l d = case cmLookup d m of
                                                        Nothing -> error $ e d
                                                        Just p -> (d, p) 
                                                e d = error "crCycloDivSet: Logic error: Divisor = '" ++ (show d) ++ "' not found!" 
                            -}  

                         c'  | r == cr   = (pr, (pm, pm))
                             | otherwise = (cm, (mm, mm)) 
                                           where (cm, mm)      = mfn sqFulDivs pm
                                                 r             = crRadical cr
                                                 (pr, pm)      = crCycloRad r m
                                                 sqFulDivs     = crd \\ crDivisors r  -- "squareful" divisors
                                                 mfn []     _  = error "Logic Error in mfn: Empty list is forbidden"
                                                 mfn (n:ns) mp | ns == []  = cp
                                                               | otherwise = mfn ns mp' 
                                                               where cp@(_, mp') = crCycloAll n mp

-- | Compute the "radical" divisors first and then the non-square free entries.
crCycloRad :: CR_ -> CycloMap -> (CycloPair, CycloMap)
crCycloRad cr m = case cmLookup cr m of 
                    Nothing -> c' -- need to compute it
                    Just p  -> (p, m)           -- found it
                  where c' | cs == []  = (cycpr, cmInsert cr cycpr m)           
                           | otherwise = (cyc_n, cmInsert cr cyc_n mp)
                           where (_ : cs)   = cr
                                 -- for primes, because the tail of the cr is [] meaning only one prime factor
                                 r          = fromInteger $ crToI $ crRadical cr  
                                              -- ToDo: Optimize cycpr to be quotient of (r^n -1)/(r-1) when r is a big prime  
                                 cycpr      = (1, poly LE (replicate r 1.0)) --prime : ToDo: Optimize this to be quotient when a
                                 -- for composites
                                 -- Create polynomial of the form : x^n -1
                                 xNm1       = poly LE ( (-1.0:(replicate (r-1) 0.0) ++ [1.0]) :: [Float] )
                                 (cPrd, mp) = mf (init $ crDivisors cr)
                                 cyc_n      = (1, quotPoly xNm1 cPrd)

                        -- mf (Memo Fold) takes a list of divisors and returns the pair: (cyclotomic product, memoized map)
                        mf (n:ns) = f ns p m' 
                                    where ((_,p), m')      = crCycloRad n m  
                                          f (n':ns') p' mp = f ns' (multPoly p' p'') m'' -- cycloMap-threaded mult. fold
                                                             where ((_,p''), m'') = crCycloRad n' mp
                                          f _        p' mp = (p', mp)
                        mf []     = error "Logic error: Blank list can't be passed to mf aka crCycloMemoFold" 

-- | Return a pair of Integer and its cyclotomic polynomial while efficiently building up a map
crCycloAll :: CR_ -> CycloMap -> (CycloPair, CycloMap)
crCycloAll cr m | p == cr1     = case cmLookup cr m of 
                                   Nothing -> error "Logic error: Radical value not found for crCycloAll"
                                   Just cb -> (cb, m)         -- found it                
                | otherwise    = (crp, cmInsert cr crp md)
                where (p, d)      = crPullSq
                      ((i,y), md) = case cmLookup d m of 
                                      Nothing -> crCycloAll d m -- need to compute it
                                      Just c  -> (c, m)         -- found it                
                      -- Optimization: (1, x + 1) => (4, x + 1). Note: Cyc2(x) = x + 1
                      -- The first value is the exponential multiplier Cyc8(x) = C2(x^4) = (x^4) + 1
                      crp         = ((fst $ head p) * i, y) 
                      crPullSq    = f [] cr
                                    where f h []             = (cr1, h)
                                          f h (c@(cp,ce):cs) | ce > 1    = ([(cp, 1)], h ++ (cp, ce-1):cs) 
                                                             | otherwise = f (h ++ [c]) cs

-- | These "apply cyclo" functions will use cyclotomic polynomial methods to factor x^e - b^e.
applyCrCycloPair :: Integer -> Integer -> CR_ -> CycloMap -> ([Integer], CycloMap)
applyCrCycloPair l r cr m = (applyCrCycloPairI l r cr (M.elems $ fromCM md), mn)
                            where (md, mn) = crCycloDivSet cr m

applyCrCycloPairI :: Integer -> Integer -> CR_ -> [CycloPair] -> [Integer]
applyCrCycloPairI l r cr cds           = map applyPoly cds
                 where nd              = crTotient cr
                       pA v            = a where a = array (0,nd) ([(0,1)] ++ [(i, v*a!(i-1)) | i <- [1..nd]]) -- array of powers
                       lpa             = pA l
                       rpa             = pA r
                       applyPoly (m,p) = foldr1 (+) (map f $ zip fmtdCy [0..])
                                         where f (a, b) | a == 0    = 0
                                                        | otherwise = a * lpa!(m*b) * rpa!(m*(maxExp - b))
                                               fmtdCy   = map ceiling $ polyCoeffs LE p -- format poly from mult poly pair
                                               maxExp   = toInteger $ length fmtdCy - 1

-- | Wraps applyCycloPairWithMap with default CycloMap argument.
applyCycloPair :: Integer -> Integer -> Integer -> [Integer]
applyCycloPair x y e = fst $ applyCycloPairWithMap x y e crCycloInitMap

-- | This will use cyclotomic polynomial methods to factor x^e - b^e.
applyCycloPairWithMap :: Integer -> Integer -> Integer -> CycloMap -> ([Integer], CycloMap)                  
applyCycloPairWithMap  x y e m = applyCrCycloPair x y (crFromI e) m

-- | This will display the cyclotomic polynomials for a CR.
showCyclo :: CR_ -> CycloMap -> [Char]
showCyclo n m = p $ map (\x -> (ceiling x) :: Integer) $ polyCoeffs LE (snd $ fst $ crCyclo n m)
                where p  (c:cs)   = show c ++ (p' cs (1 :: Int)) -- "LE" endianness is assumed here
                      p  _        = []
                      p' (c:cs) s | c == 0    = r
                                  | otherwise = (if c > 0 then " + " else  " - ") ++ (if ac == 1 then "" else show ac) ++
                                                "x" ++ (if s == 1 then "" else "^" ++ show s) ++ r
                                  where r  = p' cs (s+1) 
                                        ac = abs c
                      p' _      _ = []

-- | All the exponents must be even to return True.
crSquareFlag :: CR_ -> Bool
crSquareFlag = all (\(_, ce) -> mod ce 2 == 0) 

-- | Wrapper for chineseAurifWithMap with default CycloMap parameter
chineseAurif :: Integer -> Integer -> Bool -> Maybe (Integer, Integer)
chineseAurif x y b = fst $ chineseAurifWithMap x y b crCycloInitMap

-- | Integer wrapper for chineseAurifCr
chineseAurifWithMap :: Integer -> Integer -> Bool -> CycloMap -> (Maybe (Integer, Integer), CycloMap)
chineseAurifWithMap x y b m = chineseAurifCr (crFromI x) (crFromI y) b m

-- The source for this algorithm is the paper by Sun Qi, Ren Debin, Hong Shaofang, Yuan Pingzhi and Han Qing
-- http://www.jams.or.jp/scm/contents/Vol-2-3/2-3-16.pdf (The formula at 2.7 there is implemented below)
-- This will handle a subset of the cases that the main Aurif. routines handle

-- | This function reduces the two CR parameters by gcd before calling an internal function to find a "Chinese" Aurifeullian factorization.
chineseAurifCr :: CR_ -> CR_ -> Bool -> CycloMap -> (Maybe (Integer, Integer), CycloMap)
chineseAurifCr xp yp b m = case c of
                             Nothing -> chineseAurifI mbyx n myx (crToI myx) b m' -- if first try fails, try the reverse
                             r       -> (r, m') 
                           where (c, m') = chineseAurifI mbxy n mxy (crToI mxy) b m
                                 gcdxy   = crGCD xp yp
                                 (x, y)  = (crDivStrict xp gcdxy, crDivStrict yp gcdxy) -- strip out any commonality
                                 n       = gcd (crMaxRoot $ crAbs x) (crMaxRoot $ crAbs y)  
                                 ncr     = crFromI n                         
                                 mbxy    = crRoot (crDivRational x y) n
                                 mxy     = crGCD (crNumer mbxy)  ncr   
                                 mbyx    = crRecip mbxy
                                 myx     = crGCD (crNumer mbyx) ncr  

-- | Internal function to find factor of mb^n +/- 1 (mb would be M from paper, mb meaning m "big".
--   Solution forms: Any non-zero multiple of (q^2m * p) ^ (p * k) op (r^2n)^(p * k)  where k is an odd, postive number, m, n > 0.
--   This will work if the op is "+" when mod p 4 = 3   OR when op is "-" for when mod p 4 = 1.
chineseAurifI :: CR_ -> Integer -> CR_ -> Integer -> Bool -> CycloMap -> (Maybe (Integer, Integer), CycloMap)
chineseAurifI mbcr n mcr m b mp | mod n 2 == 0        || mod m 2 == 0 ||          -- n and m must both be odd
                                  m < 3               || km /= 0      ||          -- m must be odd and > 1 and m | n
                                  (mm4 == 1 && b)     || -- sign and modulus
                                  (mm4 == 3 && not b) || -- must be in synch           
                                  mbdm == cr0         || not (crSquareFlag mbdm)  -- mb/m must be a square and integral
                                            = (Nothing, mp)
                                | otherwise = case cv - (gd1 * gd2) of
                                                0 -> (Just (gd1, gd2), mp')
                                                _ -> (Nothing, mp) -- addl check since paper doesn't indicate rationals are supported
                                              where mm4      = mod m 4
                                                    e        = toRational $ if (mm4 == 3) then (-1) else mm4
                                                    (k, km)  = quotRem n m
                                                    mbdm     = case crDiv mbcr mcr of
                                                                 Left  _ -> cr0 -- error condition if not a multiple
                                                                 Right q -> q
                                                    r        = crToRational $ crRoot (crMult mbcr mcr) 2 -- sqrt (m*M) from paper
                                                    mb       = crToRational mbcr
                                                    jR c     = toRational $ convJacobi $ jacobi c m 
                                                    eM       = e * mb
                                                    v1       = (toRational m) * mb^(div (k * (m + 1)) 2)
                                                    v2       = t * s
                                                             where t = (jR 2) * r * (mb ^ (div (k-1) 2))
                                                                   s = sum $ map (\c -> (jR c) * eM^(k*c)) 
                                                                           $ filter (\c -> gcd c m == 1) [1..m] -- rel. prime
                                                    ncr      = crFromI n
                                                    -- get cyclotomic value
                                                    cv        = head $ applyCrCycloPairI (numerator eM) (denominator eM) ncr [cp]
                                                    (cp, mp') = crCyclo ncr mp 
                                                    gd1       = gcd cv (numerator $ v1 - v2) -- delta1 
                                                    gd2       = gcd cv (numerator $ v1 + v2) -- delta2

-- workaround after arithmoi changes
convJacobi :: JacobiSymbol -> Integer
convJacobi j = case j of
                 MinusOne -> -1
                 Zero     -> 0
                 One      -> 1

