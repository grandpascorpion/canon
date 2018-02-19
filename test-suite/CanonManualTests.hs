-- |
-- Module:      Math.NumberTheory.CanonTests
-- Copyright:   (c) 2018 Andrew Lelechenko
-- Licence:     MIT
-- Maintainer:  Frederick Schneider <frederick.schneider2011@gmail.com> 
-- Stability:   Provisional
--
-- Tests for Math.NumberTheory.Canon, etc
--

{-# OPTIONS_GHC -fno-warn-type-defaults #-}

import Math.NumberTheory.Canon
import Math.NumberTheory.Canon.AurifCyclo
import Data.Array (array)
import Control.Monad (forever)

trueS, falseS :: String
trueS = "true"
falseS = "FALSE"

divvyTest, aCaDTest, aDTest, cATest, cATestM, aCPTest :: Bool
divvyTest = ans == divvy a x y
            where a   = [4,7,8401,62324358089100907319521,682969,61,374857981681,547]
                  x   = 50031545486420197
                  y   = 50031544711579219
                  ans = [765980456641,81365467681,374857981681,301,2269,31,271,547,61,7,4]

aCaDTest = r == aurCandDec (2^58) 1 True
           where r = Just (536838145,536903681)

aDTest = r == aurDec 5
         where r = Just (array (0,2) [(0,1),(1,3),(2,1)],array (0,1) [(0,1),(1,1)])

--chineseAurif: Any non-zero multiple of (q^2m * p) ^ (p * k) + (r^2n)^(p * k)  where k is odd pos, m, n > 0
-- q and r do not both equal 1

cATest = r == chineseAurif (44^253) 1 True -- Equivalent to 44^253 + 1.  Should these two factors below.  Example from Sichuan 5 paper
              where r = Just (
                        3708082114051284931014527275382936962949050019900548504948093002539948192457694962513241254988377338102340862648630965276420678480576906389289483833735873261700512602622143146599971,
                        10004590597907985573943582945748620748239251502916976018978239877682278432398712396908419662400063010898795149152694380672517014008143612228221361453877714927361019333917217066917231
                        )

cATestM = r == chineseAurif ((q*p)^(p*m)) (s^(p*m)) False -- Equivalent to 117^221 - 4^221.
          where (p, q, m, s) = (13, 9, 17, 4)
                r = Just (
                          6777177566148891825866597484460647604677595599339380316570867390255387995775996275965289196556216301121524986265286043390240164764352880415910164128699689628228970391585087480017942725930708815238591,
                          1760066887061200649747400254189929691148780525097352459006167529137160481395362942899568367387185016629815611235574356459997927884738618313122568841325847458481738026543495018488267067010986061866931
                         )         

aCPTest = boolFlag 
          where (_, _, boolFlag) = verifyApplyCycloPair 5 3 2310

verifyApplyCycloPair :: Integer -> Integer -> Integer -> (Integer, [Integer], Bool)
verifyApplyCycloPair x y e = (v, factors, v == product factors) -- should be True
                             where v       = x^e - y^e
                                   factors = applyCycloPair x y e

{-
-- fix this
f p e = aurCandDec (p^(e*p)) 1 True 
f 11 15
Just (1271895306126722839332303077175663680408337203898205913979279374031646228168717,1271895436663409913619808282471754544629810369181390985798959949855832620283803)

oddExpAur p em = aurCandDec (p^(em*p)) 1 True
evenExpAur p em = aurCandDec (p^(em*p)) 1 False
-}

canonBasicProperties :: Int -> [(Int, String)]
canonBasicProperties m | m <= 0    = error "Positive ints only"
                       | otherwise = formatTestOutput tests
                       where tests = [mc * rc == c1,
                                      mc / mc == c1,
                                      (toInteger $ mc - mc) == 0,
                                      mc + mc == mc * 2,
                                      mc ^ 2  == mc * mc,

                                      mc + c1 > mc,
                                      mc - 1 < mc,
                                      mc == negate nmc, -- double negative
                                      mc == abs nmc,
                                      mc == cReciprocal rc, -- double reciprocal

                                      signum mc == c1,
                                      signum nmc == negate c1,
                                      toInteger mc == toInteger m, -- undo the conversion
                                      cNegative nmc && cPositive mc,
                                      cIntegral mc && cIntegral nmc,

                                      --XXXX cIrrational sr && 
                                      --XXXX sr <^ mp1 == c1 &&
                                      oc /= ec && (oc || ec) 
                                     ] 
                             mc  = makeCanon $ toInteger $ m
                             rc  = cReciprocal mc 
                             nmc = negate mc
                             -- mp1 = mc + c1
                             -- sr  = mp1 >^ mp1 -- take the xth root of x (x is > 1).  Must be irrational
                             oc  = cOdd mc
                             ec  = cOdd $ mc + c1 -- even check
                             c1  = makeCanon 1

canonBasicProperties2 :: Int -> Int -> [(Int, String)]
canonBasicProperties2 m n | m <= 0 || n <= 0 = error "m and n must be positive"
                          | otherwise        = formatTestOutput tests
                          where 
                            tests = [mc * nc / g == cLCM mc nc,
                                     mc == q * nc + r,
                                     mc == nc >^ mxn,  -- test the root operator
                                     r == mod mc nc
                                    ]
                            mc    = makeCanon $ toInteger m
                            nc    = makeCanon $ toInteger n
                            g     = makeCanon $ toInteger $ gcd m n
                            (q,r) = quotRem mc nc
                            mxn   = mc <^ nc -- exponentiation

formatTestOutput :: [Bool] -> [(Int, String)]
formatTestOutput tests = zip [1..] $ map (\b -> if b then trueS else falseS) tests

main :: IO ()
main = forever $ do
  print "Canon Basic Properties (Enter 1 param): " 
  p <- getLine
  print $ canonBasicProperties (read p :: Int) 
  print ""
  print "Canon Basic Properties (Enter 2 params, one each line): "
  p1 <- getLine
  p2 <- getLine
  print $ canonBasicProperties2 (read p1 :: Int) (read p2 :: Int)
  print ""
  print "Canon Specific Tests (0 params): "
  print $ formatTestOutput [divvyTest, aCaDTest, aDTest, cATest, cATestM, aCPTest]
  print ""

