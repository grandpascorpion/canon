-- |
-- Module:      Math.NumberTheory.Canon.SpecialFunctions
-- Copyright:   (c) 2018-2019 Frederick Schneider
-- Licence:     MIT
-- Maintainer:  Frederick Schneider <fws.nyc@gmail.com>
-- Stability:   Provisional
--
-- This module defines numerous functions associated with massive numbers.
-- This is an excellent resource: http://googology.wikia.com/wiki/Googology_Wiki

module Math.NumberTheory.Canon.SpecialFunctions (
  moserFunc,
  moserTriangle,
  moserSquare,
  moserPentagon,
  mega,
  megiston,
  moser,
  knuth,
  conwayChain,
  conwayGuy,
  genGrahamFunc,
  grahamFunc,
  grahamsNumber,
  ackermann,
  ackermann3
  -- , sudan
)
where

import Math.NumberTheory.Canon

moserFunc :: Canon -> Canon -> Canon -> Canon
moserTriangle, moserSquare :: Canon -> Canon
moserPentagon, mega, megiston, moser :: Canon

-- | Generalized Moser function: https://en.wikipedia.org/wiki/Steinhaus%E2%80%93Moser_notation
moserFunc nP mP pP 
  | cIntegral nP && cIntegral mP && cIntegral pP && nP >= c1 && pP >= c3
              = m' nP mP pP
  | otherwise = error "The parameters to the Moser function must all be integral with n >= 1 and p >= 3."
  where m' n m p | n < 1     = error "n must be >= 1 in the Moser function"
                 | m > c1    = m' (m' n c1 p) (m-c1) p
                 | p > c3    = m' n           n     (p-c1) 
                 | otherwise = n <^ n
-- to do: non-recursive definition?

-- | Moser Triangle (see Wikipedia link above)
moserTriangle n = moserFunc n c1 c3

-- | Moser Square (see Wikipedia link above)
moserSquare n   = moserFunc n c1 c4

-- | Moser Pentagon (see Wikipedia link above)
moserPentagon = mega

-- | Mega: "2 in a circle" (see Wikipedia link above) 
mega          = moserFunc c2  c1 c5

-- | Megiston: "10 in a circle" (see Wikipedia link above) 
megiston      = moserFunc c10 c1 c5
                where c10 = makeCanon 10

-- | Moser number; "2 in a mega-gon" (see Wikipedia link above)
moser         = moserFunc c2 c1 mega 

ackermann :: Canon -> Canon -> Canon
ackermann3 :: Canon -> Canon -> Canon -> Canon

-- | <https://en.wikipedia.org/wiki/Ackermann_function Ackermann function>
ackermann m n
  | cIntegral m && cIntegral n && m >= c0 && n >= c0 
              = a m n
  | otherwise = error "m and n must both be integral in the Ackermann function with m >= 0 and n >= 0"
  where a m' n' | m' == c0            = n' + c1
                | m' < c3 && n' == c0 = a (m' - c1) c1
                | m' < c3             = a (m' - c1) $ a m' (n - c1)
                | otherwise           = -3 + conwayChain [2, n+3, m-2]
               
-- | The original 3 parameter Ackermann function 
ackermann3 mP nP pP 
  | cIntegral mP && cIntegral nP && cIntegral pP && nP >= c0 && pP >= c0 
              = a3 mP nP pP
  | otherwise = error "m, n and p must all be integral in the Ackermann3 function"
  where a3 m n p | n < c0 || p < c0 = error "ackermann3 Both n and p must be >= 0"
                 | p == c0           = m + n
                 | p == c1           = m * n 
                 | p == c2           = m <^ n
                 | p == c3           = m <^> (n + c1)
                 | n == c0           = m
                 | p == c4 && n == 2 = m <^> (1 + m <^> (m + c1)) -- Found while testing.  Helps along calculation 
                 | p == c4 && n > 2  = m <^> (1 + a3 m (n - c1) p)
                 | otherwise         = a3 m (a3 m (n - c1) p) (p - c1)

{- Status
 ackermann3 2 2 4 = 2 <^> 17  -- could also be written as 2 <^> (1 + 2<^>3) so this is between 2 <<^>> 3 and 2 <<^>> 4
 ackermann3 2 3 4 = 2 <^> {1 + 2 <^> 17}
 ackermann3 2 4 4 ... Generated error saying special cases in cHyperOp not covered when more than two items.  XXX
 ackermann3 3 2 4 = 3 <^> (1 + 3 <^> (2*2))
 ackermann3 3 3 4 ... Hung initially but workaround added 
 ackermann3 7 3 4 = 7 <^> {1 + 7 <^> {1 + 7 <^> (2^3)}} 
 ackermann3 5 4 4 = 5 <^> {1 + 5 <^> {1 + 5 <^> {1 + 5 <^> (2 * 3)}}} -- note the folding based on the second term

 ackermann3 2 2 5 ... Hangs

 Here's why (stepping through the logic)
 a3 2 2 5 = a3 2 (a3 2 1 5) 4
 where a3 2 1 5 = a3 2 (a3 2 0 5) 4 = a3 2 2 4

 a3 2 2 5 = a3 2 (a3 2 2 4) 4 = a3 2 (2<^>17) 4.  So, this folding step would have to be done an incredible number of times.

 ToDo: Is there an elegant closed form expression? x n 4 is between x <<^>> n+ 1 and x <<^>> n + 2.
-}

{- ToDo: Fix and add later
-- | The Sudan function created by Gabriel Sudan, a student of David Hilbert (https://en.wikipedia.org/wiki/Sudan_function)
sudan :: Canon -> Canon -> Canon -> Canon
sudan n x y | not (cIntegral n) || not (cIntegral x) || not (cIntegral y) || n < 0 || x < 0 || y < 0 
                        = error "All input to the sudan function must be integral and >= 0"
            | otherwise = s n x y 
            where s n x y | n == 0          = x + y
                          | n > 0 && y == 0 = x
                          | n == 1          = s c1 c0 y + x * 2 <^ y
                          | otherwise       = s (n-1) snxym1 (snxym1 + y)
                           where snxym1 = s n x (y-1) 
-}

genGrahamFunc :: Canon -> Integer -> Canon
grahamFunc :: Integer -> Canon
grahamsNumber :: Canon

-- | Calls the generalized Graham function with value 3
grahamFunc = genGrahamFunc c3

-- | <https://en.wikipedia.org/wiki/Graham%27s_number Graham's Number>
grahamsNumber = grahamFunc 64
 
-- | Generalized Graham Function
genGrahamFunc cP nP 
  | cIntegral cP && cP >= c1 && nP >= 1
              = gGF cP nP
  | otherwise = error "c and n must be Integral and both c and n >= 1 in the generalized Graham function"
  where gGF c n | n > 1     = cApplyHy (gGF c (n -1)) [c,c] True -- recursively defined
                | otherwise = c <<<^>>> c -- Hexation or 4 arrows

knuth :: Canon -> Canon -> Canon -> Canon

-- | <https://en.wikipedia.org/wiki/Knuth%27s_up-arrow_notation Knuth's Up Arrow Notation>, analagous to hyperoperations
knuth a n b        = cApplyHy (c2 + n) [a,b] True 

-- | <https://en.wikipedia.org/wiki/Conway_chained_arrow_notation Conway Chained-Arrow Notation>: 
--   This function will try to reduce generalized conway chain notation down to humble hyperoperations (or better).
conwayChain :: [Canon] -> Canon
conwayChain l' 
  | all (\c -> cIntegral c && c > c0) l' = cc l'
  | otherwise                            = error "ConwayChain: Each element in the input list/chain must be integral and > 0"
  where cc ch | null ch       = error "Logic Error: conwayChain requires a non-zero list." 
              | head ch == c1 = c1
              | otherwise     = f (takeWhile (/= c1) ch) 
        f c   = case l of 
                0 -> c1 -- in this context we have stripped out the 1s so we can assume 1
                1 -> p  
                2 -> p <^ q
                3 -> knuth p r q -- "simple" hyperoperation

                     -- Beyond length 3, we may never come back. Note: We string out the 1s
                _ |  p == c2 && q == c2 -> c4 -- Property #6
                  |  otherwise          -> cc $ x ++ [cc (x ++ [s-1, v])] ++ [v-1] -- Rule #4 
                where l         = length c
                      (p, q, r) = (head c, c !! 1, c!! 2)
                      x         = take (l-2) c -- x is like the prefix chain from the wiki formula
                      (s, v)    = (c !! (l-2), last c) -- second to last AND "very" last terms

-- Note: conwayChain [x,2,2,2] = x <H(x^2 + 1)> x.  (e.g. conwayChain [3,2,2,2] = 3 ~^~ 3, which is the hyperoperator for level 10)

{-  Some low-level level 4 examples

v = map (\l -> (l, conwayChain $ map makeCanon l)) [[3,2,2,2], [3,2,3,2], [3,3,2,2], [3,3,3,2],  [3,2,2,3], [3,3,2,3]]
mapM_ (putStrLn . show) v
([3,2,2,2],  3 ~^~ 3)  -- Level 10 = 3^2 + 1 Hyper Operation.  Note: The library converts: x <HO: h> 2 TO x <HO: h-1> x

([3,2,3,2], 3 <H{1 + 3 ~^~ 3}> 3)  -- which is 3 <H{1 + conwayChain[3,2,2,2])> 3

([3,3,2,2],3 ~~|<<<<^>>>>|~~ 3) -- Level 29 = 3^3 + 2 Hyper Operation

([3,3,3,2],3 <H{2 + 3 ~~|<<<<^>>>>|~~ 3}> 3)  -- which is  3 <H{2 + conwayChain[3,3,2,2])> 3

([3,2,2,3],3 <H{1 + 3 <H{1 + 3 <H{1 + 3 <H{1 + 3 <H{1 + 3 <H{1 + 3 <H{1 + 3 ~^~ 3}> 3}> 3}> 3}> 3}> 3}> 3}> 3)

([3,3,2,3],3 <H{2 + 3 <H{2 + 3 <H{2 + 3 <H{2 + 3 <H{2 + 3 <H{2 + 3 <H{2 + 3 <H{2 + 3 <H{2 + 3 <H{2 + 3 <H{2 + 3 <H{2 + 3 <H{2 + 3 <H{2 + 3 <H{2 + 3 <H{2 + 3 <H{2 + 3 <H{2 + 3 <H{2 + 3 <H{2 + 3 <H{2 + 3 <H{2 + 3 <H{2 + 3 <H{2 + 3 <H{2 + 3 ~~|<<<<^>>>>|~~ 3}> 3}> 3}> 3}> 3}> 3}> 3}> 3}> 3}> 3}> 3}> 3}> 3}> 3}> 3}> 3}> 3}> 3}> 3}> 3}> 3}> 3}> 3}> 3}> 3}> 3)

Note: conwayChain [3,3,3,3] = conwayChain [3,3, [3,3,2,3], 2] so you have to iteratively embed the hyper operations a massive number of times
Note: For perspective, Graham's number has been shown to be between [3,3,64,2] and [3,3,65,2]!
-}

conwayGuy :: Canon -> Canon
                        
-- | Conway-Guy function is a conwayChain of n copies of n.  
conwayGuy n = conwayChain (replicate (fromIntegral n) n)

-- Kind of unrelated but interesting: goodstein rep: https://en.wikipedia.org/wiki/Knuth%27s_up-arrow_notation#Numeration_systems_based_on_the_hyperoperation_sequence

