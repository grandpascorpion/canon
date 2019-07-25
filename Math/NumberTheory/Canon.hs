-- |
-- Module:      Math.NumberTheory.Canon
-- Copyright:   (c) 2015-2019 Frederick Schneider
-- Licence:     MIT
-- Maintainer:  Frederick Schneider <fws.nyc@gmail.com> 
-- Stability:   Provisional
--
-- A Canon is exponentation-based representation for arbitrarily massive numbers, including prime towers and hyper-expressions.

{-# LANGUAGE PatternSynonyms, ViewPatterns, RankNTypes #-}

module Math.NumberTheory.Canon ( 
  Canon, makeCanon, makeCanon', BareStatus(..), CanonValueType(..), 
  cShowFull, cShowFullAsCode, cShowAsCode, cShowAsCodeUnf, cShowUnf,
  cMult, cDiv, cAdd, cSubtract, cExp,
  cReciprocal, (>^), (<^),
  cGCD, cLCM, cMod, cOdd, cEven, cTotient, cPhi,
  cNegative, cPositive, cIntegral, cRational, cIrrational, cPrime, cSimplified,
  cSplit, cNumerator, cDenominator,
  cCanonical, cBare, cBareStatus, cValueType, cDelve,
  cIsPrimeTower, cPrimeTowerLevel, cSuperLog, cSuperLogCmp,

  -- Hyper levels 4 through 9 for these 4 lines
  cTetration,  cPentation,  cHexation,  cHeptation,  cOctation, cNonation,
  cTetrationL, cPentationL, cHexationL, cHeptationL, cOctationL, cNonationL,
  (<^>),  (<<^>>),  (<<<^>>>),  (<<<<^>>>>),  (<<<<<^>>>>>),  (|<^>|),
  (<^^>), (<<^^>>), (<<<^^>>>), (<<<<^^>>>>), (<<<<<^^>>>>>), (|<^^>|),

  -- Operators for hyper levels 10-50
  (~^~), (~<^>~), (~<<^>>~), (~<<<^>>>~), (~<<<<^>>>>~),                                         -- 10-14
  (~|^|~), (~|<^>|~), (~|<<^>>|~), (~|<<<^>>>|~), (~|<<<<^>>>>|~),                               -- 15-19
  (~~^~~), (~~<^>~~), (~~<<^>>~~), (~~<<<^>>>~~), (~~<<<<^>>>>~~),                               -- 20-24
  (~~|^|~~), (~~|<^>|~~), (~~|<<^>>|~~), (~~|<<<^>>>|~~), (~~|<<<<^>>>>|~~),                     -- 25-29
  (~~~^~~~), (~~~<^>~~~), (~~~<<^>>~~~), (~~~<<<^>>>~~~), (~~~<<<<^>>>>~~~),                     -- 30-34
  (~~~|^|~~~), (~~~|<^>|~~~), (~~~|<<^>>|~~~), (~~~|<<<^>>>|~~~), (~~~|<<<<^>>>>|~~~),           -- 35-39
  (~~~~^~~~~), (~~~~<^>~~~~), (~~~~<<^>>~~~~), (~~~~<<<^>>>~~~~), (~~~~<<<<^>>>>~~~~),           -- 40-44
  (~~~~|^|~~~~), (~~~~|<^>|~~~~), (~~~~|<<^>>|~~~~), (~~~~|<<<^>>>|~~~~), (~~~~|<<<<^>>>>|~~~~), -- 45-49
  (~~~~~^~~~~~),                                                                                 -- FIFTY

  cAddOpLevel,  cMultOpLevel, cExpOpLevel,  cTetrOpLevel,             -- Hyper levels 1-4
  cPentOpLevel, cHexOpLevel,  cHeptOpLevel, cOctOpLevel, cNonOpLevel, -- Hyper levels 5-9
  cGetHyperList, cGetHyperOp, maxHyperOpDispLevel, maxHyperOpDelveLevel, 
  cFactorSum, cConvertToSum, cMaxExpoToExpand, cFactorHorizon, 
  cApplyHy, cHyperOp, cHyperExpr, cHyperExprAny, cMaxHyperOp, cMinHyperOp, 
  cHyperSum, cHyperProd, cHyperExpo, cHyperSumAny, 
  cHyperize, cQuasiCanonize, cQuasiCanonized, cCleanup, cGetAddends, cGetFactors, cCleanupAsNumDenPair,

  CanonElement, cGetBase, cGetExponent,
  cGetBases, cGetBasesDeep, cGetExponents, cGetElements, 
  cNumDivisors, cTau, cDivisors, cNthDivisor, cWhichDivisor, cRelativelyPrime, cGetFirstNDivisors,

  cN1, c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, 
  CycloMap, getIntegerBasedCycloMap, showCyclo, crCycloInitMap -- Exposes cyclotomic map-related functionality from AurifCyclo
)
where

import Math.NumberTheory.Primes (primes, unPrime)
import Math.NumberTheory.Primes.Testing (isPrime)
import Data.List 
import Data.Maybe (fromMaybe)
import GHC.Real (Ratio(..))
import Math.NumberTheory.Canon.Internals
import Math.NumberTheory.Canon.Additive
import Math.NumberTheory.Canon.AurifCyclo
import Math.NumberTheory.Canon.Simple (CanonConv(..))
-- import Debug.Trace (trace)

-- | CanonValueType: 3 possibilities for this GADT (integral, non-integral rational, irrational).  
--   Imaginary/complex numbers are not supported
data CanonValueType = IntC | NirC | IrrC deriving (Eq, Ord, Show)

-- | This element is a base, exponent pair.  The base is an integer and is generally prime or 0, -1.
--   The exponent is also a Canon (allowing for arbitrary nesting)
--   A Canon conceptually consists of a list of these elements.  The first member of the pair will 
--   be a Canon raised to the first power.  By doing this, we're allow for further generality
--   in the definition of a Canon. 
type CanonElement = (Canon, Canon)

-- | GCR_ stands for Generalized Canonical Representation.  This is internal to Canon.
type GCR_  = [GCRE_]

type GCRE_ = (Integer, Canon)

-- | Canon: GADT for either Bare (Integer) or some variation of a Can(onical) form (see CanonValueType).
data Canon = Bare Integer BareStatus | Can GCR_ CanonValueType | HX Canon [Canon] CanonValueType

-- | BareStatus: A "Bare Simp" number means a prime number, +/-1 or 0.  The code must set the flag properly
--               A "Bare NSim" number is an Integer that has not been checked (to see if it can be factored).
data BareStatus = Simp | NSim deriving (Eq, Ord, Show)

-- | Create a Canon from an Integer.  This may involve expensive factorization.
makeCanon :: Integer -> Canon
makeCanon n = fst $ makeCanon' n

-- | Create a Canon from an Integer.  Also return True if the number is fully factored
makeCanon' :: Integer -> (Canon, Bool)
makeCanon' n = (f cr, ff)
               where f POne                  = Bare 1 Simp
                     f c    | null cs && eh == 1  
                                             = if superLogI bh > superLogICutoff -- because we assume bare < hyper expr
                                               then error "Lib limitation: Can't handle massive bare numbers > cutoff"
                                               else Bare bh (if ff then Simp else NSim) 
                            | otherwise      = Can g (gcrCVT g)
                                               where (bh,eh):cs = c
                                                     g          = map (\(p,e) -> (p, makeCanon e)) c
                                                     -- (can't be reduced any further)
                     (cr, ff)                = crFromI n -- 2nd param, the totally factored flag not used at this time 

-- | Convert from underlying canonical rep. to Canon.  The 2nd param indicates whether or not to force factorization/simplification.
crToC :: CR_ -> Bool -> Canon
crToC POne _                  = Bare 1              Simp
crToC c    _ | crSimplified c = Bare (fst $ head c) Simp -- a little ugly
             | otherwise      = Can g (gcrCVT g)
                                where g          = map (\(p,e) -> (p, makeCanon e)) c

-- | Instances for Canon
instance Eq Canon where
  x == y = cEq x y

-- | Internal value that corresponds with ~~~~~^~~~~~ (level 50 hyperoperation)
maxHyperOpDispLevel :: Integer
maxHyperOpDispLevel = 50;

-- | Max hyper operaton level when converting to canonical form (for the sake of combining and reducing terms)
maxHyperOpDelveLevel :: Canon 
maxHyperOpDelveLevel = makeCanon 100; 

-- These must correspond with the built-in and defined operators (from addition through hexation), except for ^
hyperOpStrings :: [String] -- ensure this is consistent with small canons / maxHyperOpDisplayLevel
hyperOpStrings = [
  "", "+", "*", "^", "<^>", "<<^>>", "<<<^>>>", "<<<<^>>>>", "<<<<<^>>>>>", "|<^>|",             -- 0-9
  "~^~", "~<^>~", "~<<^>>~", "~<<<^>>>~", "~<<<<^>>>>~",                                         -- 10-14
  "~|^|~", "~|<^>|~", "~|<<^>>|~", "~|<<<^>>>|~", "~|<<<<^>>>>|~",                               -- 15-19
  "~~^~~", "~~<^>~~", "~~<<^>>~~", "~~<<<^>>>~~", "~~<<<<^>>>>~~",                               -- 20-24
  "~~|^|~~", "~~|<^>|~~", "~~|<<^>>|~~", "~~|<<<^>>>|~~", "~~|<<<<^>>>>|~~",                     -- 25-29
  "~~~^~~~", "~~~<^>~~~", "~~~<<^>>~~~", "~~~<<<^>>>~~~", "~~~<<<<^>>>>~~~",                     -- 30-34
  "~~~|^|~~~", "~~~|<^>|~~~", "~~~|<<^>>|~~~", "~~~|<<<^>>>|~~~", "~~~|<<<<^>>>>|~~~",           -- 35-39
  "~~~~^~~~~", "~~~~<^>~~~~", "~~~~<<^>>~~~~", "~~~~<<<^>>>~~~~", "~~~~<<<<^>>>>~~~~",           -- 40-44
  "~~~~|^|~~~~", "~~~~|<^>|~~~~", "~~~~|<<^>>|~~~~", "~~~~|<<<^>>>|~~~~", "~~~~|<<<<^>>>>|~~~~", -- 45-49
  "~~~~~^~~~~~"]                                                                                 -- FIFTY 

smallCanons :: [Canon]
smallCanons = map (\n -> makeCanon n) [0..maxHyperOpDispLevel]

-- | Levels starting with 1 in the hyperoperation hierarchy
cAddOpLevel, cMultOpLevel, cExpOpLevel, cTetrOpLevel, 
  cPentOpLevel, cHexOpLevel, cHeptOpLevel, cOctOpLevel, cNonOpLevel :: Canon

(_: cAddOpLevel  : cMultOpLevel : cExpOpLevel  : cTetrOpLevel : 
    cPentOpLevel : cHexOpLevel  : cHeptOpLevel : cOctOpLevel  : cNonOpLevel : _) = smallCanons

-- | Various show functions: cShowFull - fully expand large primes and composites in Canon expression.  
--   "Unf" in name means don't factor unless it's too big too display
--    "AsCode" in name means you can copy and paste the results and execute them. 
cShowFull, cShowFullAsCode, cShowAsCode, cShowAsCodeUnf, cShowUnf, cShowForEqChk :: Canon -> String
cShowFull       = cShow True  False False False
cShowFullAsCode = cShow True  True  False False
cShowAsCode     = cShow False True  False False  -- displays hyperexpr wrapped in parens
cShowAsCodeUnf  = cShow False True  True  False
cShowUnf        = cShow False False True  False
cShowForEqChk   = cShow False False False True

instance Show Canon where 
  -- If debugging ... show = cShowAsCode -- so can it be pasted back in and run.  Leave this way? Maybe default should not use { } and use use <^
  show = cShow False False False False -- 1st bool = b: if True, full display of all integers, 
                                       -- 2nd bool = p: if True, all parens for most hyperexprs,
                                       -- 3rd bool = i: if True, display unfactored integers where possible
                                       -- 4th bool = m: if True, when a hyOp is a sum or product, sort it, when to check for equality)
  -- Note: If parens flag is true and as long as the hyperOp doesn't exceed the max display level, 
  --       you can copy and paste the expression back in as input

cShow :: Bool -> Bool -> Bool -> Bool -> Canon -> String
cShow b _ i _ (Bare n NSim)
  = showI b n False i  -- False means composite
cShow b _ i _ (Bare n Simp)
  = showI b n True i -- True means prime (or -1, 0, 1)
cShow b p i m (HX h l _)
  | p && (cHyperExprAny h || h > maxSmallC) 
              = "cApplyHy " ++ showH h ++ " [" ++ (concat $ intersperse ", " $ map (cShow b p i m) cl) ++ "] True" -- fmt as fcn call!
  | otherwise = fmt1 (head cl) ++ s' (tail cl)
  where cl      | h == cAddOpLevel && any cNegative l = pR ++ nR -- put the negatives in back
                | otherwise                           = l
                where (pR, nR) = partition cPositive l -- there should always be at least one of each.  The sum must be positive
        fmt1 hD | not (cHyperExpr hD) && h == cMultOpLevel = cShow b p i m hD
                | otherwise                                = showH hD
        showH c | h == cAddOpLevel || cBare c || (i && canConvToI c) = rep -- showH small helper function for clarity of expression
                | (not p) && cHyperExpr c                            = "{" ++ rep ++ "}"
                | otherwise                                          = "(" ++ rep ++ ")"
                where rep = cShow b p i m c
        fmtHy f | f                                = "-" -- indicates a negative sign, flip a plus to minus
                | cHyperExprAny h || h > maxSmallC = fmt' h 
                | p && h == cExpOpLevel            = "<^"
                | otherwise                        = hyperOpStrings !! (fromInteger $ cToI h) -- and write cApplyHy for exp
                where fmt' c | (not p) && cHyperExpr c = "<H{" ++ rep' ++ "}>"
                             | otherwise               = "<H(" ++ rep ++ ")>"
                             where rep  = cShow b p i m c
                                   rep' | not m                         = rep
                                        | cGetHyperOp c == cAddOpLevel  = cShow b p i m (fst $ cConvertToSum c)
                                        | cGetHyperOp c == cMultOpLevel = cShow b p i m c 
                                        | otherwise                     = rep

        s' (x:xs) = " " ++ fmtHy f' ++ " " ++ showH (if f' then (negate x) else x) ++ s' xs
                    where f' = h == cAddOpLevel && cNegative x
        s' _      = ""
        maxSmallC = smallCanons !! (fromInteger $ maxHyperOpDispLevel)
cShow b p i m c
  | denom == c1 = s numer False
  | otherwise   = s numer True ++ " / " ++ s denom True
  where (numer, denom)      = cSplit c 
        s (Bare n f) _ = cShow b p i m (Bare n f)
        s v          w | i && canConvToI v = show $ cToI v -- if the Canonical is not too big, convert it back to integer (when i flag is true)
                       | w                 = "(" ++ catList ++ ")"
                       | otherwise = catList               -- w = with(out) parens
                       where catList        =   concat $ intersperse " * " $ map sE $ gcr' $ cToGCR v
                             gcr' g@(x:y:gs)| fst x == -1 && snd y == c1 = ((fst x * fst y, snd y) : gs)
                                            | otherwise                  = g -- above: display (-1,1), (2,1) as -2
                             gcr' g         = g
                             sE (p', e)     | ptLevel > 2 = sp ++ " <^> " ++ s ptLevel True -- sE means show element
                                            | otherwise   = case e of
                                                            Bare 1 _ -> sp
                                                            Bare _ _ -> sp ++ expOp ++ se
                                                            _        -> sp ++ " " ++ expOp ++ " (" ++ se ++ ")"
                                            where ptLevel = cPrimeTowerLevelI e p' 1
                                                  sp      = showI b p' (isPrime p' || p' == -1) i
                                                  se      = cShow b p i m e
                             expOp          = if p then "<^" else "^"

canConvToI :: Canon -> Bool
canConvToI c = not $ cSuperLogGT (fst $ cSuperLog c) cSuperLogCutoff 

-- Allow via first parameter to suppress full printing of massive integers and just indicate an "x-digit number"
showI :: Bool -> Integer -> Bool -> Bool -> String
showI b n pOrC i | i         = show n -- just as is
                 | not pOrC  = "[" ++ txt ++ "]" -- composites go in brackets (either number or digit count)
                 | truncFlag = "(" ++ txt ++ ")" -- if prime but tooBig, put in parens
                 | otherwise = txt             -- just the number
               where txt          = if truncFlag
                                    then (show $ nd n) ++ "-digit " ++ (if pOrC then "prime" else "composite")
                                    else show n
                     truncFlag    = (not b) && n > integerShowCutoff
                     nd :: Integer -> Integer
                     nd n'        = nd' n' 1 -- Count digits 1 by 1.  ToDo: Optimize
                                    where nd' n'' ct = if (n'' >= 10) then nd' (div n'' 10) (ct + 1)
                                                                      else ct
 
instance Enum Canon where
  toEnum   n = makeCanon $ fromIntegral n
  fromEnum c = fromIntegral $ cToI c

instance Ord Canon where
  compare x y = cCmp x y 

instance Real Canon where
  toRational c | cIrrational c = toRational $ cToD c
               | otherwise     = (cToI $ cNumerator c) :% (cToI $ cDenominator c)

instance Integral Canon where
  toInteger c | cIntegral c = cToI c 
              | otherwise   = floor $ cToD c
  quotRem n m = fst $ cQuotRem n m crCycloInitMap  --  tries to use map but ultimately throws it away 
  mod n m     = cMod n m
            
instance Fractional Canon where
  fromRational (n :% d) = makeCanon n / makeCanon d                   
  (/) x y               = fst $ cDiv x y crCycloInitMap -- tries to use map but ultimately throws it away

instance Num Canon where -- tries to use the map but ultimately throws it away when using +, - and * operators
  fromInteger n = makeCanon n
  x + y         = fst $ cAdd      x y crCycloInitMap  
  x - y         = fst $ cSubtract x y crCycloInitMap 
  x * y         = fst $ cMult     x y crCycloInitMap 
  
  negate x      = cNegate x
  abs x         = cAbs    x
  signum x      = cSignum x

-- | Checks if the Canon is Canonical, a more complex expression.
cCanonical :: Canon -> Bool
cCanonical (Can _ _) = True
cCanonical _         = False

-- | Checks if the Canon just a "Bare" Integer.
cBare :: Canon -> Bool
cBare (Bare _ _) = True
cBare _          = False

-- | Returns the status for "Bare" numbers.
cBareStatus :: Canon -> BareStatus
cBareStatus (Bare _ b) = b
cBareStatus _          = error "cBareStatus: Can only checked for 'Bare' Canons"

-- | Return the CanonValueType (Integral, etc).
cValueType :: Canon -> CanonValueType
cValueType (Bare _ _) = IntC
cValueType (Can  _ v) = v
cValueType (HX _ _ v) = v

-- | Split a Canon into the numerator and denominator.
cSplit :: Canon -> (Canon, Canon)
cSplit c = (cNumerator c, cDenominator c)

-- | Check for equality.
cEq :: Canon -> Canon -> Bool
-- cEq a b | trace ("cEq: (a=" ++ show a ++ ") and (b=" ++ show b ++ ")") False = undefined
cEq (Bare x _ )   (Bare y _ )      = x == y
cEq (Bare _ Simp) (Can _ _ )       = False
cEq (Can _ _ )    (Bare _ Simp)    = False
cEq a@(HX _ _ _)  b@(HX _ _ _)     | signum a /= signum b = False
                                   | h1 /= h2             = False -- Confirm: Always true?
                                   | h1 < cExpOpLevel     = cmpHyLists cL1 cL2 
                                   | otherwise            = cShowForEqChk a' == cShowForEqChk b' -- Note: Kludge for deeply nested numbers
                                   where (cL1:cL2:_) = map cGetHyperList [a',b']
                                         -- Quadratic compare: necessary to avoid sorting 
                                         -- which can be problematic and expensive for hyperoperations
                                         cmpHyLists x y | length x /= length y = False
                                                        | otherwise            = c' x y []
                                         c' l@(x:xs) (y:ys) bN | x == y    = c' xs (bN++ys) []
                                                               | otherwise = c' l  ys       (bN ++ [y])
                                         c' (_:_)    _      _  = False
                                         c' _        y      _  = null y 
                                         -- "Endless" looping! (a', b') = (cQuasiCanonize $ fst $ cConvertToSum a, cQuasiCanonize $ fst $ cConvertToSum b)
                                         (a', b')              = (fst $ cConvertToSum a, fst $ cConvertToSum b) -- ToDo: make this more robust?
                                         (h1, h2)              = (cGetHyperOp a', cGetHyperOp b')

cEq hx@(HX _ _ _) b                | cBare b || cMaxHyperOp hx >= cPentOpLevel 
                                               = False 
                                   | otherwise = cValueType hx == cValueType b && cGetBases hx == cGetBases b 
                                                 && (cSuperLogCmp (fst $ cSuperLog hx) (fst $ cSuperLog b) == EQ) 
                                                  -- ToDo: Verify this is robust
cEq a             hx@(HX _ _ _)    = cEq hx a
cEq (Bare x NSim) y                | cValueType y /= IntC = False
                                   | otherwise                 = x == cToI y 
cEq x             y@(Bare _ NSim) = cEq y x
cEq (Can x a )    (Can y b)       = if a /= b then False else gcrEqCheck x y

-- | Check if a Canon is integral and odd/even, respectively.  Note: Return False for both if the Canon is not integral.
--   See CanonValueType for possible cases.
cOdd, cEven :: Canon -> Bool
cOdd  = cMod2Check 1 gcrOdd
cEven = cMod2Check 0 gcrEven

cMod2Check :: Int -> (GCR_ -> Bool) -> Canon -> Bool
cMod2Check m _ (Bare x _)       = mod x 2 == toInteger m
cMod2Check _ f (Can c IntC)     = f c
cMod2Check m _ (HX PoA cL IntC) = mod (sum $ map (\c -> mod c c2) cL) 2 == smallCanons !! m -- match add "operator"
cMod2Check m _ (HX PoM cL IntC) = mod (product $ map (\c -> mod c c2) cL) 2 == smallCanons !! m -- match on mult "operator"
cMod2Check m _ (HX _   cL IntC) = mod (head cL) 2 == smallCanons !! m
cMod2Check _ _ _                = False

-- | GCD and LCM functions for Canon
cGCD, cLCM :: Canon -> Canon -> Canon
cGCD x y | cHyperExprAny x || cHyperExprAny y = head $ cMultiplicative x y Gcd 
         | otherwise                          = cLGApply gcrGCD x y
cLCM x y | cHyperExprAny x || cHyperExprAny y = head $ cMultiplicative x y Lcm
         | otherwise                          = cLGApply gcrLCM x y

-- | Compare Function (cHyperCmp is internal)
cCmp, cCmpH, cCmp' :: Canon -> Canon -> Ordering
-- cCmp a b | trace ("cCmp: (a=" ++ show a ++ ") and (b=" ++ show b ++ ")") False = undefined
cCmp (Bare x _)      (Bare y _)   = compare x y
cCmp x@(Can _ _)     y@(Bare _ _) = gcrCmp (cToGCR x) (cToGCR y)
cCmp x@(Bare _ _)    y@(Can _ _)  = gcrCmp (cToGCR x) (cToGCR y)
cCmp x@(Can _ _)     y@(Can _ _)  = gcrCmp (cToGCR x) (cToGCR y)
cCmp x@(HX _ _ _)    (Bare _ _)   = if signum x == c1 then GT else LT -- Hyperexpr always has greater magnitude
cCmp (Bare _ _)      y@(HX _ _ _) = if signum y == c1 then LT else GT -- Inverse of above
cCmp x               y            | signum y == c1 && signum x /= c1   = LT
                                  | signum x == c1 && signum y /= c1   = GT
                                  | signum x == cN1 && signum y == cN1 = cCmp (abs y) (abs x)
                                  | otherwise                          = cCmpH x y

-- At this point, we are comparing positive hyper expressions.  Should not be called directly.
-- cCmpH a b | trace ("cCmpH: (a=" ++ show a ++ ") and (b=" ++ show b ++ ")") False = undefined -- Interferes with show
cCmpH x@(Can _ _)     y@(HX _ _ _)         | not (cSuperLogGT (fst $ cSuperLog x) cSuperLogCutoff) = LT
                                           | otherwise                                             = cCmpH (cConvertToHyperExpr x) y 
cCmpH x@(HX _ _ _)    y@(Can _ _)          | not (cSuperLogGT (fst $ cSuperLog y) cSuperLogCutoff) = GT
                                           | otherwise                                             = cCmpH x (cConvertToHyperExpr y) 
cCmpH a@(HX h1 cL1 _) b@(HX h2 cL2 _) 
    | a == b                              = EQ 
    | (h1 == cAddOpLevel || h2 == cAddOpLevel) && aS /= a
                                          = cCmp aS bS 
    | (h1 == cMultOpLevel || h2 == cMultOpLevel) && aR /= a -- we don't always take this.  Otherwise, we can have an endless loop
                                          = cCmp aR bR
    | mOa > mOb + 1                       = GT 
    | mOb > mOa + 1                       = LT 
    | mOa > cHexOpLevel && mOb > cHexOpLevel && candPred a && candPred b  -- To Verify: do the bases have to match
                                          = compare (tryLiftTail a) (tryLiftTail b)  
    | flag1Less                           = cba
    | flag1More                           = cab
    | mP && exprDomination a b            = GT
    | mP && exprDomination b a            = LT
    | bP && lA' > lB'                     = GT -- ToDo: Further investigate if there are any exceptions to this?
    | bP && lA' < lB'                     = LT   
    | h1 > cMultOpLevel && h1 == h2 && dominates cL1 cL2 True  
                                          = GT 
    | h2 > cMultOpLevel && h1 >  h2 && dominates cL1 cL2 False 
                                          = GT
    | h1 > cMultOpLevel && h2 == h1 && dominates cL2 cL1 True  
                                          = LT 
    | h1 > cMultOpLevel && h2 >  h1 && dominates cL2 cL1 False 
                                          = LT
    | bP                                  = case compare (last cL1) (last cL2) of  --For large enough hyOps, last entry says which is >
                                            EQ -> compare (reduce a) (reduce b)  -- If equal try compare lists with all but last members 
                                            cmp -> cmp 
    | otherwise                           = cCmp' a b
    where (mOa, mOb, bP)         = (cMaxHyperOp a, cMaxHyperOp b, h1 == h2 && h1 > cPentOpLevel) 
          mP                     = mOa >= hyperOpCutoff && mOb >= hyperOpCutoff 
          reduce c               | len == 0  = error "Logic error in comparison: rFmt must have a hyper list with at least one entry"
                                 | len == 1  = head l
                                 | otherwise = simpleHX (cGetHyperOp c) (init l) -- create new hyper expr with all but the last entry
                                 where (l, len) = (cGetHyperList c, length l)
          (flag1Less, cba)       = (h1 >= cPentOpLevel && h2 == h1 + 1, comp1Diff b a False)  -- ToDo: Verify it handles embedded HEs.
          (flag1More, cab)       = (h2 >= cPentOpLevel && h1 == h2 + 1, comp1Diff a b True)
          
          (hLa, hLb, lHa, lHb)   = (cGetHyperList a, cGetHyperList b, length hLa, length hLb) 
          (lA', lB') | lHa > lHb = (cApplyHy h1 (drop lD hLa) True, last hLb)
                     | lHa < lHb = (last hLb,                       cApplyHy h2 (drop lD hLb) True)
                     | otherwise = (last hLa,                       last hLb)
                     where lD = abs (lHa - lHb)
          -- Modify this to see if there are any terms in common
          -- ((aS, bS), (aR, bR))   = (reduceSums a b, reduceProds a b) -- can cause endless looping
          ((aS, bS), (_,aR,bR))  = (reduceSums a b, simpleReduce a b False)

cCmpH x               y                    = error $ errorStrg -- We should never get to this spot in the code
                                             where errorStrg = "Logic error in cCmpH in program flow: " ++ show x ++ " vs. " ++ show y ++ "."

{- Two known cases that will cause loops.
   compare (3 * ((7 <^> 5) * (5 <<^>> 8 <<^>> 6)) + 17 <<^>> 5 + 4) (3 * ((7 <^> 4) * (5 <<^>> 6 <<^>> 8)) + 2)
   compare (3 * 5 <<^>> 8 <<^>> 6 + 2) ( 3 * 5 <<^>> 6 <<^>> 8 + 4)
-}

reduceSums :: Canon -> Canon -> (Canon, Canon)
reduceSums a b = (sum aS', negate $ sum bS') 
                 where (aS', bS') = partition cPositive (cGetAddends diff) -- low level diff, no infernal looping!
                       diff       = combineSum $ simpleHX cAddOpLevel (cGetAddends a ++ (map cNegate $ cGetAddends b))

reduceProds :: Canon -> Canon -> (Canon, Canon)
-- reduceProds a b | trace ("reduceProds: (a=" ++ show a ++ ") and (b=" ++ show b ++ ")") False = undefined
reduceProds a b = (aR', bR') 
                  where (_:aR':bR':_) = cMultiplicative a b Gcd 

dominates :: [Canon] -> [Canon] -> Bool -> Bool
-- dominates a b _ | trace ("dominates: (a=" ++ show a ++ ") and (b=" ++ show b ++ ")") False = undefined
dominates a' b' gtf    = d' a' b' (0 :: Integer) -- gtf indicates the underlying hyper operation level was greater in a than b
  where d' (x:xs) (y:ys) pc | x < y     = False
                            | otherwise = d' xs ys (pc + if x > y then 1 else 0)
        d' _      (_:_)  _              = False
        d' (_:_)  _      _              = True
        d' _      _      pc             = gtf || pc > 0 -- if flag set or positive ct, it dominates

-- a has a hyper operation in its base one more than b's base.  We are dealing with positive hyper expressions here
-- ToDo: what if there are hyper expressions embedded
comp1Diff :: Canon -> Canon -> Bool -> Ordering
comp1Diff a' b' cF = if cF then r else flp r -- EQ in this context means inconclusive
  where hLA@(aB:aE:_) = cGetHyperList a'
        (lA2, lB2) = (length hLA, makeCanon $ toInteger $ length $ cGetHyperList b') 
        flp r'     = case r' of
                     GT -> LT
                     LT -> GT
                     c  -> c

        r          | lA2 < ml6 = LT -- larger embedded hexation in pentated b
                   | lA2 > 2   = GT -- tower for the larger hyperoperation. e.g. 6 <<<^>>> 7 <<<^>>> 3
                                    -- would be larger than any pentation tower
                                    -- The above is equivalent to: 6 <<^>> (6 <<<^>>> 7 <<<^>>> 3 - 1)
                   | aE > lB2  = GT -- The "exponent" for the larger is greater than the length of the smaller
                                    -- For instance: 5 <<^>> 7 <<^>> 8 would be less than 6 <<<^>>> 4.
                   | aE < lB2  = LT
                     -- e.g. Downgrade a =  6 [6,3] to 5 [6,6,6] and compare it to b (aE == lB)
                   | otherwise = compare (simpleHX (cGetHyperOp b') (replicate (fromInteger $ cToI aE) aB)) b'

        ml6        = maxHypLen cHexOpLevel b'

-- ToDo:adapt this so it finds the maximum chunk?
-- maximum length of list based on hyper operation. Assumed to be the maximum in the expression
maxHypLen :: Canon -> Canon -> Int
maxHypLen h c = mhl c 0 
                where mhl c' mx | cHyperExprAny c' = if cGetHyperOp c' == h 
                                                     then max mx (length cL)
                                                     else (foldl1 max $ map (maxHypLen h) cL)
                                | otherwise        = 0              
                                where cL = cGetHyperList c'                    
hyperOpCutoff :: Canon
hyperOpCutoff = cTetrOpLevel 

-- unsigned values are assumed.  This checks if s is less than d or less than a subexpression of d
exprDomination :: Canon -> Canon -> Bool
-- exprDomination d s | trace ("exprDomination: (s=" ++ show s ++ ") and (d=" ++ show d ++ ")") False = undefined
exprDomination d s = eD d s False -- The flag indicates what whether we are already embedded or not in the structure

eD :: Canon -> Canon -> Bool -> Bool
-- eD d' s' b' | trace ("eD: (d' = " ++ show d' ++ ", s' = " ++ show s' ++ ", b' = " ++ show b' ++ ")") False = undefined
eD d' s' b' | notBoth s' d' && not b'     = s' < d'   -- first level check
            | notBoth s' d' && b'         = s' <= d'
            | s' == d'                    = b' -- equality shows domination if at an inner level 
            | s' /= sRp                   = eD dRp sRp b'
            | rC                          = rC
            | b' && (compare d' s' /= LT) = True -- (if inside the nested expression).  Could be expensive.
            | otherwise                   = False
            -- at last check if individual items in list dominate
            where notBoth x y = not (cMaxHyperOp x >= hyperOpCutoff  && cMaxHyperOp y >= hyperOpCutoff)
                  (sRs, dRs) = if b' && (cHyperSum s'   || cHyperSum d')   then reduceSums s' d' else (s', d')
                  (sRp, dRp) = if b' && (cHyperProd sRs || cHyperProd dRs) then reduceProds sRs dRs else (sRs, dRs)
                  rC         = any (\e -> eD e s' False || eD e s' True) $ cGetHyperList d'

-- Fall back comparison function.  If the numbers are small enough and sufficiently close, 
-- they will be converted back to integers and compared.  We are dealing with positive hyper expressions here.
-- cCmp' a b | trace ("cCmp': (a=" ++ show a ++ ") and (b=" ++ show b ++ ")") False = undefined
cCmp' a b | aH == cPentOpLevel && bH == cTetrOpLevel && any cHyperExprAny (cGetHyperList b) && cSuperLogGT slb sla
                                 = LT -- pentation vs. nested tetration
          | bH == cPentOpLevel && aH == cTetrOpLevel && any cHyperExprAny (cGetHyperList a) && cSuperLogGT sla slb
                                 = GT -- nested tetration vs. pentation
          | aH >= cPentOpLevel && aH > bH -- Note: comp1Diff handles the case where aH = bH + 1
                                 = GT
          | bH >= cPentOpLevel && bH > aH  
                                 = LT
          | aH <= cTetrOpLevel && bH <= cTetrOpLevel && cSuperLogGT sla slb
                                 = GT
          | aH <= cTetrOpLevel && bH <= cTetrOpLevel && cSuperLogGT slb sla
                                 = LT
          | bBh == cPentOpLevel && aBh == bBh
                                 = pCmp a b 
          | aBh == cAddOpLevel || bBh == cAddOpLevel || cmpAddends /= EQ
                                 = cmpAddends
          | aBh == cMultOpLevel || bBh == cMultOpLevel || cmpFactors /= EQ
                                 = cmpFactors
          | aBh == bBh && aBh > cMultOpLevel && cmpHyperList /= EQ
                                 = cmpHyperList -- ToDo:  
          -- Note: super log is only practical <= level 10
          | cSuperLogGT sla slb  = GT -- These two checks will handle cases like: compare (5 <^> 8 <<^>> 6) (17 <<^>> 5)
          | cSuperLogGT slb sla  = LT
          | otherwise            = error $ "Unable to accurately compare a = " ++ show a ++ " and b = " ++ show b
          where (aH, bH)     = (cMaxHyperOp a, cMaxHyperOp b)
                (aBh, bBh)   = (cGetHyperOp a, cGetHyperOp b)
                (sla, slb)   = (fst $ cSuperLog a, fst $ cSuperLog b)
                cmpList f    = compare (sort $ f a) (sort $ f b)
                cmpAddends   = cmpList cGetAddends
                cmpFactors   = cmpList cGetFactors
                cmpHyperList = cmpList cGetHyperList

-- Only for pentation check
pCmp :: Canon -> Canon -> Ordering
pCmp a b | pA > pB = GT
         | pA < pB = LT
         | otherwise   = cSuperLogCmp sla' slb'
         where pTail x  = cApplyHy aBh (tail $ cGetHyperList x) False
               (pA, pB) = (pTail a, pTail b)
               sl x t   = fst $ cSuperLog $ simpleHX aBh (x:[t - m + 2]) 
               sla'     = sl (head $ cGetHyperList a) pA
               slb'     = sl (head $ cGetHyperList b) pB
               m        = min pA pB
               aBh      = cGetHyperOp a

-- | wrapper to create apply a hyperoperation to a list 
cApplyHy :: Canon -> [Canon] -> Bool -> Canon -- the Bool says whether to raise an error for a null list
cApplyHy ho a b = if length a == 0 && b 
                 then error "cApplyHy: Null list passed. Specified as fatal condition by calling fcn"
                 else fst (cHyperOp ho a crCycloInitMap) -- This function will do any simplifications 

-- | Find the maximum hyperoperation embedded in a Canon
cMaxHyperOp :: Canon -> Canon
cMaxHyperOp = findSigHyOp max

-- | Find the minimum hyperoperation embedded in a Canon.  (If not at all, return zer0
cMinHyperOp :: Canon -> Canon
cMinHyperOp = findSigHyOp mHo 
              where mHo a b | a == b    = a
                            | a == c0   = b
                            | b == c0   = a
                            | otherwise = min a b

-- Can be called with f = max or mHo
findSigHyOp :: (Canon -> Canon -> Canon) -> Canon -> Canon
findSigHyOp _ (Bare _ _)  = c0
findSigHyOp f (Can g _)   = foldl1 f $ map runningSig g
                            where runningSig (_, e) | e == c1   = cMultOpLevel 
                                                    | otherwise = f cExpOpLevel (findSigHyOp f e) -- at least exp
findSigHyOp f (HX h hl _) = f h (foldl1 f $ map (findSigHyOp f) hl) 

-- | QuotRem Function
cQuotRem :: Canon -> Canon -> CycloMap -> ((Canon, Canon), CycloMap)
cQuotRem x y m | cHyperExprAny x || cHyperExprAny y = ((hQ, c0), mR) -- ToDo: Handle non-zero modulus, say if x is a sum.
               | cIntegral x && cIntegral y         = ((gcrToC q', md'), m'')
               | otherwise                          = error "cQuotRem: Must both parameters must be integral."
               where (q', md', m'') = case gcrDiv (cToGCR x) gy of
                                      Left  _        -> (q,        md, m')
                                      Right quotient -> (quotient, c0, m)
                                      where gy       = cToGCR y
                                            md       = cMod x y
                                            q        = gcrDivStrict (cToGCR d) gy  -- equivalent to: (x - mod x y) / y.
                                            (d, m')  = cSubtract x md m
                     (hQ, mR)       = cDiv x y m

-- | Mod function
cMod :: Canon -> Canon -> Canon
-- cMod c m | trace ("cMod: (c=" ++ show c ++ "), m=" ++ show m ++ ")") False = undefined
cMod c m | not (cIntegral c) || not (cIntegral m) 
                         = error "cMod: Must both parameters must be integral" 
         | c < m         = c
         | m == cGCD c m = c0 -- c is a multiple of m. If m is a hyper expr, this all we can do for now
         | otherwise     = makeCanon $ cModI c (cToI m)                          

-- | Mod function between a Canon and integer.  This is usually called by cMod
cModI :: Canon -> Integer -> Integer
-- cModI c m | trace ("cModI: (c=" ++ show c ++ "), m=" ++ show m ++ ")") False = undefined
cModI _   0       = error "cModI: Divide by zero error when computing n mod 0"
cModI _   1       = 0
cModI _   (-1)    = 0
cModI Pc1 PIntPos = 1
cModI Pc0 _       = 0
cModI c   m       | cn && mn         = -1 * cma
                  | (cn && not mn) ||
                    (mn && not cn)   = signum m * ((abs m) - cma)
                  | otherwise        = cModI' c m
                  where (cn, mn, cma)             = (cNegative c, m < 0, cModI' (abs c) (abs m))
                        -- cModI' b m' | trace ("cModI' (b=" ++ show b ++ "), m'=" ++ show m' ++ ")") False = undefined
                        cModI' (Bare n _)      m' = mod n m'
                        cModI' (Can c' _)      m' = if c == makeCanon m' then 0 else mod (product $ map pM c') m' 
                                                    where pM (b,e) = if (mod b m' == 0) then 0 else (pmI b (mmt e) m')
                                                          mmt e = cModI e (totient m') -- optimization
                        cModI' (HX PoA cL _)   m' = mod (sum $ map (\ce -> cModI ce m') cL) m'
                        cModI' h@(HX PoM cL _) m' = if (cModI (product $ cGetBases h) m' == 0)
                                                    then 0 -- simple check if the bases are a multiple of the modulus
                                                    else mod (product $ map (\ce -> cModI ce m') cL) m'
                        cModI' (HX PoE cL _)   m' = cModI (foldr1 (<^) (b':tail cL)) m' -- convert it a power tower
                                                    where b' = makeCanon $ cModI (head cL) m'
                        cModI' (HX h cL _)     m' | h == cTetrOpLevel && length cL == 2 && 
                                                    not (cHyperExprAny (cL !! 1)) && totient twrHeight > m'
                                                              = cModHyTwr (head cL) m' twrHeight -- exp
                                                  | otherwise = cModHyper (head cL) m' -- to infinity and beyond :)
                                                  where twrHeight = cToI $ cL !! 1

                        -- https://www.quora.com/What-would-be-the-remainder-if-Grahams-number-were-divided-by-2-4-5-6-7-8-9-or-10
                        -- ToDo : Optimize this for larger m especially powers of 10 to show trailing digits
                        -- cModHyper b m' | trace ("cModHyper: (b=" ++ show b ++ "), m'=" ++ show m' ++ ")") False = undefined
                        cModHyper b m' | (all (\e -> elem e bB) $ cGetBases $ mC') = 0 -- the base of a hyper expression must be multiple of m' 
                                       | otherwise                                 = cToI $ f mC'
                                       where (bB, mC') = (cGetBases b, makeCanon m')
                                             -- f mC | trace ("f: (mC=" ++ show mC ++ ")") False = undefined
                                             f mC | mC == c2   = if cEven b then c0 else c1
                                                  | otherwise  = cMod (b <^ f phi) mC
                                                  where phi = fst $ cPhi mC crCycloInitMap

                        -- ToDo: Optimize: This runs in linear time. It could leverage the information above if "f phi" is low enough
                        -- cModHyTwr b m' s | trace ("cModHyTwr: (b=" ++ show b ++ "), m'=" ++ show m' ++ ", s = " ++ show s ++ ")") False = undefined
                        cModHyTwr b m' s           | r == 0    = 0 
                                                   | otherwise = cToI $ cm' (s-1) r
                                                   where r        = makeCanon $ cModI b m'  
                                                         cm' y lv | y == 0    = nv -- at end
                                                                  | otherwise = cm' (y-1) nv 
                                                                  where nv = makeCanon $ cModI (r <^ lv) m'
-- | Totient functions
cTotient, cPhi :: Canon -> CycloMap -> (Canon, CycloMap)
cTotient c m | (not $ cIntegral c) || cNegative c = error "Not defined for non-integral or negative numbers"
             | not $ cSimplified c                      = error "cTotient Can't compute if number not completely factored"
             | c == c0                            = (c0, m)
             | otherwise                          = f (cToGCR c) c1 m
             where f []         prd m' = (prd, m') 
                   f ((p,e):gs) prd m' = f gs wp mw 
                   -- f is equivalent to the crTotient function but with threading of CycloMap 
                   -- => product $ map (\(p,e) -> (p-1) * p^(e-1)) cr
                                         where cp           = makeCanon p 
                                               -- "Canon-ize" cp above.  Generally, this should be a prime already
                                               (pM1, mp)    = cSubtract cp c1 m'
                                               (eM1, me)    = cSubtract e c1 mp 
                                               (pxeM1, mpm) = cExp cp eM1 False me
                                               (nprd, mprd) = cMult pM1 pxeM1 mpm    
                                               (wp, mw)     = cMult prd nprd  mprd

cPhi = cTotient


-- | The thinking around the hyperoperators is that they should look progressively scarier :)
-- | They range from level 4 / tetration (<^>) to level 50 (~~~~~^~~~~~). Please read .odp file for the naming convention.
infixr <^>, <<^>>, <<<^>>>, <<<<^>>>>, <<<<<^>>>>>, |<^>|,                                  -- 4-9
       ~^~, ~<^>~, ~<<^>>~, ~<<<^>>>~, ~<<<<^>>>>~,                                         -- 10-14
       ~|^|~, ~|<^>|~, ~|<<^>>|~, ~|<<<^>>>|~, ~|<<<<^>>>>|~,                               -- 15-19
       ~~^~~, ~~<^>~~, ~~<<^>>~~, ~~<<<^>>>~~, ~~<<<<^>>>>~~,                               -- 20-24
       ~~|^|~~, ~~|<^>|~~, ~~|<<^>>|~~, ~~|<<<^>>>|~~, ~~|<<<<^>>>>|~~,                     -- 25-29
       ~~~^~~~, ~~~<^>~~~, ~~~<<^>>~~~, ~~~<<<^>>>~~~, ~~~<<<<^>>>>~~~,                     -- 30-34
       ~~~|^|~~~, ~~~|<^>|~~~, ~~~|<<^>>|~~~, ~~~|<<<^>>>|~~~, ~~~|<<<<^>>>>|~~~,           -- 35-39
       ~~~~^~~~~, ~~~~<^>~~~~, ~~~~<<^>>~~~~, ~~~~<<<^>>>~~~~, ~~~~<<<<^>>>>~~~~,           -- 40-44
       ~~~~|^|~~~~, ~~~~|<^>|~~~~, ~~~~|<<^>>|~~~~, ~~~~|<<<^>>>|~~~~, ~~~~|<<<<^>>>>|~~~~, -- 45-49
       ~~~~~^~~~~~                                                                          -- FIFTY

(<^>), (<<^>>), (<<<^>>>), (<<<<^>>>>), (<<<<<^>>>>>), (|<^>|),                                  -- 4-9
  (~^~), (~<^>~), (~<<^>>~), (~<<<^>>>~), (~<<<<^>>>>~),                                         -- 10-14
  (~|^|~), (~|<^>|~), (~|<<^>>|~), (~|<<<^>>>|~), (~|<<<<^>>>>|~),                               -- 15-19
  (~~^~~), (~~<^>~~), (~~<<^>>~~), (~~<<<^>>>~~), (~~<<<<^>>>>~~),                               -- 20-24
  (~~|^|~~), (~~|<^>|~~), (~~|<<^>>|~~), (~~|<<<^>>>|~~), (~~|<<<<^>>>>|~~),                     -- 25-29
  (~~~^~~~), (~~~<^>~~~), (~~~<<^>>~~~), (~~~<<<^>>>~~~), (~~~<<<<^>>>>~~~),                     -- 30-34
  (~~~|^|~~~), (~~~|<^>|~~~), (~~~|<<^>>|~~~), (~~~|<<<^>>>|~~~), (~~~|<<<<^>>>>|~~~),           -- 35-39
  (~~~~^~~~~), (~~~~<^>~~~~), (~~~~<<^>>~~~~), (~~~~<<<^>>>~~~~), (~~~~<<<<^>>>>~~~~),           -- 40-44
  (~~~~|^|~~~~), (~~~~|<^>|~~~~), (~~~~|<<^>>|~~~~), (~~~~|<<<^>>>|~~~~), (~~~~|<<<<^>>>>|~~~~), -- 45-49
  (~~~~~^~~~~~)                                                                                  -- FIFTY
    :: Canon -> Canon -> Canon

a         <^>         b = cTetration a b
a        <<^>>        b = cPentation a b
a       <<<^>>>       b = cHexation  a b
a      <<<<^>>>>      b = cHeptation a b
a     <<<<<^>>>>>     b = cOctation  a b
a        |<^>|        b = cNonation  a b
a         ~^~         b = cApplyHy (makeCanon 10) [a,b] True
a        ~<^>~        b = cApplyHy (makeCanon 11) [a,b] True
a       ~<<^>>~       b = cApplyHy (makeCanon 12) [a,b] True
a      ~<<<^>>>~      b = cApplyHy (makeCanon 13) [a,b] True
a     ~<<<<^>>>>~     b = cApplyHy (makeCanon 14) [a,b] True
a        ~|^|~        b = cApplyHy (makeCanon 15) [a,b] True
a       ~|<^>|~       b = cApplyHy (makeCanon 16) [a,b] True
a      ~|<<^>>|~      b = cApplyHy (makeCanon 17) [a,b] True
a     ~|<<<^>>>|~     b = cApplyHy (makeCanon 18) [a,b] True
a    ~|<<<<^>>>>|~    b = cApplyHy (makeCanon 19) [a,b] True
a        ~~^~~        b = cApplyHy (makeCanon 20) [a,b] True
a       ~~<^>~~       b = cApplyHy (makeCanon 21) [a,b] True
a      ~~<<^>>~~      b = cApplyHy (makeCanon 22) [a,b] True
a     ~~<<<^>>>~~     b = cApplyHy (makeCanon 23) [a,b] True
a    ~~<<<<^>>>>~~    b = cApplyHy (makeCanon 24) [a,b] True
a       ~~|^|~~       b = cApplyHy (makeCanon 25) [a,b] True
a      ~~|<^>|~~      b = cApplyHy (makeCanon 26) [a,b] True
a     ~~|<<^>>|~~     b = cApplyHy (makeCanon 27) [a,b] True
a    ~~|<<<^>>>|~~    b = cApplyHy (makeCanon 28) [a,b] True
a   ~~|<<<<^>>>>|~~   b = cApplyHy (makeCanon 29) [a,b] True
a       ~~~^~~~       b = cApplyHy (makeCanon 30) [a,b] True
a      ~~~<^>~~~      b = cApplyHy (makeCanon 31) [a,b] True
a     ~~~<<^>>~~~     b = cApplyHy (makeCanon 32) [a,b] True
a    ~~~<<<^>>>~~~    b = cApplyHy (makeCanon 33) [a,b] True
a   ~~~<<<<^>>>>~~~   b = cApplyHy (makeCanon 34) [a,b] True
a      ~~~|^|~~~      b = cApplyHy (makeCanon 35) [a,b] True
a     ~~~|<^>|~~~     b = cApplyHy (makeCanon 36) [a,b] True
a    ~~~|<<^>>|~~~    b = cApplyHy (makeCanon 37) [a,b] True
a   ~~~|<<<^>>>|~~~   b = cApplyHy (makeCanon 38) [a,b] True
a  ~~~|<<<<^>>>>|~~~  b = cApplyHy (makeCanon 39) [a,b] True
a      ~~~~^~~~~      b = cApplyHy (makeCanon 40) [a,b] True
a     ~~~~<^>~~~~     b = cApplyHy (makeCanon 41) [a,b] True
a    ~~~~<<^>>~~~~    b = cApplyHy (makeCanon 42) [a,b] True
a   ~~~~<<<^>>>~~~~   b = cApplyHy (makeCanon 43) [a,b] True
a  ~~~~<<<<^>>>>~~~~  b = cApplyHy (makeCanon 44) [a,b] True
a     ~~~~|^|~~~~     b = cApplyHy (makeCanon 45) [a,b] True
a    ~~~~|<^>|~~~~    b = cApplyHy (makeCanon 46) [a,b] True
a   ~~~~|<<^>>|~~~~   b = cApplyHy (makeCanon 47) [a,b] True
a  ~~~~|<<<^>>>|~~~~  b = cApplyHy (makeCanon 48) [a,b] True
a ~~~~|<<<<^>>>>|~~~~ b = cApplyHy (makeCanon 49) [a,b] True
a     ~~~~~^~~~~~     b = cApplyHy (makeCanon 50) [a,b] True

cTetration, cPentation, cHexation, cHeptation, cOctation, cNonation :: Canon -> Canon -> Canon

-- | Tetration Function - Level 4
cTetration a b = cApplyHy cTetrOpLevel [a,b] True

-- | Pentation Function - Level 5
cPentation a b = cApplyHy cPentOpLevel [a,b] True

-- | Hexation Function - Level 6
cHexation a b  = cApplyHy cHexOpLevel  [a,b] True

-- | Heptation Function - Level 7
cHeptation a b = cApplyHy cHeptOpLevel [a,b] True

-- | Octation Function -- Level 8
cOctation a b  = cApplyHy cOctOpLevel  [a,b] True

-- | Nonation Function -- Level 9
cNonation a b  = cApplyHy cNonOpLevel  [a,b] True

-- | Hyperoperation List Operators.  On display, the towers will have single caret operators interspersed.
infixr 9 <^^>, <<^^>>, <<<^^>>>, <<<<^^>>>>, <<<<<^^>>>>>, |<^^>|

(<^^>), (<<^^>>), (<<<^^>>>), (<<<<^^>>>>), (<<<<<^^>>>>>), (|<^^>|) :: Canon -> [Canon] -> Canon

a     <^^>     b = fst $ cTetrationL a b crCycloInitMap
a    <<^^>>    b = fst $ cPentationL a b crCycloInitMap
a   <<<^^>>>   b = fst $ cHexationL  a b crCycloInitMap
a  <<<<^^>>>>  b = fst $ cHeptationL a b crCycloInitMap
a <<<<<^^>>>>> b = fst $ cOctationL  a b crCycloInitMap
a    |<^^>|    b = fst $ cNonationL  a b crCycloInitMap

cTetrationL, cPentationL, cHexationL, cHeptationL, cOctationL, cNonationL
   :: Canon -> [Canon] -> CycloMap -> (Canon, CycloMap)

-- | Tetration List Function
cTetrationL a b m = cHyperOp cTetrOpLevel (a:b) m

-- | Pentation List Function
cPentationL a b m = cHyperOp cPentOpLevel (a:b) m

-- | Hexation List Function
cHexationL a b m  = cHyperOp cHexOpLevel  (a:b) m

-- | Heptation List Function
cHeptationL a b m = cHyperOp cHeptOpLevel (a:b) m 

-- | Octation List Function
cOctationL a b m  = cHyperOp cOctOpLevel (a:b) m

-- | Nonation List Function
cNonationL a b m  = cHyperOp cNonOpLevel (a:b) m 

-- | Generalized Hyperoperation Function (https://en.wikipedia.org/wiki/Hyperoperation)
cHyperOp :: Canon -> [Canon] -> CycloMap -> (Canon, CycloMap)
-- cHyperOp n l _ | trace ("cHyperOp: (ho=" ++ show n ++ "), l=" ++ show l ++ ")") False = undefined
cHyperOp n l@(a:b:cs) m 
   | any (not . cIntegral) (n:l)    = error "cHyperOp requires the 1st 2 parameters to be integral at this time."
   | b < cN1 && n > cExpOpLevel     = error $ hyperLvlError b n 
   | n > c2 && any cNegative (b:cs) = error "cHyperOp: At this time, all trailing entries must be >= 0 when using exponentiation or greater."
   | cNegative a && n > c3          = error "cHyperOp: At this time, the base must be >= 0 when using tetration or greater."
   | cNegative a && n == c3         = (if oddPwr then negate absHe else absHe, m)
   | n < c0                         = error "cHyperOp: Requires the level n >= 0"
   | any (== c0) l                  = if n == cAddOpLevel then filterV c0 
                                                          else (if n == cMultOpLevel then (c0, m) else stripVs c0)
   | any (== c1) l && n > cAddOpLevel
                                    = if n == cMultOpLevel then filterV c1 else stripVs c1
   | (a /= c0 && a /= c1 && b > c1 && not (a == c2 && b == c2)) ||
     n == c1 || n == c2             = tryToDemoteOrPromote  
   | null cs'                       = cHyperOpSpecial (toInteger n) a b m 
   | otherwise                      = error "Can not handle special cases with more than 2 params at this time" 
   where -- ToDo: Weave in the cycloMap
         -- Note: This tetration demotion logic is closely tied to the cSuperLogCutoff
         -- The idea that anything internally considered as a hyperexpression must be greater than
         -- the cutoff which is currently 10^10^5.  Even 22934 ^ 22934
         absHe                      = fst $ cHyperOp n ((abs a):b:cs) m
         oddPwr                     = cOdd $ fst $ cHyperOp n (b:cs) m
         tryToDemoteOrPromote 
           | n == cAddOpLevel  = (sum l, m) 
           | n == cMultOpLevel = (product l, m) 
           | hyperFree && n == cExpOpLevel  = (foldr1 (<^) l, m) -- Note: The underlying function calls cHyperOp for hyper expressions
           | n == cPentOpLevel && l == [c3, c3] -- expand to 3 <^> 3 <^> 3 so it can be reduced
             = (c3 <^> c3 <^> c3, m)
           | null cs && n == cTetrOpLevel && b == 2
             = (a <^ a, m) -- tetration to exp
           | null cs && n > cTetrOpLevel  && b == 2
             = if cGetHyperOp a == nM1
               then (cApplyHy nM1 (a:(cGetHyperList a)) True, m) -- e.g. (3<^>4) <<^>> 2 => (3<^>4)<^>3<^>4
               else (cApplyHy nM1 [a,a] True, m)          -- e.g. can't append: (3<<^>>4) <<^>> 2 = (3<<^>>4)<<^>>(3<<^>>4)
           | a == 2 &&
             (
              ((null cs &&
                ((n == 5 && b == 3) ||
                 (n == 4 && b == 4))
               ) ||
               (length cs == 1 && head cs == 2 && n == 4 && b == 2)
              )
             )
             = (makeCanon (65536 :: Integer), m) -- 2^2^2^2 = 2 <^> 4 = 2 <^> 2 <^> 2 = 2 <<^>> 3
           | a == 2 && b == 3 && null cs -- 2 <<<^>>> 3 = 2 <<^>> (2 <<^>> 2) = 2 <<^>> 4 -- Special demotion case for 2
             = (cApplyHy nM1 [a, c4] True, m)
           | a == 2 && b == 4 && null cs && n == 5
             = (cApplyHy nM1 [a, cApplyHy n [a, b - 1] True] True, m) -- another demotion: 2 <<^>> 4 = 2 <^> 65536. Both help with comparisons
           | null cs &&
             ((a <= 6 && n == 4 && b == 3) ||
              (a == 3 && n == 5 && b == 2))
             = (a <^ a <^ a, m)
           | ((lL > 2 && n > cMultOpLevel) || (lL >= 2 && n <= cMultOpLevel)) && sameVal l
             -- e.g. (1 + 5<^>7) ^ (1 + 5<^>7) ^ (1 + 5<^>7) = (1+ 5<^>7) <^> 3
             = (promotedC, m)
           | otherwise
             = (cleanup b, m) 
           where nM1            = n - c1
                 hyperFree      = not $ any cHyperExprAny l
                 sameVal (x:xs) = s' xs 
                                  where s' (v:vs) | v == x    = s' vs
                                                  | otherwise = False
                                        s' _      = True
                 sameVal _      = error "cHyperOp: List with at least two items expected"
                 (lL, lenC)     = (length l, makeCanon $ toInteger lL)
                 promotedC      = case n of
                                  1 -> (head l) * lenC
                                  2 -> (head l) <^ lenC
                                  _ -> cApplyHy (n+1) [head l, lenC] True

         cs' = if b == c1 then [] else cs -- blank out cs if b == 1 -- ToDo : always correct? 
         defHypEx = HX n l IntC -- this just takes the input and creates a HyExp. Might not be what's returned later

         filterV v = (cApplyHy n (filter (/= v) l) False, m)
         stripVs v = (cApplyHy n nl False, m)
                     where nl            = if v == c0 then s l [] 
                                                      else (fst $ span (/= v) l) -- e.g. [2,3,1,4,5] -> [2,3]
                           s (x:xs) wl = if x == c0 
                                         then (if (ct0 xs 0) == 1 
                                               then wl -- two trailing zeros evaulate to 1
                                               else (if length wl > 0 then init wl else [])
                                              )
                                         else s xs (wl ++ [x])
                                         where ct0 (y:ys) ct = if y == c0 then ct0 ys (ct+1) else ct
                                               ct0 _      ct = ct :: Integer
                           s _      _  = error "Logic error in strip0: should not get to the end"
                     
                     -- Examples [2,3,4,0,5] => 0^5 = 0 so [2,3,4,0] -> [2,3,1] -> [2,3]
                     -- for 0    [2,3,4,0,0] => 0^0 = 1 so [2,3,4,1] -> [2,3,4]
                     --          [2,3,0,0,0] => [2,3,0,1] -> [2,3,0] -> [2,1] -> [2]

         -- Upgrade Chain Example Below n = 4, a = 7, b = HX (n+1) [a, 13] IntC => HX 5 [7,13] IntC
         -- Then, the answer should be HX (n+1) [a,t+1] IntC = HX 5 [7,14] IntC 
         -- 7 <^> (7 <<^>> 13) simplifies to 7 <<^>> 14
         -- Function for regular cases
         -- cleanup n'  | trace ("cleanup: Processing: (ho=" ++ show n' ++ ")") False = undefined 
         cleanup (HX h cL@(a':e:xs) _)   
           | a == a' && h == n + c1 && null xs && null cs 
                                            = cApplyHy h [a, e + c1] False --  Upgrade Chain 
           | h == n && null cs              = cApplyHy h (a:cL) False -- combine into longer chain: 5<^>(7<^>7) = 5<^>7<^>7
           | n == eL && cGetHyperOp a == mL = distProdForExpo
           | otherwise                      = defHypEx
         cleanup _ 
           | n == eL && cGetHyperOp a == mL = distProdForExpo
           | otherwise                      = defHypEx

         distProdForExpo = computeExpr mL $ map (\p -> f (p:es)) $ cGetHyperList b' -- dist expo if it can't be upgraded
           where (b':es)  = l
                 f l'@(x:xs) | cGetHyperOp x == eL = computeExpr eL [bX, eXEval * computeExpr eL xs] -- (x^a)^b = x^(a*b) 
                             | cHyperExprAny x     = computeExpr eL l'
                             | otherwise           = foldr1 (<^) l'
                             where (bX:eX) = cGetHyperList x
                                   eXEval  = computeExpr eL eX
                 f _      = error "Logic Error: Empty list found in cleanup"

         (mL, eL) = (cMultOpLevel, cExpOpLevel)

cHyperOp h (a:_)  m  | h < c0 || not (cIntegral h) = error "cHyperOp: Hyper operator must be >= 0 and integral"
                     | otherwise                   = (a, m)
cHyperOp h l      m  | h < cAddOpLevel || not (cIntegral h) 
                                    = error "cHyperOp: Nullary value not defined if hyper operator is lower than addition"
                     | h == cAddOpLevel = (sum l, m)
                     | otherwise        = (product l, m)

hyperLvlError :: Canon -> Canon -> String
hyperLvlError b n = "cHyperOp: Hyperexpr not defined when b < -1 and n is beyond exponentiation. b = " ++ 
                    show b ++ ", n = " ++ show n ++ "."

-- go through the map and flatten any sums/products in the list
-- take the list. partition it by having "hyper" expressions or not.  Collapse the non-hyper entries
cFlattenAndGroup :: Canon -> [Canon]
--cFlattenAndGroup c | trace ("cFlattenAndGroup: Processing: (c=" ++ show c ++ ")") False = undefined 
cFlattenAndGroup c = cFlattenAndGroup' c cMaxExpoToExpand

cFlattenAndGroup' :: Canon -> Canon -> [Canon] 
cFlattenAndGroup' c mx
  | n1 == cAddOpLevel || n1 == cMultOpLevel = fAndG
  | otherwise                               = [c]
  where n1        = cGetHyperOp c -- hyper op from input
        (cA,n,cL) = (abs c, cGetHyperOp cA, cGetHyperList cA) 
        fAndG     = fmt (gF nH) (sF h)
                    where (gF, tF, sF)  | n == cAddOpLevel = (sum,     tryFlatSum,  sortByHpo)
                                        | otherwise        = (product, tryFlatProd, id)
                          (h, nH)       = partition cHyperExprAny $ concat $ map tF cL
                          fmt nonHC hyL | n == cAddOpLevel && nonHC == c0  = hyL
                                        | n == cMultOpLevel && nonHC == c1 = hyL
                                        | otherwise                        = (nonHC:hyL)
                          tryFlatSum v  | cGetHyperOp v' == cAddOpLevel = cGetHyperList v'
                                        | otherwise                     = [v']
                                        where v' = fst $ cConvertToSum' v mx
                          tryFlatProd v | cGetHyperOp v == cMultOpLevel  = cGetHyperList v
                                        | otherwise                      = [v]
        -- When operating on a sum, we can flatten some products and distribute them
        -- ToDo: Factor algebraic expressions with hyperoperations.

-- Elements with more hyper expressions in base are sorted first.  The lists of hyper ops are sorted in descending
-- order.  Products of equal "hyper length" will then be compared by the lists.
sortByHpo :: [Canon] -> [Canon]
-- sortByHpo v | trace ("sortByHpo: Processing v = " ++ show v ++ ".") False = undefined
sortByHpo l' | length l' == 1 = l'
             | otherwise      = filter (/= c0) $ map collHy $ groupBy (\x y -> snd x == snd y) $ 
                                sortBy sHPO $ map hpo $ map combineProd l'  -- This groups by hyOps, bases pair
             where collHy z = combineSum $ computeExpr cAddOpLevel (map fst z) 

-- allows for crude sorting without doing any heavy lifting
type CanonInfo = ([Canon], ([[Canon]], [Canon])) -- ([bases], ([["exponents"]],[hyper ops'])) 

combineProd, combineSum :: Canon -> Canon
-- combineProd c | trace ("combineProd: Processing c = " ++ show c ++ ".") False = undefined
combineProd c | cGetHyperOp c' == cMultOpLevel = simpleHX c2 (map fst $ reverse $ sortBy sHPO $ map hpo $ cGetHyperList c') 
              | otherwise                      = c'
              where c' = if cNegative c then negate aCm else aCm
                         where aCm = combine cMultOpLevel $ abs c

combineSum  c = combine cAddOpLevel c

combine :: Canon -> Canon -> Canon
-- combine h c | trace ("combine: Processing h = " ++ show h ++ ", c = " ++ show c ++ ".") False = undefined
combine h c | length (cGetHyperList c) < 2 || cGetHyperOp c /= h 
                               = c
            | nH == nullary    = computeExpr h cLc
            | h == cAddOpLevel = computeExpr h (cLc ++ [nH]) -- leave non-hyper expressions at the end
            | otherwise        = computeExpr h (nH:cLc)
            where (nH, cL') = (if h == cMultOpLevel then prepM else prepA) c
                  cLc       = if null cL' then [] else (combine' (tail cL') [head cL'] []) -- can be null for sums
                              -- use the quadratic check logic and group them together
                  -- factors (multiplicands)
                  -- prepM c | trace ("prepM: Processing c=" ++ show c ++ ".") False = undefined
                  prepM (HX PoE (b:es) _) = (c1, [(b, computeExpr nxtOp es)])
                  prepM c'@(HX PoM _   _) = (fld nHe, concat $ map (snd . prepM) hE)
                                            where (hE, nHe) = partition cHyperExpr $ cFlattenAndGroup c'
                  prepM c'@(HX _ _     _) = (c1, [(c', c1)])
                  prepM c'                = (c', [])

                  -- addends
                  prepA (HX PoM l  _) = (c0, [(computeExpr nxtOp hE, product nHe)])
                                        where (hE, nHe) = partition cHyperExpr l
                  prepA (HX PoA l  _) = (fld nHe, concat $ map (snd . prepA) hE) 
                                        where (hE, nHe) = partition cHyperExpr l
                  prepA c'@(HX _ _ _) = (c0, [(c', c1)])
                  prepA c'            = (c', [])

                  -- combine' c l wL | trace ("combine': Processing c=" ++ show c ++ ", l=" ++ show l ++", wL=" ++ show wL ++ ".") False = undefined
                  combine' l@((xB,xE):xs)    (yP@(yB,yE):ys)   wL
                    | xB == yB  = combine' xs (wL ++ combinedTerm ++ ys) []
                    | otherwise = combine' l ys (yP:wL)
                    where combinedTerm = if (xE + yE == c0) then [] else [(xB, xE + yE)]
                  combine' (xP:xs)           _                 wL
                    = combine' xs (xP:wL) []
                  combine' _                 y                 _
                    = map f y -- this is the simplified list
                      where f (b,e)              | e == c1                = b
                                                 | cGetHyperOp e == nxtOp = computeExpr nxtOp (b:cGetHyperList e)
                                                 | otherwise              = computeExpr nxtOp [b, e]

                  (fld, nullary,nxtOp) | h == cAddOpLevel       = (sum,     c0, cMultOpLevel)
                                       | otherwise              = (product, c1, cExpOpLevel)


-- ToDo: Modify so that there are pairs of numbers when there are repeated exponents?  Or is this close enough?
hpo :: Canon -> (Canon, CanonInfo)
hpo c' = (c', h' (abs c'))
        where h' c@(HX PoM l2 _) = (getHyperBases c, (reverse $ sort $ concat e2, reverse $ sort $ filter (\h -> h /= c0) $  concat h2))
                                   where (e2, h2) = unzip $ map spHyOp $ filter cHyperExpr l2 
              h' c@(HX _   _  _) = (getHyperBases c, spHyOp c) -- Use the back hyperOp for now
              h' _               = ([],  ([[]], [])) -- nothing to consider in sorting

getHyperBases :: Canon -> [Canon]
getHyperBases c        = cGetBases' False False True c

sHPO :: (Canon, CanonInfo) -> (Canon, CanonInfo) -> Ordering
sHPO (_,(b1,(e1,hl1))) (_,(b2,(e2,hl2))) | hl1 > hl2 = LT 
                                         | hl1 < hl2 = GT 
                                         | otherwise = case compare hl2 hl1 of -- rev sort the hyper ops
                                                       EQ  -> case compare b1 b2 of  -- and then the bases if needed
                                                              EQ   -> case compare (length e1) (length e2) of
                                                                      EQ   -> compare e1 e2
                                                                      cmpE -> cmpE
                                                              cmpB -> cmpB
                                                       cmp -> cmp

-- give greater weight to hyper expressions raised to an exponent. ToDo: verify soundness
spHyOp :: Canon -> ([[Canon]], [Canon])
-- spHyOp c | trace ("spHyOp: Processing: (" ++ show c ++ ")") False = undefined
spHyOp c               | h == cExpOpLevel && (cHyperExpr $ head hL) = (replicate nR $ tHl, replicate nR hH)
                       | h == cMultOpLevel                          = (filter (/= []) $ sort $ concat e', sort $ concat h') -- handle product 
                       | otherwise = ([tHl], [h])
                       where (h, hL)     = (cGetHyperOp c, cGetHyperList c)
                             hH          = cGetHyperOp $ head hL
                             nR          = if l > 2 || e > 1000 then 1000 else (fromInteger $ cToI e) -- ToDo: handle edge case when grouping
                                           where l = length $ cGetHyperList $ head hL
                                                 e = head $ tail hL
                             (e', h')    = unzip $ map spHyOp $ filter cHyperExpr hL
                             tHl         | h == cExpOpLevel && length bHl > 1 = tail bHl 
                                         | otherwise                          = if length hL > 1 then tail hL else []
                                           where bHl = cGetHyperList $ head hL
                     
-- Function for special cases:                 
-- Note: When n (first param) is zero, that is known as "succession"
--   Cases when a is zero ...
cHyperOpSpecial :: Integer -> Canon -> Canon -> CycloMap -> (Canon, CycloMap)
cHyperOpSpecial 0 Pc0 b'   m = cAdd b' c1 m 
cHyperOpSpecial 1 Pc0 b'   m = (b', m)
cHyperOpSpecial 2 Pc0 _    m = (c0, m)
cHyperOpSpecial 3 Pc0 b'   m = (if b' == c0 then c1 else c0, m)
cHyperOpSpecial _ Pc0 b'   m = (if cOdd b' then c0 else c1, m)
--   Cases when b is zero ...
cHyperOpSpecial 0 _   Pc0  m = (c1, m)
cHyperOpSpecial 1 a'  Pc0  m = (a', m)
cHyperOpSpecial 2 _   Pc0  m = (c0, m)
cHyperOpSpecial _ _   Pc0  m = (c1, m)
--   Cases when b is -1 ...
cHyperOpSpecial 0 _   PcN1 m = (c0, m)
cHyperOpSpecial 1 a'  PcN1 m = cSubtract a' c1 m
cHyperOpSpecial 2 a'  PcN1 m = (cNegate a', m)
cHyperOpSpecial 3 a'  PcN1 m = (cReciprocal a', m)
cHyperOpSpecial _ _   PcN1 m = (c0, m)
--   Other Cases ...
cHyperOpSpecial h Pc2 Pc2  m | h == 0    = (smallCanons !! 3, m)
                             | otherwise = (smallCanons !! 4, m) -- recursive identity
cHyperOpSpecial _ Pc1 _    m = (c1, m)
cHyperOpSpecial _ a'  Pc1  m = (a', m)
cHyperOpSpecial _ _   _    _ = error "Can't compute this hyperoperation.  b must be >= -1.  Not a 'special' case"                

-- | Return the list of canons from a hyper expression
cGetHyperList :: Canon -> [Canon]
cGetHyperList (HX _ cL _) = cL
cGetHyperList _           = []

-- | Return the level of hyperoperation from a hyper expression.
cGetHyperOp :: Canon -> Canon
cGetHyperOp (HX h _ _) = h
cGetHyperOp _          = c0

-- | Exponentiation and root operator declarations
infixr 9 <^, >^

(<^), (>^) :: Canon -> Canon -> Canon

a <^ b = fst $ cExp a b True crCycloInitMap
r >^ n = cRoot n r

-- | Convert a Canon back to its underlying rep (if possible).
cToCR :: Canon -> CR_
cToCR (Can c v)      | v /= IrrC = gcrToCR c 
                     | otherwise        = error "cToCR: Cannot convert irrational canons to underlying data structure"
cToCR (Bare 1 _ )    = cr1
cToCR (Bare n NSim)  = fst $ crFromI n
cToCR (Bare n Simp)  = [(n,1)] -- not ideal
cToCR c              = gcrToCR $ cToGCR c -- this could be EXTREMELY expensive for hyper-expressions.

-- | Convert generalized canon rep to Canon.
gcrToC :: GCR_ -> Canon
gcrToC g | gcrBare g = Bare (gcrToI g) Simp
         | otherwise = Can g (gcrCVT g)

-- | For generalized canon rep, determine the CanonValueType.   
gcrCVT :: GCR_ -> CanonValueType         
gcrCVT POne = IntC
gcrCVT g    = g' g IntC -- start Integral, can only get "worse"
              where g' _           IrrC = IrrC -- short-circuits once irrational canon is found
                    g' POne        v    = v
                    g' ((_,ce):cs) v    = g' cs (dcv v ce) -- check the exponents for expr's value type
                    g' _           _    = error "gcrCVT : Logic error. Patterns should have been exhaustive"

                    -- checking exponents
                    dcv IrrC _            = IrrC
                    dcv _    (Can _ IrrC) = IrrC
                    dcv _    (Can _ NirC) = IrrC
                    dcv IntC (Bare  n _)  = if n < 0 then NirC else IntC
                    dcv v    (Bare  _ _)  = v
                    dcv v    c            = if cNegative c then NirC else v

-- | Define some small canons for convenience
cN1, c0, c1, c2, c3, c4, c5, c6, c7, c8, c9 :: Canon
(cN1:c0:c1:c2:c3:c4:c5:c6:c7:c8:c9:_) = map makeCanon [-1..maxHyperOpDispLevel]

impossibleHyperValue :: Canon
impossibleHyperValue = cN1 -- used internally as a sentinel

-- | Convert Canon to Integer if possible.
cToI :: Canon -> Integer
cToI (Bare i _ )       = i
cToI c@(Can g v)  | v == IntC && (cHyperExpr c || cSuperLogGT (fst $ cSuperLog c) cSuperLogCutoff)
                             = error $ tooBigError c
                  | v == IntC = gcrToI g
                  | otherwise = error $ nonIntError c
cToI h@(HX _ _ v) | v == IntC = error $ tooBigError h -- always too big.  cHyperOp is in sync with cSuperLogCutoff
                  | otherwise = error $ nonIntError h

tooBigError, nonIntError :: Canon -> String
tooBigError c = "This expression is too large to be converted to an integer: " ++ show c
nonIntError c = "Can't convert a non-integral canon to an integer: " ++ show c

-- | Convert Canon To Double.
cToD :: Canon -> Double
cToD (Bare i _) = fromIntegral i
cToD (Can c _)  = gcrToD c
cToD (HX _ _ _) = error "This hyper-expression is too large to convert to a double" 

-- | Multiply Function: Generally speaking, this will be much cheaper than addition/subtraction which requires factoring.
--   You are usually just merging lists of prime, exponent pairs and adding exponents where common primes are found.
--   This notion is the crux of the library.
--
--   Note: This can be used instead of the '*' operator if you want to maintain a CycloMap for performance
--   reasons.
cMult :: Canon -> Canon -> CycloMap -> (Canon, CycloMap) 
cMult Pc0 _   m = (c0, m)
cMult _   Pc0 m = (c0, m)
cMult Pc1 y   m = (y, m)
cMult x   Pc1 m = (x, m)
cMult x   y   m | not (cHyperExprAny x) && not (cHyperExprAny y) 
                            = (gcrToC g, m') 
                | otherwise = (multH x y, m) -- This attempts to do deeper combining and can be problematic (head $ cMultiplicative x y Mult, m) 
                where (g,  m') = gcrMult (cToGCR x) (cToGCR y) m

-- | Addition and subtraction is generally much more expensive because it requires refactorization.
--   There is logic to look for algebraic forms which can greatly reduce simplify factorization.
--   Note: This can be used instead of the +/- operators if you want to maintain a CycloMap for performance
--   reasons.
cAdd, cSubtract :: Canon -> Canon -> CycloMap -> (Canon, CycloMap)
cAdd      = cApplyAdtvOp True 
cSubtract = cApplyAdtvOp False 

-- | Internal Function to compute sum or difference based on first param.  Much heavy lifting under the hood here.
cApplyAdtvOp :: Bool -> Canon -> Canon -> CycloMap -> (Canon, CycloMap)
-- cApplyAdtvOp _ x y _ | trace ("cApplyAdtvOp: Processing: (" ++ show x ++ ") and (" ++ show y ++ ")") False = undefined
cApplyAdtvOp _     x   Pc0 m = (x, m)
cApplyAdtvOp True  Pc0 y   m = (y, m)         -- True -> (+)
cApplyAdtvOp False Pc0 y   m = (negate y, m)  -- False -> (-) 
cApplyAdtvOp b     x   y   m | not b && x == y          = (c0, m)
                             | b &&     x == (negate y) = (c0, m)
                             | not hax && not hay       = (r, m')
                             | otherwise                = (addH x (if b then y else negate y), m) 
                             where (hax, hay) = (cHyperExprAny x, cHyperExprAny y)
                                   gcd'       = cGCD x y -- non-hyper
                                   (x', y')   = (x / gcd', y / gcd')
                                   r          | tooBigToAdd x' || tooBigToAdd y' 
                                                          = simpleHX cAddOpLevel [x, if b then y else (negate y)]
                                              | otherwise = gcd' * (crToC c False)
                                   (c, m')    = crApplyAdtvOptConv b (cToCR x') (cToCR y') m -- costly bit                               

tooBigToAdd :: Canon -> Bool
tooBigToAdd c@(Can _ _) | cHyperExprAny c = True
                        | otherwise       = cSuperLogGT (fst $ cSuperLog c) cSuperLogCutoff 
tooBigToAdd (HX _ _ _)  = True
tooBigToAdd (Bare _ _)  = False

-- | Exponentiation: This does allow for negative exponentiation if the Bool flag is True.
--   Note: This can be used instead of the exponentiation operator if you want to maintain a CycloMap for performance
--   reasons.
cExp :: Canon -> Canon -> Bool -> CycloMap -> (Canon, CycloMap)
-- cExp c e _ _ | trace ("cExp: Processing: " ++ show c ++ " <^ " ++ show e ++ ".") False = undefined
cExp c e b m | cNegative e && (not b) 
               = error "Per param flag, negative exponentiation is not allowed here."
             | cIrrational c && cIrrational e 
               = error "cExp: Raising an irrational number to an irrational power is not currently supported."
             | otherwise = cExp' c e 
             where cExp' _   Pc0 = (c1, m)
                   cExp' Pc1 _   = (c1, m)
                   cExp' Pc0 _   | cNegative e = error "0^e where e < 0 gives a div by zero error"
                                 | otherwise   = (c0, m)
                   cExp' _   Pc1 = (c,  m) -- just return the value
                   cExp' _   _   | cHyperExprAny c || cHyperExprAny e  = (cApplyHy cExpOpLevel [c,e] True, m)
                                 | otherwise                           = (gcrToC g, mg)
                                 where (g, mg) = gE (cToGCR c) e m

                   gE g' e' m' | gcrNegative g' 
                                 = case cValueType e' of  -- gcr exponentiation
                                   IntC -> if cOdd e' then (gcreN1:absTail, m'')
                                                      else (absTail, m'')
                                   NirC -> if cOdd d then (gcreN1:absTail, m'')
                                                     else error "gE: Imaginary numbers not supported"
                                   IrrC     -> error "gE: Raising neg numbers to irr. powers not supported" 
                               | otherwise      
                                 = f g' m' -- equivalent to multiplying each exp by e' (with CycloMap threaded)
                               where (absTail, m'')  = gE (gcrAbs g') e' m'
                                     (_, d)          = cSplit e' -- even denom generates an imag. number
                                     f []         mf = ([], mf) 
                                     f ((p,x):gs) mf = (fp, mf')
                                                       where (prd, mx) = cMult e' x mf
                                                             (t, mn)   = f gs mx
                                                             (fp, mf') = gcrMult [(p, prd)] t mn

-- | Functions to check if a canon is negative/positive
cNegative, cPositive :: Canon -> Bool

-- cNegative c | trace ("cNegative: (l=" ++ show c ++ "))") False = undefined
cNegative (Bare n _   ) = n < 0
cNegative (Can c  _   ) = gcrNegative c
cNegative (HX PoA cL _) | lp == 0                       = True 
                        | ln == 0                       = False
                        | otherwise                     = (cCmp pH nH == LT)
                        where (posCL, negCL') = partition cPositive cL
                              negCL = map negate negCL' 
                              lp    = length posCL
                              ln    = length negCL
                              pH    = cApplyHy cAddOpLevel posCL True
                              nH    = cApplyHy cAddOpLevel negCL True
                              -- ToDo: Are there cases where combineSum could be used. Convert To Sum caused loops because it calls cNegative

cNegative (HX PoM cL _) = cNegative $ head cL
cNegative (HX _   _  _) = False -- tetration and beyond can only result in positive numbers

cPositive (Bare n   _  ) = n > 0
cPositive (Can  c   _  ) = gcrPositive c
cPositive h@(HX PoA _ _) = not $ cNegative h -- zero is not possible in a hyper-expression.
cPositive h@(HX PoM _ _) = not $ cNegative h -- same for products
cPositive (HX   _   _ _) = True -- tetration and beyond can only result in positive numbers

-- | Functions for negation, absolute value and signum
cNegate, cAbs, cSignum :: Canon -> Canon 

-- cNegate c | trace ("cNegate: Processing: v=("++show c ++ ")") False = undefined
cNegate (Bare 0 _)      = c0
cNegate (Bare 1 _)      = cN1
cNegate (Bare (-1) _)   = c1
cNegate (Bare x Simp)   = Can (gcreN1 : [(x, c1)]) IntC -- prepend a "-1", not ideal
cNegate (Bare x NSim)   = Bare (-1 * x) NSim 
cNegate (Can x v)       = gcrNegateCanonical x v

-- HyperOp case: Product of canons. 
cNegate h@(HX PoA cL _) | cNegative h = simpleHX cAddOpLevel (reverse $ map negate cL) -- only should happen internally
                        | otherwise   = simpleHX cMultOpLevel [cN1,h] 
cNegate (HX PoM cL _)   | hD == cN1           = cApplyHy cMultOpLevel (tail cL) True
                        | nhH && cNegative hD = simpleHX cMultOpLevel ((abs hD):(tail cL))    -- change the leading term which should not
                        | nhH && cPositive hD = simpleHX cMultOpLevel ((negate hD):(tail cL)) -- be hyper (if exists) in a product
                        | otherwise           = simpleHX cMultOpLevel (cN1:cL) -- prepend to existing list/product 
                        where (hD, nhH) = (head cL, not $ cHyperExpr hD)
                              
cNegate he@(HX _ _ _)   = simpleHX cMultOpLevel [cN1, he]
                          -- prepend a negative one to existing expression, making a new 2-element expr.
                          -- this applies to hyper sums which internally will always be kept positive
     
cAbs x | cNegative x = cNegate x
       | otherwise   = x

--cSignum c | trace ("cSignum: (c = " ++ show c ++ ")") False = undefined
cSignum (Bare 0 _)      = c0
cSignum g | cNegative g = cN1
          | otherwise   = c1

-- This internal function works for either gcrGCD or gcrLCM.
cLGApply :: (GCR_ -> GCR_ -> GCR_) -> Canon -> Canon -> Canon
cLGApply f x   y   | cNegative x || 
                     cNegative y = gcrToC $ f (cToGCR $ cAbs x) (cToGCR $ cAbs y)
                   | otherwise   = gcrToC $ f (cToGCR x)        (cToGCR y)

-- | This function tries to convert a hyper expression to "canonical" form.  It is rather limited
--   due to the way power towers branch for composite numbers in canonical form. Conversions can be used for non-integral division.
tryToCanonizeHyperExpr :: Canon -> Maybe Canon
tryToCanonizeHyperExpr c@(HX _ _ _) 
  | cHyperSumAny c || cMaxHyperOp c > cTetrOpLevel || cMaxTetrLevel > 10 = Nothing
  | otherwise                                                             = Just $ conv c
  where cMaxTetrLevel = mtl c0 c 
        mtl wM (HX h l@(x:xs) _) | h == cTetrOpLevel = foldl1 max [wM, mtl wM x, cApplyHy h xs True]
                                 | otherwise         = foldl1 max (wM:(map (mtl wM) l))
        mtl wM _                 = wM
        conv (HX PoM l _)        = product $ map conv l
        conv (HX PoE l _)        = foldr1 (<^) $ map conv l 
        conv (HX h l@(b:x:_)  _) | h /= c4          = error "Logic error: Only tetration allowed here"
                                 | length l /= 2    = error "Logic error: Tetration list must only have two elements"
                                 | hB < c4          = convToTwr l 
                                 | hB == c4 && simpleHyperExpr b && cMaxTetrBase <= 10 -- Note: Quite limited
                                                    = nestedTetr x
                                 | otherwise        = foldr1 (<^) $ replicate (fromInteger $ cToI $ l !! 1) (conv $ l !! 0) 
                                 where (hB, bHl, bT) = (cGetHyperOp b, cGetHyperList b, convToTwr bHl)
                                       cMaxTetrBase  = mtl c0 b
                                       convToTwr l'  = foldr1 (<^) $ replicate (fromInteger $ cToI $ l' !! 1) (conv $ l' !! 0)
                                       nestedTetr oe | oe == 2   = b <^ b
                                                     | otherwise = bT <^ nestedTetr (oe - 1)
                                       -- only relevant to tetration and above
                                       simpleHyperExpr c'@(HX h' l' _) | h' < cTetrOpLevel || not (cIntegral c') || 
                                                                         length l' /= 2 || not (any cHyperExprAny l')
                                                                                   = True
                                                                       | otherwise = False
                                       simpleHyperExpr _               = False

        conv c'                 = c' -- non-hyper expA
tryToCanonizeHyperExpr c = Just c

-- | Div function : Multiply by the reciprocal.
cDiv :: Canon -> Canon -> CycloMap -> (Canon, CycloMap)
cDiv _   Pc0 _ = error "cDiv: Division by zero error"
cDiv Pc0 _   m = (c0, m)
cDiv x   y   m 
  | not (cHyperExprAny x) && not (cHyperExprAny y) 
                                 = cMult (cReciprocal y) x m -- multiply by the reciprocal
  | y' == c1                     = (x', m) -- x is a multiple of y (One or both is a hyper expr)
  | otherwise                    = case tryHyperDiv x y m of
                                   Right r -> r
                                   Left s  -> error s
  where (x', y') = reduceProds x y

-- do not call this directly.  It assumes hyper operations 
tryHyperDiv :: Canon -> Canon -> CycloMap -> Either String (Canon, CycloMap)
tryHyperDiv x y m  
  | fmx /= hyDef && fmy /= hyDef
    = if (cCanonical fQ && cIntegral fQ && cHyperExprAny fQ) 
      --canonical yet has "hyper exponents".  Convert quotient to hyper expression.
      then Right (cConvertToHyperExpr fQ, m')
      else Right (fQ, m')
  | otherwise  
    = Left ("At this time, one can only divide hyper expressions when x is a multiple of y, non-sums or limited tetrations: x = " 
           ++ show x ++ ", y = " ++ show y)
  where fmch v             = fromMaybe hyDef (tryToCanonizeHyperExpr v)
        (hyDef, fmx, fmy)  = (impossibleHyperValue, fmch x, fmch y) 
        (fQ, m')           = cDiv fmx fmy m -- feed the canonical reps back into the function

-- Converts an integral "Canonical" canon to a hyper product. Error if the canon is not integral  Otherwise, it leaves the canon as is. 
-- ToDo: What if the result is not a hyper expr after going through the function?
cConvertToHyperExpr :: Canon -> Canon
cConvertToHyperExpr c | not (cIntegral c)               = error "Cannot convert a non-integral canon to a hyper expression"
                      | cCanonical c && cHyperExprAny c = cApplyHy cMultOpLevel ((product nHe):hE) False
                      | otherwise                       = c
                      where (hE, nHe) = partition cHyperExpr $ map hF $ cToGCR c
                            hF (p, e) = if e == c1 then pC else (cApplyHy cExpOpLevel [pC, e] True) where pC = makeCanon p

-- | Compute reciprocal (by negating exponents or equivalent).
cReciprocal :: Canon -> Canon
cReciprocal x | not (cHyperExprAny x) = fst $ cExp x cN1 True crCycloInitMap  -- raise number to (-1)st power
              | fmx /= hyDef          = cReciprocal fmx
              | otherwise             = error $ "At this time, one can only take reciprocals of hyper expressions which are " ++
                                                "non-sums and limited tetrations."
              where fmch v        = fromMaybe hyDef (tryToCanonizeHyperExpr v)
                    (hyDef, fmx)  = (impossibleHyperValue, fmch x) 

-- | Functions to check if a Canon is Integral, (Ir)Rational, "Simplified", a prime or a prime tower
cIntegral, cIrrational, cRational, cSimplified, cPrime, cIsPrimeTower :: Canon -> Bool

cIntegral   c = cValueType c == IntC
cIrrational c = cValueType c == IrrC
cRational   c = not $ cIrrational c

cSimplified (Bare _ Simp) = True
cSimplified (Bare _ NSim) = False
cSimplified (Can  c _)    = gcrSimplified c
cSimplified c@(HX h l _)  = h /= cAddOpLevel && ((cHyperProd c && all cSimplified l) || (cSimplified $ head l))

cPrime c = cSimplified c && c > c1 -- Simp includes 0, -1

cIsPrimeTower c          = cPrimeTowerLevel c > 0 -- x^x would not be, but x^x^x would be

-- | Utility functions regarding hyperoperations.  "Any" functions search the entire expression
cHyperExpr, cHyperExprAny, cHyperSum, cHyperSumAny, cHyperProd, cHyperExpo :: Canon -> Bool

cHyperExpr    = cHyperPredCheck (>= cAddOpLevel) False
cHyperExprAny = cHyperPredCheck (>= cAddOpLevel) True

cHyperSum (HX h (j:k:cs) _) = h == cAddOpLevel || 
                              (h == cMultOpLevel && j == cN1 && cGetHyperOp k == cAddOpLevel && null cs)
cHyperSum _                 = False

cHyperSumAny = cHyperPredCheck (== cAddOpLevel) True -- when looking any we can just go by hyper op

cHyperProd c@(HX PoM _ _) = not $ cHyperSum c -- Note: a negative sum is not considered a product
cHyperProd _              = False;

cHyperExpo = cHyperPredCheck (== cExpOpLevel) False -- checks if this is an exponential expression

-- | Takes a predicate related to the hyper operation.  It will search recursively if the 2nd flag is set.
cHyperPredCheck :: (Canon -> Bool) -> Bool -> Canon -> Bool 
cHyperPredCheck f b c | f (cGetHyperOp c) = True
                      | not b             = False -- don't do the any check
                      | otherwise         = cHP' c
                      where cHP' (HX _ l _) = any (cHyperPredCheck f b) l
                            cHP' (Can g _)  = any (cHyperPredCheck f b) $ map snd g
                            cHP' _          = False

-- | cNumerator and cDenominator are for processing "rational" canon reps.
cNumerator, cDenominator :: Canon -> Canon

cNumerator (Can c _ ) = gcrToC $ filter (\x -> cPositive $ snd x) c -- filter positive exponents
cNumerator b          = b 

cDenominator (Can c _ ) = gcrToC $ map (\(p,e) -> (p, cN1*e)) $ filter (\(_,e) -> cNegative e) c -- negate neg expnts
cDenominator _          = c1  -- ToDo: For now, hyper expressions are always integral 

-- ToDo : Tweak cQuasiCanonize to make this function obsolete.  The 2nd param isn't part of the QC function.
-- cNestExpTail can be used whether or not the base is a hyper expression.  It unravels tetration and beyond.
-- For example: 7 <<<^>>> 8 = 7 <^ (7 <^> (-1 + 7 <<^>> (-1 + 7 <<<^>>> 7)).  The expr after <^ would be the exp. tail
cNestExpTail :: Canon -> Bool -> Canon
cNestExpTail c'@(HX h (b:xs) IntC) bF
  | h == cAddOpLevel= c1
  | h < cExpOpLevel = error errorMsg
  | otherwise       = if bF then baseTail b * eH else eH -- If the flag is set, process the base as well.
  where expTail      = cApplyHy h xs True
        eH           = expRec h expTail
        expRec h' e' | h' == cExpOpLevel = e' -- otherwise, recursively demote down
                     | otherwise         = expRec (h' - c1) newE
                                           -- e.g. x<^>y<^>z = x^(x<^>((y<^>z)-1))
                     where newE          = cApplyHy h' [b, e' - c1] True  
        baseTail (HX PoA _ _)   = c1           
        baseTail c@(HX PoM _ _) = error $ nonPrimePowerError c  -- Limited but cQuasiCanonize kind of supplants this fcn
        baseTail c@(HX _   _ _) = cNestExpTail c bF
        baseTail c@(Can g _)    | length g > 1 = error $ nonPrimePowerError c
                                | otherwise    = snd $ head g -- the exponent
        baseTail (Bare _ Simp)  = c1
        baseTail c              = error $ nonPrimePowerError c
        errorMsg = "nestedExpTail: requires a hyper expression at level >= exponentiation: " ++ show c'
cNestExpTail _ _     = c1

-- | Break code into a canonized 
cCleanup :: Canon -> Canon
cCleanup = cHyperize . cQuasiCanonize

-- | Split the hyperoperation into a cleaned-up numerator and denominator pair (if denom is 1).  This still represents an integral value.  e.g. 3 <^> 7 / 3 <^> 4
cCleanupAsNumDenPair :: Canon -> (Canon,Canon)
cCleanupAsNumDenPair c = (n,d) 
  where (n, d)   = (cHyperize $ pr nL, cHyperize $ pr dL) 
        qc       = cQuasiCanonize c
        pr cL    = simpleHX cMultOpLevel $ map expDemote $ filter (\(_, e) -> e /= c0) cL
        (nL, dL) = unzip $ map (\(p,(eP,eN)) -> ((p, eP), (p, eN)) ) $ map (\(p,e) -> (p, spl e)) $ map (\c' -> expPromote c') $ cGetFactors qc
        spl c'   = (simpleHX cAddOpLevel pos, simpleHX cAddOpLevel (map negate neg)) 
                   where (pos, neg) = partition cPositive $ cGetAddends c' -- positive and negative entries in exponent sum expression

-- | Hyperize will take a Canon in quasi-canonized form and try to clean it up in a tidier expression
-- Example: 7 ^ ( 1 + 2 * (49 <^> 7) = 7 * 49 <^> 8.  ToDo: Enhancement: Partial hyperizing?
cHyperize :: Canon -> Canon
cHyperize c | not (cQuasiCanonized c) || (h /= cExpOpLevel && h /= cMultOpLevel) || null iM 
                        = c
            | any cNegative $ concat $ map (\(_,e) -> cGetAddends e) $ map expPromote $ cGetFactors c -- 
                        = c -- For example, we can't cleanup 3 <^> 5 / 3 <^> 4 = 3 ^ (3<^>4 - 3<^>3) into a simple expression
            | not (null $ cGetBases' False True False $ simpleHX cMultOpLevel iM) -- in-scope bases are non-unique so not valid
                        = c 
            | not (foldl1 (&&) $ map snd process)                             -- not all "tail-convertible")
                        = c 
            | not (foldl1 (&&) $ map (\(_,l) -> allTheSame $ map snd l) grp)  -- not all multipliers are the same
                        = c 
            | null grp' || not (foldl1 (&&) $ map snd grp')                   -- not all elements of each base accounted for
                        = c 
            | otherwise = iSp * oSp 
            where h        = cGetHyperOp c
                  (iM, oM) = partition (\m -> cGetHyperOp m == cExpOpLevel) $ cGetFactors c

                  process = map (\l -> hypMap (l !! 0, l !! 1)) $ map cGetHyperList iM
                  oSp     = product (oM ++ (map (snd . snd . fst) process)) -- everything that could not be rolled up
                  grp     = grpExpr $ concat $ map (\((p,(eMap,_)),_) -> map (\((_,t),m)-> (t, (p, m))) eMap) process
                  grp'    = map (\(e,l) -> ((e, snd $ head l), cBaseRadical e == product (map fst l))) grp
                  iSp     = product $ map (\((e,m),_) -> cApplyHy cExpOpLevel [e, m] True) grp' -- in scope product

                  allTheSame l@(x:_:_) = and $ map (== x) (tail l)
                  allTheSame _         = True

                  grpExpr l@(_:_:_) = gE' l []
                  grpExpr ((e,p):_) = [(e, [p])]
                  grpExpr _         = error $ "Blank list passed to grpExpr when processing c = " ++ show c

                  gE' l@((xf,_):_) wL = gE' nM ((xf, map snd m):wL) -- all the add'l base info for that expression
                                        where (m,nM) = partition (\e -> xf == fst e) l
                  gE' _            wL = wL

-- Called by hyperize at this point, the constants should have been removed
hypMap :: (Canon, Canon) -> ((Canon, ([((Canon, Canon), Canon)], Canon)), Bool) -- ToDo: Better to change this to a Maybe
hypMap (p, e) = ((p, (mV', osProd)), not $ any (\((_,t),_) -> t == impossibleHyperValue) mV')
  where (iS, oS) = partition candPred $ cGetAddends e -- only process
        osProd   = computeExpr cMultOpLevel (map (\x -> p <^ x) oS)
        mV'      = mV p iS

-- mV is short for mapped values
mV :: Canon -> [Canon] -> [((Canon, Canon), Canon)]
mV p iS | null iS   = []
        | otherwise = map (hypCheck p) $ cGetAddends $ grpAndSrtList p iS 

hypCheck :: Canon -> Canon -> ((Canon, Canon), Canon)
hypCheck p c = ((c, liftedTail), p') -- e.g. p == 13 for (3 <<^>> 4) <^ 13
               where (fs, base)  = (cGetFactors c, head $ cGetHyperList $ head $ fs)
                     liftedTail  | b' /= c1  = impossibleHyperValue -- p must be a "clean" multiple of b
                                 | otherwise = tryLiftTail $ head fs
                     (_, p', b') = simpleReduce (product $ tail fs) (qcBase p base) False -- 

-- group and sort list of canons 
grpAndSrtList :: Canon -> [Canon] -> Canon
-- grpAndSrtList p iS | trace ("grpAndSrtList: (p = " ++ show p ++ ", iS = " ++ show iS ++ ")") False = undefined
grpAndSrtList p iS = simpleHX cAddOpLevel $ map s $ cGetAddends $ factorSumIter True $ simpleHX cAddOpLevel $ map m' iS
                     where m' a     = applyFcnForHy a cMultOpLevel cFlattenAndGroup
                           s  a     = applyFcnForHy a cMultOpLevel (srt p)

-- sort the portions of the product so that the first item's base "derivative" will equal the product of the tail
srt :: Canon -> Canon -> [Canon]
srt p a' = ((reverse $ sortOn (nestLevel p) cs) ++ ncs)
           where (cs, ncs) = partition (\e -> candPred e && elem p (cGetBases e)) $ cGetFactors a'

candPred :: Canon -> Bool
candPred c'@(HX PoM _ _) = any candPred $ cGetHyperList c'
candPred c'              = powSq c' || cGetHyperOp c' == cTetrOpLevel
                           where powSq (HX PoE (b:e:xs) _) = null xs && b == e -- some item raised to itself
                                 powSq _                   = False

-- 7 ^ {7 <^> {7 <<^>> (2^2) - 1}} would be lifted to Just 7 <<^>> 5.  Useful when hyperizing
tryLiftTail :: Canon -> Canon
-- tryLiftTail c | trace ("tryLiftTail: (c = " ++ show c ++ ")") False = undefined
tryLiftTail c | cGetHyperOp c < cExpOpLevel || length l < 2 || cGetHyperOp cLift == cExpOpLevel 
                          = impossibleHyperValue
              | otherwise = cLift
              where (l, b, cLift) = (cGetHyperList c, head l, cApplyHy cExpOpLevel [b, c] True)

qcBase :: Canon -> Canon -> Canon
-- qcBase p c | trace ("qcBase: (p = " ++ show p ++ ", c = " ++ show c ++ ")") False = undefined
qcBase p c@(Bare n _) = if (n == cToI p) then c1 else error (errMsgQCB p c []) -- ToDo: Handle unfactored numbers
qcBase p c@(Can g _)  | cHyperExpr p || length pe == 0 = error (errMsgQCB p c [])
                      | otherwise                      = snd $ head pe
                      where pe = filter (\(p',_) -> p' == pI) g -- ToDo: Unfactored edge cases 
                            pI = cToI p
qcBase p c            | cGetHyperOp p == cAddOpLevel && p == c 
                                      = c1 
                      | length qce == 1 = snd $ head qce -- 3 <^ (3 <^> 4) -> 3 <^> 4
                      | otherwise       = error $ errMsgQCB p c qce
                      where qce = filter (\(b,_) -> p == b) $ map expPromote $ cGetFactors $ cQuasiCanonize c 

errMsgQCB :: Canon -> Canon -> [(Canon, Canon)] -> String
errMsgQCB p c qce = "Logic error in qcBase: Canon: " ++ show c ++ " did not contain p = " ++ 
                    show p ++ ". Length = " ++ show (length qce) 

-- Checks how embedded a prime (or sum) is in a hyper expression
nestLevel :: Canon -> Canon -> Int
nestLevel p c | cBare p || cGetHyperOp p == cAddOpLevel
                          = nL c 0
              | otherwise = error $ "nestLevel: Only for a prime or sum: " ++ show p ++ " when checking: " ++ show c
              where nL c'@(HX PoA l      _) lvl = if p == c' then (lvl + 1) else (getMax l lvl)
                    nL (HX PoM l      _)    lvl = getMax l lvl
                    nL (HX _   (b:_) _)     lvl = nL b (lvl+1)
                    nL (Bare n _)           lvl = if cHyperExpr p || n /= pI then badLevel else lvl
                    nL (Can g _)            lvl | cHyperExpr p || null matchP = badLevel
                                                | otherwise                   = if x == 1 then lvl else (lvl + 1)
                                                where matchP = filter (\(p',_) -> p' == pI) g
                                                      x      = snd $ head matchP
                    nL _                    _   = error "Should not reach this point in the code"
                    pI                          = cToI p
                    badLevel                    = -1 -- no match
                    getMax l lvl                = if null l then 0 else (foldl1 max $ map (\m -> nL m lvl) l)

-- simple utility function to create hyper expression if list specified
simpleHX :: Canon -> [Canon] -> Canon
simpleHX h c | ln == 1   = head c 
             | ln >  1   = HX h c IntC
             | otherwise = if h == cAddOpLevel then c0 else c1 -- nullary values
             where ln = length c

-- | If the Canon is a product, return the factors.  Otherwise, return the Canon itself.
cGetAddends :: Canon -> [Canon]
cGetAddends c = if cGetHyperOp c == cAddOpLevel then cGetHyperList c else [c]

-- | If the Canon is a sum, return the addends. Otherwise, return the Canon itself.
cGetFactors :: Canon -> [Canon]
cGetFactors c = if cGetHyperOp c == cMultOpLevel then cGetHyperList c else [c]

-- | Take a canon and a list of indexes and delve into the canon.  This operates on the internal hyper lists
cDelve :: Canon -> [Int] -> Canon
cDelve c xL | x < length hL = if null xs then e else cDelve e xs
            | otherwise     = error $ "Can not find index " ++ show x ++ " in canon: " ++ show c 
            where (hL, e) = (cGetHyperList c, hL !! x)
                  (x:xs)  = xL

applyFcnForHy :: Canon -> Canon -> (Canon -> [Canon]) -> Canon
applyFcnForHy c h f           = if cGetHyperOp c == h then simpleHX h (f c) else c

-- FactorSumIter: Performs steps like: a*b + b + c =>  b * (a+1)+c.
factorSumIter :: Bool -> Canon -> Canon
factorSumIter hF (HX PoA hL _) = fs (head hL) (tail hL) []
                                 where fs a (x:xs) wL | gcd' == c1 || (hF && not (cHyperExpr gcd')) = fs a  xs (wL ++ [x])
                                                      | otherwise                                   = fs nv xs wL
                                                      where (nv, gcd') = simpleFactorPair a x hF
                                       fs a _      wL = computeExpr cAddOpLevel (wL ++ [a])
factorSumIter _  c             = c

-- | This checks if the (hyper)expression is in quasi-canonical form 
cQuasiCanonized :: Canon -> Bool
cQuasiCanonized (HX PoA _ _)        = True
cQuasiCanonized c@(HX PoM l _)      = all cQuasiCanonized l && null (cGetBases' True True False c)
cQuasiCanonized (HX PoE (b:_:xs) _) = (cBare b || cGetHyperOp b == cAddOpLevel) && null xs -- only b ^ e not b ^ e ^ x
cQuasiCanonized (HX h _ _)          = h > maxHyperOpDelveLevel -- anything else like tetration has not been simplified
cQuasiCanonized _                   = True

-- | This is akin to canonical form except you may have sums in the bases. It converts expression up to a hyperoperational cutoff
cQuasiCanonize :: Canon -> Canon
-- cQuasiCanonize c | trace ("cQuasiCanonize: (c = " ++ show c ++ ")") False = undefined
cQuasiCanonize c | cGetHyperOp c > maxHyperOpDelveLevel || (pF && null sM) -- nothing below the the hyper limit
                             = c -- don't attempt to canonize
                 | pF && not (null bM) -- there are entries beyond the hyper limit.
                             = computeExpr cMultOpLevel ((cL sMp) ++ bM)
                 | otherwise = computeExpr cMultOpLevel (cL c)     -- all below the hyper limit
  where (bM, sM)              = partition (\m -> cGetHyperOp m > maxHyperOpDelveLevel) $ cGetHyperList c -- partition product
        (sMp, pF)             = (computeExpr cMultOpLevel sM, cGetHyperOp c == cMultOpLevel)
        -- "Endless" looping! cL c' = map (\l -> promote (fst $ head l, fst $ cConvertToSum $ sum $ map snd l)) $
        cL c'                 = map (\l -> promote (fst $ head l, sum $ map snd l)) $   -- ToDo: Make this more robust?
                                groupBy (\x y -> fst x == fst y) $ sortOn fst $ can' c'
        promote (b',e')       | e' == c1         = b'
                              | cHyperExprAny e' = (computeExpr cExpOpLevel [b',e'])
                              | otherwise        = b' <^ e' 

        can' c'@(HX h l'@(b:xs) IntC) 
          | h == cAddOpLevel  = [(c', c1)] -- you need the base
          | h == cMultOpLevel = concat $ map can' l'
          | otherwise         = map (\(b', e') -> (b', mul e')) $ can' b 
          where expTail      = cApplyHy h xs True
                eH           = expRec h expTail
                mul :: Canon -> Canon
                mul e'       | e' == c1  = eH
                             | eH == c1  = e' 
                             | otherwise = applyFcnForHy (simpleHX cMultOpLevel [e', eH]) cMultOpLevel cFlattenAndGroup
                expRec h' e' | h' == cExpOpLevel = e' -- otherwise, recursively demote down
                             | otherwise         = expRec (h' - c1) newE -- e.g. x<^>y<^>z = x^(x<^>((y<^>z)-1))
                             where newE          = cApplyHy h' [b, e' - c1] True
        can' (Can g _)        = map (\(b', e') -> (makeCanon b', e')) g -- essentially the same thing
        can' c'               = [(c', c1)] 

nonPrimePowerError :: Canon -> String -- collect all of the errors together
nonPrimePowerError c = "cNestExpTail: Can't compute if base is a product or unfactored: " ++ show c

cBaseRadical :: Canon -> Canon         -- need a cutoff for what to process
cBaseRadical = cBaseRadical' False False False

cBaseRadical' :: Bool -> Bool -> Bool -> Canon -> Canon
cBaseRadical' f d h c = product $ cGetBases' f d h c
-- For cToGCR combine the bases or partial bases that match on a gcm (say with the other term) in cTryToCanonize

cHyOpLvlOutOfRange :: Canon -> Bool
cHyOpLvlOutOfRange h | h < cMultOpLevel || h > maxHyperOpDelveLevel = True
                     | otherwise                                    = False

data FuncType = Mult | Gcd | Lcm deriving (Show, Eq)

-- Several choices from multiplicative functions. "Let results escape" to cHyperOp only at end 
cMultiplicative :: Canon -> Canon -> FuncType -> [Canon]
-- cMultiplicative v w t | trace ("cMultiplicative: Processing: v=("++show v++", w= "++show w++", t = "++show t++")") False = undefined
cMultiplicative v w t 
  | not (cHyperExpr v) && not (cHyperExpr w) 
                         = case t of 
                           Gcd -> [gvw, div v gvw, div w gvw]
                           Lcm -> [cLCM v w]
                           _   -> [v * w] 
  | t == Mult            = [v * w] -- No longer does anything distinct from multiplication
  | t == Lcm && relPrime = if v' == c1 then [abs w]
                                       else (if w' == c1 then [abs v]
                                                         else [hyperize' $ cCleanup $ head $ cMultiplicative' vA wA t])
  | t == Lcm             = [hyperize' $ cCleanup $ head $ cMultiplicative' (cQuasiCanonize vA) (cQuasiCanonize wA) t]
  | t == Gcd && relPrime = [gHvw,  f v' v, f w' w] 
  | otherwise            = [gHvw', f v2 v, f w2 w]
  where gvw             = cGCD v w -- non-hyper
        (vA, wA)        = (abs v, abs w)
        hyperize' c     = simpleHX cMultOpLevel (concat $ map (\e -> cGetFactors $ if cQuasiCanonized e then cHyperize e else e) $ cGetFactors c)
        (gHvw:v':w':_)  = map (hyperize' . cCleanup) $ cMultiplicative' vA  wA  Gcd -- first try
        (gHvw2:v2:w2:_) = map (hyperize' . cCleanup) $ cMultiplicative' (cQuasiCanonize v') (cQuasiCanonize w') Gcd 
        gHvw'           = gHvw * gHvw2
        relPrime        = null $ intersect (cGetBases v') (cGetBases w')              
        f a' a          = if signum a == cN1 then negate a' else a'  -- efficient way to adjust by sign

-- do not call directly. assumes unsigned "hyper" input
cMultiplicative' :: Canon -> Canon -> FuncType -> [Canon]
-- cMultiplicative' v w t | trace ("cMultiplicative': Processing: v=("++show v++", w= "++show w++", t = "++show t++")") False = undefined
cMultiplicative' v w t = [apply r, apply xN, apply yN]
  where  -- Internally we just manipulate lists rather than continually passing interim results to cApplyHy
    apply l = product $ (ccProd:hEs) 
              where ccProd    = product $ map conv cc
                                where conv c | cHyperExpr c = (head hL) <^ (head $ tail hL) -- always of this form
                                             | otherwise    = c
                                             where hL = cGetHyperList c
                    (cc, hEs) = partition canConv l
                    canConv c = not (cHyperExprAny c) || 
                                (cGetHyperOp c == cExpOpLevel && length hL == 2 && not (any cHyperExprAny hL))
                                where hL = cGetHyperList c
    (xN, yN, r) = p' (allFactors v) (allFactors w) -- this mode creates a hyper list

    p' x y  -- We ignore the first two return values when not running for Gcd.  ToDo: simplify the code below
     | eitherNull x1 y1 = if t == Gcd then (x1, y1, r1) else ([], [], r1 ++ x1 ++ y1)
     | eitherNull x2 y2 = if t == Gcd then (x2, y2, r2) else ([], [], r2 ++ x2 ++ y2)
     | eitherNull x3 y3 = if t == Gcd then (x3, y3, r3) else ([], [], r3 ++ x3 ++ y3)
     | otherwise   = if t == Gcd then (x4, y4, r4) else ([], [], r4 ++ x4 ++ y4)
     where (x1, y1, r1) = rW x  y  [] False False 
           (x2, y2, r2) = rW x1 y1 r1 True  False 
           (x3, y3, r3) = rW x2 y2 r2 False True 
           (x4, y4, r4) = rW x3 y3 r3 True  True

           -- rW x' y' g' bx by | trace ("rW: (x = "++show x'++",y="++show y'++", g' = "++show g'++",bx="++show bx++",by="++show by++")") False = undefined
           rW x' y' g' bx by = promote (fmt x') (fmt y') [] [] g' bx by t
                               where fmt m = allFactors (simpleHX cMultOpLevel m) -- ToDo: change wrap kludge
           eitherNull j k    = null j || null k

           -- promote a' b' aW' bW' g' aF bF _ | trace ("promote: (a' = "++show a'++", b' = "++show b'++", aW' = "++show aW'++", bW' = "++show bW'++", g' = "++show g'++", aF = "++show aF++", bF = "++show bF++")") False = undefined
           promote a' b' aW' bW' g' aF bF t' 
             = if (aF && bF) then r' (sortOn getBase' a') (sortOn getBase' b') aW' bW' g' [] [] -- Loopage worries seem unfounded. 
                             else r' a' b' aW' bW' g' [] []                                     -- Doesn't seem necessary for both 
               where 
                     -- r' aC bC aW bW g _ bN | trace ("r': (aC = "++show aC++", bC = "++show bC++", aW = "++show aW++", bW = "++show bW++", g = "++show g++", bN = "++show bN++")") False = undefined
                     r' (a:as) (b:bs) aW bW g aN bN  
                       | aB == bB  && (aT /= impossibleHyperValue && bT /= impossibleHyperValue)
                                   = r' as     bs nAw nBw (g ++ [aB <^ m]) aN bN
                       | otherwise = r' (a:as) bs aW  bW  g                aN (bN ++ [b]) 
                       where (aB, bB)   = (f' a aF, f' b bF)
                             (aT, bT)   = (e' a aF, e' b bF)
                             m          | t' == Gcd && aF && bF = if a < b then aT else bT -- leverage the comparision instead of using tail
                                        | t' == Gcd             = min aT bT 
                                        | t' == Lcm && aF && bF = if a > b then aT else bT -- leverage, pt. 2
                                        | t' == Lcm             = max aT bT 
                                        | otherwise             = aT + bT  -- multiply, so add the exponents
                             nGcdE w'   | w' /= m && cMaxHyperOp w' > cTetrOpLevel && cMaxHyperOp m > cTetrOpLevel
                                                    = simpleHX cAddOpLevel [w', negate m] -- to avoid infinite loops
                                        | otherwise = w' - m 
                             (nAw, nBw) | t' == Gcd = (aW ++ [aB <^ nGcdE aT], bW ++ [bB <^ nGcdE bT])
                                        | otherwise = (aW,                    bW)
                     r' (a:as) _ aW bW g aN bN 
                       = r' as bN newAw bW g newAn [] -- add to aW, use tail for #1 + feed in bN list for #2
                         where (newAw, newAn) | t' == Gcd = (aW ++ [a], aN)
                                              | otherwise = (aW,        aN ++ [a]) -- not found
                     r' _      b aW bW g aN bN -- at the end
                       | t' == Gcd = (aW, bW ++ b ++ bN, g) -- add unprocessed members of b lists
                       | otherwise = (aN, b ++ bN,       g) -- feed the lists back in

                     f' j fB = if fB then getBase' j     else j
                     e' j fB = if fB then (if cGetHyperOp j > maxHyperOpDelveLevel
                                           then impossibleHyperValue 
                                           else cNestExpTail j False) -- ToDo: replace with cQuasiCanonize
                                     else c1 -- if whole expression, exp is just 1

                     getBase' s@(HX PoA _ _) = s
                     getBase' c@(HX PoM _ _) = error $ getBaseHypError c
                     getBase' (HX _ (b:_) _) = b
                     getBase' (Bare b _)     = makeCanon b
                     getBase' c@(Can g _)    | length g == 1 = gcrToC g --makeCanon $ fst $ head g 
                                             | otherwise     = error $ getBaseCanError c 
                     getBase' _              = error "getBase' unknown canon type encountered."

                     getBaseCanError c       = "getBase': canonical param with > 1 base not allowed: " ++ show c
                     getBaseHypError c       = "getBase': hyper prod param not allowed: " ++ show c

-- Note: This does not delve into hyperoperations and try separate or group
--       It does split canonical elements unlike cGetFactors
allFactors :: Canon -> [Canon]
-- allFactors c | trace ("allFactors: (c = " ++ show c ++ ")") False = undefined 
allFactors (HX PoM l _)   = concat $ map allFactors l
allFactors c@(HX _   _ _) = [c]
allFactors c              | cIntegral c = filter (/= c1) $ map expLift $ cToGCR c
                          | otherwise   = error "allFactors only takes integral canons"
                          -- Note: We call the constructor directly so there are no demotions applied by cApplyHy
                          where expLift (b', e') = if e' == c1 then bC else (simpleHX cExpOpLevel [bC,e']) -- avoids "2" bug
                                                       where bC = makeCanon b'

-- | Compute the rth-root of a Canon.
cRoot :: Canon -> Canon -> Canon  
cRoot c r 
  | not (cPositive r)      = error "r-th roots are not allowed when r <= 0 or not integral" 
  | r == c1 || c == c0     = c 
  | cNegative c && cEven r = error "cRoot does not support imaginary numbers (even roots of negative numbers)." 
  | all (\(_,e) -> cMod e r == 0) cL'
                           = if cNegative c then negate root else root
  | cMaxHyperOp c > maxHyperOpDelveLevel 
                           = error $ "Root could not be found but that may be due to the level of hyper operation being beyond the cutoff: " ++ show c
  | otherwise              = error $ "The root requested was not a multiple of all the exponents in the expansion of " ++ show c
  where cL'  = map expPromote $ allFactors $ cQuasiCanonize $ abs c
        root = simpleHX cMultOpLevel $ map (\(p,e) -> expDemote (p, e / r)) cL' 

-- | This is used for tetration, etc.  It defaults to zero for non-integral reps.
cPrimeTowerLevel :: Canon -> Canon                  
cPrimeTowerLevel (Bare _ Simp)        = c1
cPrimeTowerLevel (Can g IntC)         | gcrPrimePower g   = cPrimeTowerLevelI (snd $ head g) (fst $ head g) (1 :: Integer)
                                      | otherwise         = c0
cPrimeTowerLevel c@(HX h l@(b:xl) _)  | h < cExpOpLevel || any cHyperExprAny l || not (cPrime b) 
                                                                  = c0 -- ToDo: handle nested hyper expression cases properly
                                      | h == cExpOpLevel          = if cQuasiCanonized c && cMaxHyperOp c > cExpOpLevel
                                                                    then (cPrimeTowerLevel $ cHyperize c)
                                                                    else (makeCanon $ toInteger $ length l)
                                      | h == cTetrOpLevel         = simpleHX h xl
                                      | h <= maxHyperOpDelveLevel = cDelve (cQuasiCanonize c) [1,1] -- gets the tetration expression
                                      | otherwise                 = c -- it's so massive just return the number itself.  Not that critical.
cPrimeTowerLevel _                  = c0

-- | Internal workhorse function to compute the height of a prime tower (e.g. 5^(5^7) => 3)
cPrimeTowerLevelI :: Canon -> Integer -> Integer -> Canon
cPrimeTowerLevelI (Bare b _)   n l | b == n    = makeCanon $ l + 1 
                                   | otherwise = c0
cPrimeTowerLevelI (Can g IntC) n l | gcrPrimePower g == False = c0 
                                   | n /= (fst $ head g)      = c0
                                   | otherwise                = cPrimeTowerLevelI (snd $ head g) n (l+1)
cPrimeTowerLevelI _            _ _ = 0 -- This is only for internal display.  Not needed for hyper-expressions.


-- | Function to convert Canon to generalized canon rep
cToGCR :: Canon -> GCR_
--cToGCR c | trace ("cToGCR: (c = " ++ show c ++ ")") False = undefined -- Tracing here may cause stack overflow!
cToGCR c = case gAtt of 
           Just g -> g
           _      -> error $ noConvError
           where gAtt        = cToGCR' c 
                 noConvError = "Could not to convert unwieldy hyper expression to canonical rep: " ++ show c ++ "."

cToGCR' :: Canon -> Maybe GCR_
cToGCR' (Can x _)  = Just x
                     -- don't attempt to factor a large composite at this time.  To Do: may not handle trial division.
cToGCR' (Bare x s) | s == Simp || gcrBigComposite (x, c1)
                               = Just $ if x == 1 then gcr1 else [(x, c1)]
                   | otherwise = cToGCR' (makeCanon x) -- ToDo:Thread in CycloMap?
cToGCR' c          | any (\c' -> cHyperExpr c' && (cHyOpLvlOutOfRange $ cGetHyperOp c')) $ cGetFactors c
                               = Nothing 
                   | any (not . cSimplified) f 
                               = Nothing  -- if there are any unsimplified bases, fail
                   | otherwise = Just g -- product of base / exponent pairs
                   where f               = cGetFactors $ cQuasiCanonize c
                         g               = sortOn fst $ concat $ map conv f
                         conv (Bare n _) = [(n, c1)]
                         conv (Can g' _) = g'
                         conv (HX _ l _) = [(cToI (l !! 0), l !! 1)] -- already in canonized mode so this is safe

-- Warning: Don't call this for 0 or +/- 1.  The value type will not change by negating the value     
gcrNegateCanonical :: GCR_ -> CanonValueType -> Canon    
gcrNegateCanonical g  v | gcrNegative g = case gcrPrime (tail g) of
                                          True  -> Bare (fst $ head $ tail g) Simp
                                          False -> Can (tail g) v             
                        | otherwise     = Can (gcreN1 : g) v -- just prepend

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

gcrMult :: GCR_ -> GCR_ -> CycloMap -> (GCR_, CycloMap)
gcrMult x    POne m = (x, m) 
gcrMult POne y    m = (y, m)  
gcrMult _    Pg0  m = (gcr0, m) 
gcrMult Pg0  _    m = (gcr0, m)

gcrMult x@(xh@(xp,xe):xs) y@(yh@(yp,ye):ys) m 
                    = case compare xp yp of
                      LT -> (xh:g, m') 
                            where (g, m') = gcrMult xs y m
                      EQ -> if gcrNegative x || expSum == c0 
                            then gcrMult xs ys m -- cancel double negs/exponents adding to zero
                            else ((xp, expSum):gf, mf) 
                            where (expSum, m') = cAdd xe ye m 
                                  (gf, mf)     = gcrMult xs ys m'
                      GT -> (yh:g, m') 
                            where (g, m') = gcrMult x ys m
gcrMult x    y    _ = error e 
                      where e = "Non-exhaustive pattern error in gcrMult.  Params: " ++ show x ++ "*" ++ show y

gcr1, gcr0 :: GCR_
gcr1 = []
gcr0 = [(0, c1)]   

gcreN1 :: GCRE_
gcreN1 = (-1, c1)

gcrToI :: GCR_ -> Integer  -- ToDo: Add upperbound into conversaion step
gcrToI g = product $ map f g
           where f (p, e)  | ce > 0    = p ^ ce 
                           | otherwise = error negExpErr
                           where ce = cToI e 
                 negExpErr = "gcrToI: Negative exponent found trying to convert " ++ show g

gcrToD :: GCR_ -> Double
gcrToD g = product $ map (\(p,e) -> (fromIntegral p) ** cToD e) g

gcrCmp :: GCR_ -> GCR_ -> Ordering
gcrCmp POne y            = gcrCmpTo1 y True
gcrCmp x    POne         = gcrCmpTo1 x False
gcrCmp x y | x == y      = EQ            
           | xN && yN    = compare (gcrToC $ tail y) (gcrToC $ tail x)
           | xN          = LT
           | yN          = GT         
           | gcrIsZero x = LT
           | gcrIsZero y = GT
           | otherwise   = case cSuperLogCmp (superLogCan x) (superLogCan y) of
                           -- If equal: we have to break out the big guns and try to convert it to an integer
                           EQ  -> compare (gcrToI x) (gcrToI y) 
                           cmp -> cmp
           where (xN, yN)      = (gcrNegative x, gcrNegative y)
                 gcrIsZero Pg0 = True;
                 gcrIsZero _   = False

gcrCmpTo1 :: GCR_ -> Bool -> Ordering
gcrCmpTo1 PNeg b = if b then GT else LT
gcrCmpTo1 Pg0  b = if b then GT else LT
gcrCmpTo1 _    b = if b then LT else GT 

-- | These internal functions should not be called directly.  The definition of GCD and LCM 
--   are extended to handle non-Integers.
gcrGCD, gcrLCM :: GCR_ -> GCR_ -> GCR_  
gcrGCD Pg0 y   = y
gcrGCD x   Pg0 = x
gcrGCD x   y   | crFactCutoff > 0 &&  -- partial factorization workarounds can be disabled if <= 0
                 ((gcrIncompFact x && gcrUnsmooth y) || -- either has an imcomplete factorization and the other
                  (gcrIncompFact y && gcrUnsmooth x)) = f spx spy -- in case of unfactored bits
               | otherwise                            = f x y
               where f Pg1 _   = gcr1
                     f _   Pg1 = gcr1
                     f x'  y'  = case compare xp yp of
                                 LT -> f xs y'
                                 EQ -> (xp, min xe ye) : f xs ys
                                 GT -> f x' ys
                                 where ((xp,xe):xs) = x'
                                       ((yp,ye):ys) = y'
                     (spx, spy)= spFactor x y

gcrLCM Pg0 _   = gcr0
gcrLCM _   Pg0 = gcr0
gcrLCM x   y   | gcrNegative x || gcrNegative y       = f (gcrAbs x) (gcrAbs y)
               | crFactCutoff > 0 && -- partial factorization workarounds can be disabled if <= 0
                 ((gcrIncompFact x && gcrUnsmooth y) || -- either has an imcomplete factorization and the other
                  (gcrIncompFact y && gcrUnsmooth x)) = f spx spy -- in case of unfactored bits
               | otherwise                    = f x   y
               where f Pg1 y'  = y'
                     f x'  Pg1 = x'
                     f x'  y'  = case compare xp yp of
                                 LT -> xh : f xs y'
                                 EQ -> (xp, max xe ye) : f xs ys
                                 GT -> yh : f x' ys
                                 where (xh@(xp,xe):xs) = x'
                                       (yh@(yp,ye):ys) = y'
                     (spx, spy)= spFactor x y

-- special factor: This covers the case where we have unfactored large components but on comparison with another
-- cr we can see that the component can be reduced.  We partition the cr into
-- three pieces: small factor cutoff, prime, composite (implying it's > factor. cutoff)
-- ToDo: This code as well as for gcd and lcm closely matches that in Internals.hs.  Remove the duplicate code
-- Note: This and related functions are only called when crFactCutoff > 0 (indicating a partial factorization is possible)
spFactor :: GCR_ -> GCR_ -> (GCR_, GCR_)
spFactor x y = (sx ++ (grp $ sortOn fst $ px ++ spF cx (py ++ cy)),
                sy ++ (grp $ sortOn fst $ py ++ spF cy (px ++ cx)) )
               where spl n           = (s, p, c)
                                       where (s, r) = partition gcrSmooth n
                                             (p, c) = partition (\ce -> not $ gcrBigComposite ce) r
                     (sx, px, cx)    = spl x
                     (sy, py, cy)    = spl y
                     grp (n:ns)      = g' n ns
                     grp _           = error "The list to be grouped in spFactor must have at least one element"
                     g' (b,e) (r:rs) = if b == b' then g' (b, e + e') rs  -- group by common base on sorted list
                                                  else (b,e):g' (b', e') rs
                                       where (b', e') = r
                     g' ce    _      = [ce]

                     -- take each entry in f and compute the gcd.  ToDo: replace with fold
                     spF n (f:fs)    = spF (concat $ map (proc f) n) fs -- this is quadratic but likely with very short lists
                                       where proc (pf, _) (pn, en) = if g == 1 || g == pn then [(pn, en)]
                                                                     else [(g, en), (div pn g, en)]
                                                                     where g = gcd pn pf
                     spF n _         = n

-- Predicates used for special cases of GCD and LCM
gcrUnsmooth, gcrIncompFact :: GCR_ -> Bool
gcrUnsmooth    = any (\ce -> not $ gcrSmooth ce)
gcrIncompFact  = any gcrBigComposite

gcrBigComposite, gcrSmooth :: GCRE_ -> Bool
gcrSmooth       (b,_) = b <= crSmallFactCutoff
gcrBigComposite (b,_) = bigComposite b

bigComposite :: Integer -> Bool
bigComposite b = crFactCutoff > 0 && b > crFactCutoff && (not $ isPrime b)
{-  Use cSuperLog instead
gcrLogDouble :: GCR_ -> Double
gcrLogDouble g = sum $ map (\(p,e) -> (log $ fromIntegral p) * (cToD e)) g
-}

divisionError :: String
divisionError = "gcrDiv: As requested per param, the dividend must be a multiple of the divisor." 

divByZeroError :: String
divByZeroError = "gcrDiv: Division by zero error!"

zeroDivZeroError :: String
zeroDivZeroError = "gcrDiv: Zero divided by zero is undefined!"

gcrDivStrict :: GCR_ -> GCR_ -> GCR_
gcrDivStrict x y = case gcrDiv x y of
                   Left errorMsg -> error errorMsg
                   Right results -> results

gcrDiv :: GCR_ -> GCR_ -> Either String GCR_
gcrDiv Pg0 Pg0 = Left zeroDivZeroError 
gcrDiv Pg0 _   = Right gcr0
gcrDiv _   Pg0 = Left divByZeroError
gcrDiv n   d   = g' n d 
                 where g' x     POne = Right x
                       g' POne  _    = Left divisionError
                       g' x     y 
                                     | gcrNegative y  = g' (gcrNegate x) (gcrAbs y)
                                     | otherwise      = case compare xp yp of      
                                                        LT           -> case (g' xs y) of
                                                                        Left _    -> Left divisionError
                                                                        Right res -> Right ((xp, xe) : res)
                                                        EQ | xe > ye -> case (g' xs ys) of
                                                                        Left _    -> Left divisionError
                                                                        Right res -> Right ((xp, xe - ye) : res)
                                                        EQ | xe == ye -> gcrDiv xs ys
                                                        _             -> Left divisionError                     
                                                        where ((xp,xe):xs) = x
                                                              ((yp,ye):ys) = y 

-- GCR functions (GCR is an acronym for generalized canonical representation)
gcrAbs :: GCR_ -> GCR_
gcrAbs x | gcrNegative x = tail x
         | otherwise     = x

gcrToCR :: GCR_ -> CR_
gcrToCR c = map (\(p,e) -> (p, cToI e)) c

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

gcrOdd, gcrEven :: GCR_ -> Bool
gcrOdd Pg0  = False
gcrOdd POne = True
gcrOdd c    | gcrNegative c  = gcrOdd (gcrAbs c)
            | otherwise      = cp /= 2 
              where (cp,_):_ = c

gcrEven g   = not (gcrOdd g)

gcrEqCheck :: GCR_ -> GCR_ -> Bool
gcrEqCheck POne         POne         = True
gcrEqCheck POne         _            = False
gcrEqCheck _            POne         = False 
gcrEqCheck ((xp,xe):xs) ((yp,ye):ys) | xp /= yp || xe /= ye = False 
                                     | otherwise            = gcrEqCheck xs ys
gcrEqCheck x            y            = error e
                                     where e = "Non-exhaustive patterns in gcrEqCheck comparing " ++ show x ++ " to " ++ show y

gcrSimplified :: GCR_ -> Bool
gcrSimplified = all (\(b,e) -> cSimplified e && check b) 
                where check n = crFactCutoff <= 0 || n < crFactCutoff || (n > crFactCutoff && isPrime n)

-- | Return the base b from a Canon Element (equivalent to b^e)
cGetBase :: CanonElement -> Canon
cGetBase (b, _) = b

-- | Return the exponent e from a Canon Element (equivalent to b^e)
cGetExponent :: CanonElement -> Canon
cGetExponent (_, e) = e

-- | Return the list of bases from a Canon (conceptually of the form [b^e])>
cGetBases :: Canon -> [Canon]
cGetBases = cGetBases' False False False -- don't check if in range

cGetBases' :: Bool -> Bool -> Bool -> Canon -> [Canon]
cGetBases' f d h c -- if f flag True, only keep the "True" matches based on allowed hyper op level range
                   -- if d flag True, only return the bases that occur more than once (for grouping later)
                   -- if h flag True, only include the "hyper bases"
  = if d then rMultiple else nub r'
    where rMultiple            = map fst $ filter (\(_,ct) -> ct /= 1) $ map (\l -> (head l, length l)) $ group $ sort r'
          r'                   = map fst $ if f then (filter (\(_, f') -> f') r) else r
          r                    = g' (abs c) h
          g' b@(Bare _ _)   h' = if h' || b == c1 then [] else [(b,True)]
          g' (Can g _)      h' = map (\c' -> (cGetBase $ convGCREToCE c', True)) g2
                                 where g2 = if not h' then g else (filter (\(_,e) -> cHyperExprAny e) g)
          g' c'@(HX PoA _ _) _ = [(c', not $ (f && (cHyOpLvlOutOfRange $ cGetHyperOp c')))] -- return sum itself, only option.
          g' (HX PoM cL _)  h' = concat $ (g' (head cL) h'):(map (\e -> g' e False) (tail cL))
                                 -- ToDo: weave in mult check even though in range
          g' (HX y cL _)    _  = map (\(c',_) -> (c',pF)) $ g' (head cL) False
                               where pF = not $ f && cHyOpLvlOutOfRange y -- If true, we drill down
                               -- e.g 3^4 or 3<^>4.  First member of list is 3.  Could also be a composite

-- | Similar to cGetBases except that it will do trial factoring of any hyper sums.  So, for obvious reasons, this is not a complete factorization.
cGetBasesDeep :: Canon -> [Canon]
cGetBasesDeep c@(HX PoA l _) = sort $ nub ((c':i) ++ sF)
                               where i  = foldl1 intersect $ map cGetBasesDeep l
                                     iP = product i
                                     c' = simpleHX cAddOpLevel (map (\a -> div a iP) l)
                                     sF = filter (\p -> mod c p == 0) $ smallPrimeCanons
cGetBasesDeep c            = cGetBases c

-- | Return the list of exponents from a Canon (conceptually of the form [b^e]).
cGetExponents :: Canon -> [Canon]
cGetExponents (Bare _ _)    = [c1] -- always just one
cGetExponents (Can g _)     = map (cGetExponent . convGCREToCE) g
cGetExponents (HX PoA _ _)  = [c1] -- this is a sum so the exponent is just one
cGetExponents hx@(HX _ _ _) = map (cGetExponent . convGCREToCE) $ cToGCR hx

-- | Return the list of CanonElements from a Canon (conceptually of the form [b^e]).
cGetElements:: Canon -> [CanonElement] 
cGetElements b@(Bare _ _)  = [(b, c1)]
cGetElements (Can g _)     = map convGCREToCE g
cGetElements hx@(HX _ _ _) = map convGCREToCE $ cToGCR hx

-- | Convert a generalized canon rep element to a CanonElement
convGCREToCE :: GCRE_ -> CanonElement
convGCREToCE (b, e) = (makeCanon b, e) -- ToDo: Optimize as b is already known to be a prime here

-- | Divisor functions should be called with integral Canons. Restricted to positive divisors. Returns Either String Canon
cNumDivisors, cTau :: Canon -> Canon
cNumDivisors c = case (cNumDivisors' c) of
                 Left  s -> error s
                 Right v -> v

cTau = cNumDivisors

-- | Underlying divisor function that can return value or (error) message.
cNumDivisors' :: Canon -> Either String Canon
cNumDivisors' c 
  | not (canComputeDivs c') = Left $ "Canon was zero, not integral or not completely factored.  Can't compute."
  | otherwise               = case cToGCR' c' of 
                              Just g -> Right $ product $ map (\(_,e) -> 1 + e) g
                              Nothing -> Left "Unknown issue converting to underlying GCR structure." 
  where c' = abs c

-- | Compute the nth divisor of a Canon. It operates on the absolute value of the Canon and is zero based.
--   Note: This is deterministic but it's not ordered by the value of the divisor.
cNthDivisor :: Canon -> Canon -> Either String Canon
cNthDivisor _ (Bare _ NSim)  = Left "cNthDivisor: Bare integer has not been simplified."
cNthDivisor n c | cNegative n || not (cIntegral n) 
                                          = Left "cNthDivisor: Both n must be integral and  >= 0" 
                | not (canComputeDivs aC) = Left "cNthDivisor: Canon was zero, not integral or not completely factored.  Can't compute"
                | cHyperExpr c            = nthHyper $ cToGCR aC
                | otherwise               = nth aC 
                where aC      = abs c 
                      nth Pc0 = Right n -- Zero has an infinite set of divisors.  The nth divisor is just n as a Canon
                      nth cn  = case f (cAbs n) (cToGCR cn) of
                                Right r -> Right $ gcrToC r
                                Left e  -> Left e
                                where f Pc0 _   = Right gcr1
                                      f _   Pg1 = Left "cNthDivisor: Bad dividend number requested."
                                      f n'  c'  = case f (div n' (e + 1)) cs of     -- First param is the next n
                                                  Right r -> Right $ if m == c0 then r else ((b,m):r)
                                                  e'      -> e' -- Return error message  
                                                  where (b,e):cs = c'   
                                                        m        = mod n' (e + 1)
                      nthHyper :: GCR_ -> Either String Canon
                      nthHyper x | n >= nd              = Left "cNthDivisor: Bad dividend number requested of hyper expression."
                                 | otherwise            = Right $ compute n divL c1
                                 where nd                       = product $ map snd divL -- Number of dividends
                                       divL                     = map (\(p,e) -> (Bare p Simp, e + 1)) x
                                       compute n' ((p,d):ds) wP | nq == 0   = newWp -- at 0, no need to continue
                                                                | otherwise = compute nq ds newWp
                                                                where (nq, m)    | n' < d    = (c0, n') 
                                                                                 | cHyperExpr d && n' < 100 * d
                                                                                             = proc n' (0 :: Int)
                                                                                 | otherwise = (quotRem n' d) -- limited -- ToDo: make it smarter
                                                                      newWp      = if m == c0 then wP else (wP * p <^ m)
                                                                      proc n2 rc | n2 < d    = (makeCanon $ toInteger rc, n2)
                                                                                 | otherwise = proc (n2 - d) (rc + 1)
                                       compute _  _      wP     = wP

-- | Consider this to be the inverse of the cNthDivisor function.  This function ignores signs
--   but both parameters must be integral.
cWhichDivisor :: Canon -> Canon -> Either String Canon
cWhichDivisor d c | not (cIntegral d)       = Left "cWhichDivisor: d must be integral" 
                  | d == c0                 = Left "cWhichDivisor: Zero is not a proper divisor"
                  | d == c1 && aC /= c0     = Right c0
                  | not (canComputeDivs aC) = Left "cWhichDivisor: Canon was either zero or not completely factored.  Can't compute"
                  | d == c                  = Right $ cNumDivisors c - 1
                  | otherwise               = case gcrDiv gAc gAd of
                                              Right _ -> Right $ wD gAd divLProg c0 -- valid divisor so it's safe to compute
                                              Left _  -> Left "cWhichDivisor: d is not a divisor of c"
                  where (aD, aC, gAd, gAc)                = (abs d, abs c, cToGCR aD, cToGCR aC)
                        divLProg                          = zip (map fst gAc) (c1:(init $ scanl1 (*) $ map (\(_,e) -> e + 1) gAc))
                        wD a@((aP,aE):as) ((bP,bC):bs) wS | aP < bP   = error "Logic error: Unexpected factors found in divisor"
                                                          | aP > bP   = wD a bs wS
                                                          | otherwise = wD as bs (wS + aE * bC)
                        wD a              _            wS | null a    = wS
                                                          | otherwise = error "Logic error: Unexpected factors found in divisor"

-- | Efficiently compute all of the divisors based on the canonical representation.
-- | Returns Either an error message or a list of Canons.
cDivisors :: Canon -> Either String [Canon]
cDivisors c | not (canComputeDivs c') = Left "cWhichDivisor: Canon was either zero or not completely factored.  Can't compute"
            | otherwise               = divs c'
            where c' = abs c
                  divs (Bare x _) | x == 1    = Right [c1]
                                  | otherwise = Right [c1, makeCanon x] 
                  divs (Can g _)  = Right $ map gcrToC $ foldr1 cartProd $ map pwrDivList g
                                    where cartProd xs ys   = [x ++ y | y <- ys, x <- xs]
                                          pwrDivList (n,e) = [if y == 0 then gcr1
                                                                        else [(n, makeCanon y)] | y <- [0 .. cToI e]]
                  divs _          = error "cDivisors can't return all of the divisors for hyper expressions!"

-- | Return the first N divisors of a hyper expression (if possible)
cGetFirstNDivisors :: Int -> Canon -> Either String [Canon]
cGetFirstNDivisors n c@(HX _ _ IntC) 
                       | any errPred divList = Left "cGetNDivisors: Canon was either zero or not completely factored.  Can't compute"
                       | otherwise           = Right $ map clean divList 
                       where divList = map (\i -> cNthDivisor (makeCanon $ toInteger i) c) [0..n-1]
                             errPred (Left _)  = True
                             errPred (Right _) = False
                             clean (Left _)    = error "'Dirty list' passed to clean function"
                             clean (Right v)   = v     
cGetFirstNDivisors n c = case cDivisors c of
                         Right ds -> Right $ take n ds
                         msg      -> msg

-- Assumes unsigned input
canComputeDivs :: Canon -> Bool
canComputeDivs c | cBare c && (cToI c == 0)                    = False
                 | not (cSimplified c) || not (cIntegral c)    = False
                 | not (cHyperExpr c)                          = True
                 | cHyperSum c                                 = False
                 | cGetHyperOp c > maxHyperOpDelveLevel        = False
                 | cHyperProd c && not (all canComputeDivs cL) = False
                 | otherwise                                   = canComputeDivs b
                 where cL@(b:_) = cGetHyperList c

smallPrimeCanons :: [Canon]
smallPrimeCanons = map (\p -> Bare p Simp) $ map unPrime $ take 1000 primes

-- | This will determine if two arbitary expressions are relatively prime or not (if possible).  Goes deep.
cRelativelyPrime :: Canon -> Canon -> Maybe Bool
cRelativelyPrime x y | x == c1 || y == c1     = Just True
                     | cEven x && cEven y     = Just False
                     | not (null iBs)         = Just False -- Intersection between the bases
                     | xHs == c1 && yHs == c1 = Just True
                     | xHs /= c1 && f xHs yB  = Just False
                     | yHs /= c1 && f yHs xB  = Just False
                     | xHs /= c1 && yHs /= c1 = if hpi then (Just False) else Nothing
                     | otherwise              = Nothing
                     where (xB, yB)     = (cGetBases x, cGetBases y)
                           iBs          = intersect xB yB
                           hs b         = product $ filter cHyperSum $ b
                           (xHs, yHs)   = (hs xB, hs yB)
                           f x' l       = any (\p -> mod x' p == 0) l -- does anything in l divide the hyperexpression x
                           hpi          = any (\p -> mod x p == 0 && mod y p == 0) $ smallPrimeCanons -- hyper prod intersection

-- Super Log Logic:
-- This section allows for comparison of hyperoperations by converting to a super log
-- For instance: 9 ^ (8 ^ 7) = 10 ** 10 ** 6.301288668477042.  We represent the super log as (2, 6.301288668477042)

-- | Used when computing "Super Log"
type SuperPairC = (Canon, Double)
type SuperPairI = (Integer, Double)

-- Trick to handle floating point issues (https://stackoverflow.com/questions/2354707/in-haskell-is-there-infinity-num-a-a)
infinity :: Double
infinity = read "Infinity"

integerDblCutoff, manualLB :: Integer
integerDblCutoff = 2 ^ ((snd $ floatRange (1.0 :: Double)) - 1) -- integral upper bound for converting to doubles.
-- Note: I reduced this by one to be safe. When testing in 8.4.3, I noticed some inconsistent behavior close to 2^1024
manualLB = lBI ^ (16 :: Int) -- manually walk down number to this lower bound to get significant 'digits'

dblLogMantissaUB :: Double
dblLogMantissaUB = logD $ fromInteger integerDblCutoff -- we can safely compute lB ** lB ** doubleLogMantissaCutoff

-- This is the cutoff for converting numbers to integers
superLogICutoff :: SuperPairI
superLogICutoff = (2, 5.0) -- 10^10^5

cSuperLogCutoff :: SuperPairC
cSuperLogCutoff = (makeCanon $ fst superLogICutoff, snd superLogICutoff) -- 10^10^5

-- |  This is the super or iterated log function.  A level and mantissa is returned along with the number's sign.  
cSuperLog :: Canon -> (SuperPairC, Int)
-- cSuperLog c | trace ("cSuperLog: Processing: (c=" ++ show c ++ ")") False = undefined
cSuperLog (Bare n _)        = (makeSuperLogC $ superLogI n, if n > 0 then 1 else (-1))
cSuperLog c@(Can g _)       = if d == c1 then (superLogCan g, s) -- ToDo: if contains a hyperexpr, convert all?
                                         else (slDiv (superLogCan $ cToGCR n) (superLogCan $ cToGCR d), s)
                              where (n, d) = cSplit c 
                                    s      = if cPositive c then 1 else (-1)
cSuperLog (HX PoA s _)      = cSuperLogSum s
cSuperLog (HX PoM p _)      = cSuperLogProd p 
cSuperLog (HX PoE e _)      = (cSuperLogExp e, 1) -- ToDo: always positive?

-- beyond exponentiation, get the tower height from the tail and adjust by offset
cSuperLog c@(HX h (b:cs) _) | h > maxHyperOpDelveLevel = error $ "Unable to take cSuperLog of massive hyper expression: " ++ show c
                            | h == cTetrOpLevel        = ((sv1 + offset, m), 1) -- in case the cNestExpTail is not a hyper expr.
                            | otherwise                = ((c1 + offset + (head $ tail $ cGetHyperList $ cNestExpTail c False), m), 1)
                            where (offset, m) = getTowerMantissa b sv1
                                  sv1         = cApplyHy h cs True
cSuperLog _                 = error "Logic error in Super Log: Default Canon configuration unexpectedly reached"

-- This implemented in the comparison logic.  This reveals that instead of comparing (3 <<^>> 7) to (5 <<^>> 6) with super log
-- we can compare superlog of 3 <<^>> 3 to 5 <<^>> 2
-- How the function would look: cSuperLogIter x n = if (n < 2) then (cSuperLog x) else (cSuperLog $ fst $ fst $ cSuperLogIter x (n-1)) 

superLogCan :: GCR_ -> SuperPairC -- don't really need to keep track of the sign
superLogCan g = fst $ slProd $ map f g -- convert gcr to powerTower of sls for each base and then their products
                      where f (b, e) = if e == 1
                                       then cSuperLog (bFmt b)
                                       else (cSuperLogExp ((bFmt b):[e]), if b > 0 then 1 else (-1))
                            bFmt b   = (Bare b Simp)

-- for a power tower, the mantissa doesn't change (or more than negiligibly) after this height: 2 <^> x is the most "volatile".
towerHeight :: Integer
towerHeight = 8

towerHeightC :: Canon
towerHeightC = makeCanon towerHeight

-- get the tower mantissa (allowing from something shorter than the "towerHeight" above
getTowerMantissa :: Canon -> Canon -> (Canon, Double)
getTowerMantissa b h = (lvl - makeCanon htu, m) 
                   where (lvl, m) = slExp $ replicate (fromInteger htu) slb -- replicate the superlog "hgt" times
                         slb      = fst $ cSuperLog b
                         htu      = if h < towerHeightC then (cToI h) else towerHeight

integerShowCutoff :: Integer -- numbers larger than this won't be fully printed by default
integerShowCutoff = (10 :: Integer) ^ (1000 :: Integer)

superLogI :: Integer -> SuperPairI
superLogI i | i > 0    = suL i
            | i < 0    = suL $ abs i
            | otherwise = (0, 0.0) -- integral superlog rep. for zero
            where suL n | n > integerDblCutoff = refine $ spLog' (1, mC 0 n) 
                                                 -- manually compute above: save the last few significant digits
                        | otherwise            = refine $ spLog' (0, iToD) 
                        where spLog' (lvl', n')  
                                       = if ln > lB then (spLog' (lvl' + 1, ln)) else (lvl', n') 
                                         where ln = logB n'
                              iToD    | d == infinity = error "Raise bug: Number below cutoff still returning infinity."
                                      | otherwise     = d
                              d       = fromIntegral n
                              mC :: Integer -> Integer -> Double
                              mC c n' | n' <= manualLB = fromIntegral c + (logB $ fromIntegral n') 
                                      | otherwise      = mC (c+1) (div n' lBI) 
                              refine (l,v) = if v > lB  -- similar to slRefine
                                             then refine (l+1, logB v)
                                             else (if (v < 1.0 || (v == 1 && l > 0))
                                                   then (l-1, powB v) else (l, v))

makeSuperLogC :: SuperPairI -> SuperPairC -- Promote to a Canon
makeSuperLogC (spi, d) = (makeCanon spi, d)

cSuperLogProd, cSuperLogSum :: [Canon] -> (SuperPairC, Int)
cSuperLogProd cL = slProd $ map cSuperLog cL
cSuperLogSum  cL = slSum  $ map cSuperLog cL

slEpsilon :: Double
slEpsilon = 2.0 * 10.0 ** (-15.0) -- necessary for testing equality.  Some rounding error can occur

slProd, slSum :: [(SuperPairC, Int)] -> (SuperPairC, Int)
slProd sL | null sL   = error "Null list passed to slProd" -- ((c0, 1.0), 1) -- rep for nullary product aka 1
          | otherwise = foldl1 (\(s, b) (ws, wb) -> (slMult s ws, b * wb)) sL 

slSum l | length posCL == 0                 = (negSL, -1)    -- all negative
        | length negCL == 0                 = (posSL, 1)     -- all positive
        | pl == nl && pm == nm              = ((c0, 0.0), 0) -- superlog representation for zero 
        | (pl == nl && pm > nm) || pl > nl  = (cmpSl posSL negSL, 1)
        | otherwise                         = (cmpSl negSL posSL, -1)
        where (posCL, negCL) = partition (\(_, s) -> s == 1) l -- partition by positive then negative
              posSL   = foldl1 slAdd $ map fst posCL
              negSL   = foldl1 slAdd $ map fst negCL
              (pl,pm) = posSL
              (nl,nm) = negSL
              cmpSl (l1, m1) (l2, m2) = case (l1 - l2) of
                                        0 -> case l1 of
                                             0 -> (l1, m1-m2) -- literally m1 - m2
                                             1 -> slRefine (l1, logB $ powB m1 - powB m2) -- lB^3 - lB^2
                                             _ | l1 == c2 && m1 < dblLogMantissaUB ->     -- lB^lB^2 - lB^lB^1.5
                                                   slRefine (l1, logD $ powD m1 - powD m2)
                                             _ | otherwise ->
                                                   (l1, m1) -- ToDo: This is not accurate if l1 = 2 and m1 - m2 is v. small
                                                            -- This needs a more robust solution
                                        1 -> case l1 of
                                             1 -> slRefine (l1, logB $ powB m1 - m2)    -- lB^2 - 3
                                             _ | l1 == c2 && m1 < dblLogMantissaUB ->   -- lB^lB^2 - lB^3
                                                   slRefine (l1, logD $ powD m1 - powB m2)
                                             _ | otherwise ->
                                                   (l1, m1) 

                                        _ | l1 == c2 && m1 < dblLogMantissaUB ->   -- lB^lB^2 - 3
                                              slRefine (l1, logD $ powD m1 - m2)
                                        _ | otherwise ->
                                              (l1, m1) 
 
slAdd, slMult, slDiv :: SuperPairC -> SuperPairC -> SuperPairC

slAdd e1 e2 = if cSuperLogGT e1 e2 then (add2 e1 e2) else (add2 e2 e1) -- larger first
              where add2 (l1, m1) (l2, m2) = case l1 - l2 of
                                             0 -> case l1 of
                                                  0 -> slRefine (l1, m1 + m2) -- just m1 + m2
                                                  1 -> slRefine (l1, logB $ powB m1 + powB m2) -- lB^3 + lB^2

                                                  -- lB^lB^3 + lB^lB^2 and take double logB if in range
                                                  _ | l1 == c2 && m1 < dblLogMantissaUB && tot < integerDblCutoff ->
                                                        slRefine (l1, logD $ m1pd + m2pd)
                                                        where (m1pd, m2pd) = (powD m1, powD m2)
                                                              tot = round m1pd + round m2pd + 1 -- insurance
                                                  _ | otherwise                         ->
                                                        (l1, m1)

                                             1 -> case l1 of
                                                  1 -> slRefine (l1, logB $ powB m1 + m2) -- lB^2 + 3 and take log

                                                  -- lB^lB^2 + lB^3 and take double log if in range
                                                  _ | l1 == c2 && m1 < dblLogMantissaUB ->
                                                        slRefine (l1, logD $ powD m1 + powB m2)
                                                  _ | otherwise ->
                                                        (l1, m1) 

                                             _ | l1 == c2 && m1 < dblLogMantissaUB ->
                                                   slRefine (l1, logD $ powD m1 + powB m2) -- lB^lB^2 + 3 and dbl logB
                                             _ | otherwise -> 
                                                   (l1, m1)

slMult e1 e2 = if cSuperLogGT e1 e2 then (mul2 e1 e2) else (mul2 e2 e1) -- larger first
               where mul2 (l1, m1) (l2, m2) = case l1 - l2 of
                                              0 -> case l1 of
                                                   0 -> slRefine (l1, m1 * m2) -- 2 * 3
                                                   1 -> slRefine (l1, m1 + m2) -- lB^3 * lB^2 = lB ^ (3+2)
                                                   -- lB^lB^3 * lB^lB^2 = lB ^(lB^3 + lB^2) and take logB
                                                   2 -> slRefine (l1, logB $ powB m1 + powB m2) 

                                                   -- lB^lB^lB^3 * lB^lB^lB^2 = lB ^(lB^lB^3 + lB^lB^2) and take logD 
                                                   _ | l1 == c3 && m1 < dblLogMantissaUB && tot < integerDblCutoff ->
                                                         slRefine (l1, logD $ m1pd + m2pd)
                                                         where (m1pd, m2pd) = (powD m1, powD m2)
                                                               tot = round m1pd + round m2pd + 1 -- insurance
                                                   _ | otherwise ->
                                                         (l1, m1) 

                                              1 -> case l1 of
                                                   1 -> slRefine (l1, m1 + logB m2) -- lB^2 * 3 = lB^(2 + logB 3)
                                                
                                                   -- lB^lB^2 * lB^3 = lB^(lB^2 + 3) and take logB
                                                   2 -> slRefine (l1, logB $ powB m1 + m2)
                                    
                                                   -- lB^lB^lB^2 * lB^lB^3 = lB^(lB^lB^2 + lB^3) and take dbl logB if ...
                                                   _ | l1 == c3 && m1 < dblLogMantissaUB ->
                                                         slRefine (l1, logD $ powD m1 + powB m2)
                                                   _ | otherwise -> 
                                                         (l1, m1)

                                              2 -> case l1 of
                                                   -- lB^lB^2 * 3 = lB^(lB^2 + logB 3) and take logB
                                                   2 -> slRefine (l1, logB $ powB m1 + logB m2)

                                                   -- lB^lB^lB^2 * lB^3 = lB^(lB^lB^2 + 3) and take dbl log if ...
                                                   _ | l1 == c3 && m1 < dblLogMantissaUB ->
                                                         slRefine (l1, logD $ powD m1 + m2)
                                                   _ | otherwise ->
                                                         (l1, m1)

                                              _ | l1 == c3 && m1 < dblLogMantissaUB ->
                                                    slRefine (l1, logD $ powD m1 + logB m2)
                                              _ | otherwise ->
                                                    (l1, m1)

slDiv a@(l1', m1') b@(l2', m2')
  | l1' < 0 && l2' < 0 = slDiv (slInvert b) (slInvert a)
  | l2' < 0            = slMult a (slInvert b)
  | l1' > l2' || (l1' == l2' && m1' > m2') 
                     = slRefine $ slDiv' a b
  | otherwise        = slInvert $ slRefine $ slDiv b a 
  where slInvert (l, m) = (negate l,  m) 
        slDiv' (l1, m1) (l2, m2) -- The 1st is > than the 2nd at this point and both levels are non-negative.
          | l1 == 0    = (c0, m1 / m2)                       -- simple division  
          | l1 == 1    = case l2 of
                         0 -> (l1, m1 - logB m2)             -- lB ^ (m1 - logB m2)
                         _ -> (l1, m1 - m2)                  -- lB ^ (m1 - m2)
          | l1 == 2    = case l2 of
                         0 -> (l1, logB (powB m1 - logB m2)) -- lB ^ (lB^m1 - logB m2)
                         1 -> (l1, logB (powB m1 - m2))      -- lB ^ (lB^m1 - m2)
                         _ -> (l1, logB (powB m1 - powB m2)) -- lB ^ (lB^m1 - lB^m2)               
          | l1 == 3 && m1 < dblLogMantissaUB 
                       = case l2 of
                         0 -> (l1, logD (powD m1 - logB m2)) -- lB ^ (lB^lB^m1 - logB m2)
                         1 -> (l1, logD (powD m1 - m2))      -- lB ^ (lB^lB^m1 - m2)
                         2 -> (l1, logD (powD m1 - powB m2)) -- lB ^ (lB^lB^m1 - lB^m2)   
                         _ -> (l1, logD (powD m1 - powD m2)) -- lB ^ (lB^lB^m1 - lB^lB^m2)  
          | otherwise  = (l1, m1) 
                    
-- Exp short for exponent.  Interpret as a power tower (e.g. 2 ^ (3 ^ (5 ^ 7)))
cSuperLogExp :: [Canon] -> SuperPairC
cSuperLogExp cL = slExp $ map (fst . cSuperLog) cL -- ignore the sign returned. 

slExp :: [SuperPairC] -> SuperPairC
slExp (x:r@(_:_)) = combineS x (slExp r) -- ToDo: change this to a fold
                    where combineS (nl, nm) (rl, rm) 
                           -- Note in the comments below, ^ is a bit more legible than ** and internally, doubles are used
                           = case rl of
                             0 -> case nl of
                                  0 -> slRefine (nl, nm ** rm) -- 2 ^ 3
                                  1 -> slRefine (nl, nm * rm) -- (lB^2) ^ 3 = lB^(2 * 3)

                                  -- (lB^lB^2) ^ 3 = lB^(3 * lB^2) = lB^lB^(2 + logB 3)
                                  2 -> slRefine (nl, nm + logB rm) 

                                  -- (lB^lB^lB^2) ^ 3 = lB^(3 * lB^lB^2) =
                                  -- lB ^ (lB^logB 3 * lB^lB^2) = lB^lB^(lB^2 + logB 3) then take the log
                                  3 -> slRefine (nl, logB $ powB nm + logB rm)

                                  -- at this point the remainder has minimal to no effect
                                  _ | nl == 4 && nm < dblLogMantissaUB 
                                        -> slRefine (nl, logD $ powD nm + logB rm)
                                    | otherwise  
                                        -> (nl, nm) -- rm has no effect 

                             1 -> case nl of 
                                  -- 2 ^ (lB^3)  = lB ^ (logB 2 * (lB ^ 3)) -- then progression from 0 to 2
                                  0 -> slRefine (rl, logB nm * powB rm)
                                  1 -> slRefine (rl, nm      * powB rm)
                                  2 -> slRefine (rl, powB nm * powB rm)

                                  -- (lB^lB^lB^2) ^ (lB^3) = lB ^ (lB^lB^2 * lB^3) = 
                                  -- lB^lB^(lB^2 + 3) = then take double log 
                                  3 -> slRefine (nl, logB $ powB nm + rm)

                                  -- at this point the remainder has minimal to no effect.  Note: We go down a level
                                  _ | nl == 4 && nm < dblLogMantissaUB
                                        -> slRefine (nl,logD $ powD nm + rm)
                                    | otherwise                       
                                        -> (nl, nm) -- rm has no effect 

                             2 -> case nl of
                                  -- 2 ^ (lB^lB^3) = lB ^ (log2 * lB^lB^3) = lB ^ (lB^logLog2 * lB^lB^3) = 
                                  -- lB ^ lB ^ (logLog2 + lB^3).  Then, there's a progression
                                  0 -> slRefine (rl, logD nm + powB rm)
                                  1 -> slRefine (rl, logB nm + powB rm)
                                  2 -> slRefine (rl, nm      + powB rm)
                                  3 -> slRefine (rl, powB nm + powB rm)

                                  -- at this point the remainder has minimal to no effect.  Note: We go down 2 levels
                                  -- (lB^lB^lB^lB^2) ^ (lB^lB^3) = lB ^ (lB^lB^lB^2 * lB^lB^3) =
                                  -- lB^lB^(lB^lB^2 + lB^3) then take double log and reduce a level
                                  _ | nl == 4 && nm < dblLogMantissaUB ->
                                      slRefine (rl, powD nm + powB rm)
                                    | otherwise ->
                                      (nl, nm) -- rm has no effect

                             _ | rl == 3 && rm < dblLogMantissaUB ->
                                 -- 2 ^ (lB^lB^lB^3) = lB^(log2 * lB^lB^lB^3) = 
                                 -- lB^(lB^logD 2 * lB^lB^lB^3) = lB^lB^(logD 2 + lB^lB^3)
                                 -- Then we use similar logic for the progression of nl from 0 to 3
                                 case nl of -- note the progression
                                 0 -> slRefine (rl, logB $ logD nm + powD rm) 
                                 1 -> slRefine (rl, logB $ logB nm + powD rm)
                                 2 -> slRefine (rl, logB $ nm      + powD rm)
                                 3 -> slRefine (rl, logB $ powB nm + powD rm)
                                 4 -> if nm < dblLogMantissaUB && tot < integerDblCutoff
                                      then slRefine (rl, logB $ nmpd + rmpd)
                                      else (nl, max nm rm) 
                                      where (nmpd, rmpd) = (powD nm, powD rm) 
                                            tot = round nmpd + round rmpd + 1 -- insurance
                                 _ -> (nl, nm) -- just use nl     
                                
                               | otherwise -> -- beyond we just compare the current and remainder
                                 case compare nl (rl + c1) of
                                 EQ -> (nl,      max nm rm)
                                 GT -> (nl,      nm)
                                 LT -> (rl + c1, rm)

slExp (x:_)       = slRefine x
slExp _           = (0, 1.0) -- nullary product / poewr tower

slRefine :: SuperPairC -> SuperPairC
slRefine (lvl, v) = if v > lB
                    then slRefine (lvl + c1, logB v)
                    else (if v <= 1.0 then (lvl - c1, powB v) else (lvl, v))

-- | Compare the level and the "mantissa"
cSuperLogCmp :: SuperPairC -> SuperPairC -> Ordering
cSuperLogCmp (l1, m1) (l2, m2) | l1 > l2                   = GT
                               | l1 < l2                   = LT
                               | abs (m1 - m2) < slEpsilon = EQ
                               | otherwise                 = if l1 >= 0 then (compare m1 m2) else (compare m2 m1)

cSuperLogGT :: SuperPairC -> SuperPairC -> Bool
cSuperLogGT x y = case cSuperLogCmp x y of
                       GT -> True
                       _  -> False

lBI :: Integer
lBI = 10

lB :: Double
lB = fromIntegral lBI

logB, logD, powB, powD :: Double -> Double
logB a = log a / log lB
logD a = logB $ logB a
powB a = lB ** a
powD a = lB ** (lB ** a) 

-- | Instance of CanonConv class 
instance CanonConv Canon where
  toSC c = toSC $ cToCR c
  toRC c = toRC $ cToCR c
                                                                   
-- Canon of form x^1. (Does not match on 1 itself)
pattern PBare :: forall t. [(t, Canon)]
pattern PBare <- [(_, Bare 1 _)] 

-- Canon of form p^e where e >= 1. p has already been verified to be prime.
pattern PgPPower :: forall t a. (Num a, Ord a) => [(a, t)]
pattern PgPPower <- [(compare 1 -> LT, _ )]

-- Canon of form p^1 where p is prime
pattern PgPrime :: forall a. (Num a, Ord a) => [(a, Canon)]
pattern PgPrime <- [(compare 1 -> LT, Bare 1 _)] 

-- Pattern looks for Canons beginning with negative 1
pattern PgNeg :: forall a. (Num a, Eq a) => [(a, Canon)]
pattern PgNeg <- ((-1, Bare 1 _):_) 

-- Pattern for "generalized" zero
pattern Pg0 :: forall a. (Num a, Eq a) => [(a, Canon)]
pattern Pg0 <- [(0, Bare 1 _)]  -- internal pattern for zero

-- Pattern for "generalized" 1
pattern Pg1 :: forall t. [t]
pattern Pg1 = []

-- Patterns for 0-2
pattern Pc0 :: Canon
pattern Pc0 <- Bare 0 _

pattern Pc1 :: Canon
pattern Pc1 <- Bare 1 _ 

pattern PoA :: Canon
pattern PoA <- Pc1 -- addition operator

pattern Pc2 :: Canon
pattern Pc2 <- Bare 2 _

pattern PoM :: Canon
pattern PoM <- Pc2 -- multiplication operator

pattern Pc3 :: Canon
pattern Pc3 <- Bare 3_

pattern PoE :: Canon
pattern PoE <- Pc3 -- exponentiation operator

pattern PcN1 :: Canon  -- this pattern is only used in the "bad" function
pattern PcN1 <- Can [(-1, Bare 1 _)] _

-- | Maximum exponent (of a polynomial) to distribute into a sum of terms.
cMaxExpoToExpand :: Canon 
cMaxExpoToExpand = c4 

-- need to finesse this to get the right operation returned.  If sortByHypo has more than one entry, then it's a sum. 
-- Do we just create a hyper expr
distHyperExpr, distSum, distProduct, distExpo :: Canon -> Canon -> ([Canon], Bool)
distHyperExpr c m | h == cAddOpLevel        = (dS, dS /= hL) 
                  | h == cMultOpLevel && fP = (dP, fP) -- distributed product (and maybe poly)
                  | h == cExpOpLevel  && fE = (dE, fE) -- distributed exponential
                  | otherwise         = ([c], False)
                  where (h, hL)                    = (cGetHyperOp c, cGetHyperList c)
                        ((dS,_), (dP,fP), (dE,fE)) = (distSum c m, distProduct c m, distExpo c m)

distSum (HX PoA l _) m = (concat dM, any id fM)  
                         where (dM, fM) = unzip $ map (\x -> distHyperExpr x m) l -- check if any of the flags are set
distSum c            _ = ([c], False)

distProduct c@(HX PoM l _) m | not (null sums) = (dist (head sums') (tail sums') [computeExpr cMultOpLevel nonSums], True) 
                             | otherwise       = ([c], False)  -- nothing to distribute
                             where sums'           = map exP sums
                                   exP s           = if polyPred s m then simpleHX c1 (fst $ distExpo s m) else s -- clean up?
                                   (sums, nonSums) = partition (\e -> sumPred e || polyPred e m) l
distProduct c              _ = ([c], False)

-- distribute sum against list of canons
dist :: Canon -> [Canon] -> [Canon] -> [Canon]
dist x y wL | length y > 0 = dist (head y) (tail y) cartProd
            | otherwise    = cartProd
            where cartProd = if null wL then hLx else (concat $ map (\a -> map (* a) wL) hLx)
                  hLx      = cGetHyperList x

distExpo c m | polyPred c m = cExpandPoly (cGetHyperList $ head cL) (fromInteger $ cToI (cL !! 1)) m
             | otherwise   = ([c], False)
             where cL = cGetHyperList c

sumPred :: Canon -> Bool
sumPred c = cGetHyperOp c == cAddOpLevel

polyPred :: Canon -> Canon -> Bool -- The 2nd param is a cutoff for the exponent of the polynomial
polyPred (HX h (b:e:r) _) m = h == cExpOpLevel && sumPred b && e <= m && null r 
polyPred _                _ = False

cExpandPoly :: [Canon] -> Int -> Canon -> ([Canon], Bool)  -- e.g. (1 + x + y) ^ 3
cExpandPoly (a:r@(_:_:_)) e m = (eP, True) 
                                where eP = concat $ map (\x -> fst $ distHyperExpr x m) $ 
                                           concat $ map (\x -> fst $ distHyperExpr x m) $  -- two dists needed to flatten it out? To Do: Investigate
                                           fst $ cExpandPoly [a, simpleHX cAddOpLevel r] e m 
cExpandPoly (a:b:_)       e _ = (map (\i -> product [makeCanon $ binomial e i, raise a i, raise b (e-i)]) [0..e], True)
                                where raise b' e' | e' == 0   = c1
                                                  | e' == 1   = b'
                                                  | otherwise = expH b' (makeCanon $ toInteger e') 
cExpandPoly c             _ _ = (c, False) -- No-op now. ToDo: Should this be an error condition


factorial :: [Integer]
factorial = (1 :: Integer) : 1 : zipWith (*) [2..] (tail factorial)

binomial :: Int -> Int -> Integer
binomial n m | n < 0          = error "Binomial: n must be >= 0"
             | m < 0 || m > n = error "Binomial: m must be >= 0 and <= n"
             | otherwise      = div (factorial !! n) (factorial !! m * factorial !! (n-m))

-- This is essentially a wrapper to create a hyper expression from a hyper op and hyper list.  
-- This is lower level than calling cApplyHy / cHyperOp.  Must be used with care
computeExpr :: Canon -> [Canon] -> Canon
-- computeExpr hy l | trace ("computeExpr: Processing: (hy=" ++ show hy ++ ", l=" ++ show l ++ ")") False = undefined
computeExpr hy l
  | null nL                = dV
  | length nL == 1         = head nL
  | otherwise              = simpleHX hy nL 
  where
    nL        | hy == cAddOpLevel  = filter (/= dV) (hE ++ [f nHe])
              | hy == cMultOpLevel = filter (/= dV) ((f nHe):hE)
              | otherwise          = l 
    (hE, nHe) = partition cHyperExprAny l
    (dV, f)   | hy == cAddOpLevel  = (c0, sum)
              | otherwise          = (c1, product)

simplifySum, simplifyProd :: [Canon] -> Canon

-- simplifySum l | trace ("simplifySum: Processing: (" ++ show l ++ ")") False = undefined
simplifySum l  = checkToFlipSum $ combineSum $ computeExpr cAddOpLevel l

-- simplifyProd l | trace ("simplifyProd: Processing: (" ++ show l ++ ")") False = undefined
simplifyProd l = if (any (== 0) l) then c0 else (combineProd $ computeExpr cMultOpLevel l)

checkToFlipSum :: Canon -> Canon
checkToFlipSum r = if cGetHyperOp r == cAddOpLevel && cNegative r 
                   then simpleHX cMultOpLevel [cN1, negate r] -- flip the signs and mult by negative one
                   else r

addH, multH, expH, addH', multH', expH' :: Canon -> Canon -> Canon
(addH, multH, expH) = (prep addH', prep multH', prep expH')

prep :: (Canon -> Canon -> Canon) -> Canon -> Canon -> Canon
-- prep _ x y  | trace ("prep: Processing: (" ++ show x ++ ") and (" ++ show y ++ ")") False = undefined
prep f a b | (cHyperExprAny a || cHyperExprAny b) && (not (cIntegral a) || not (cIntegral b)) 
                                = error "Can't have sums or products with non-integers and hyper expressions"
           | otherwise          = f a b

-- addH' x y | trace ("addH': Processing: (" ++ show x ++ ") and (" ++ show y ++ ")") False = undefined
addH' (HX PoA l1 _)   (HX PoA l2 _)   = simplifySum $ l1 ++ l2
addH' (HX PoA lA _)   b               | cHyperSum b = simplifySum $ lA ++ (negSumList b)
                                      | otherwise   = simplifySum (b:lA)
addH' b               a@(HX PoA _ _)  = addH' a b -- flip the terms
addH' a@(HX PoM _ _)  b@(HX PoM _ _)  | aHs && bHs  = simplifySum $ aNs ++ bNs
                                      | aHs         = simplifySum (b:aNs)
                                      |        bHs  = simplifySum (a:bNs)
                                      | otherwise   = simplifySum [a,b]
                                      where (aHs, bHs) = (cHyperSum a, cHyperSum b)
                                            (aNs, bNs) = (negSumList a, negSumList b)
addH' a@(HX PoM _ _) b                | cHyperSum a = simplifySum (b:negSumList a)
                                      | otherwise   = simplifySum [a,b]
addH' b               a@(HX PoM _ _)  = addH' a b
addH' a               b               | cHyperExprAny a || cHyperExprAny b = simplifySum [a,b]
                                      | otherwise                          = a + b -- call the underlying function.  Shouldn't happen in practice.

-- multH' a b | trace ("multH': Processing: (" ++ show a ++ ") and (" ++ show b ++ ")") False = undefined
multH' a b | nhs a && nhs b               = simplifyProd [negate a, negate b] 
           | cHyperExpr a || cHyperExpr b = if snp == cN1 then negate hp else hp -- flip sign if needed (abs value only internally)
           | otherwise                    = fst $ cMult a b crCycloInitMap
           where nhs x = cHyperSum x && cGetHyperOp x == cMultOpLevel -- negative hyper sum
                 snp   = signum a * signum b
                 hp    = simplifyProd $ cGetFactors (abs a) ++ cGetFactors (abs b)

expH' a                b               | cHyperExprAny a || cHyperExprAny b = fst $ cHyperOp cExpOpLevel [a,b] crCycloInitMap 
                                       | otherwise                          = fst $ cExp a b False crCycloInitMap

negSumList :: Canon -> [Canon]
negSumList c = map negate $ cGetHyperList ((cGetHyperList c) !! 1)  -- e.g. -1 * (3 + 5) -> (-3 -5)

-- | Convert a hyperexpression to a sum if possible.  Useful in comparison. Will expand polynomials to a limited degree.
cConvertToSum :: Canon -> (Canon, Bool)
cConvertToSum x  = cConvertToSum' x cMaxExpoToExpand 

cConvertToSum' :: Canon -> Canon -> (Canon, Bool)
-- cConvertToSum' x m | trace ("cConvertToSum': (x = " ++ show x ++ ", m = " ++ show m ++ ")") False = undefined
cConvertToSum' x m | b         = (checkToFlipSum $ computeExpr cAddOpLevel (sortByHpo $ map f d), b) 
                   | otherwise = (x, b) -- just return itself.  "dist" didn't do change the expression 
                     where f c   = if cNegative c then (negate f') else f' 
                                   where f' = product $ cFlattenAndGroup' (abs c) m
                           (d,b) = distHyperExpr x m

-- qL = cGetHyperList q, rL = cGetHyperList r, g = intersect qL rL, q' = qL \\ g, r' = rL'
-- if there's a flag, filter out hyperexpressions from the gcd'
-- this is the first level the next level is 

-- Note: These "simple" functions promote Canons to an exponent level before manipulating them then it demotes them.
-- Example Transforms: a * b <^3 => [(a,1),(b,3)], x <^ y => [(x,y)], x + y => [(x+y, 1)], x <^> y => [(x <^> y, 1)]

-- Pass ax and ay and return a * (x + y) where x and y are "relatively prime"
simpleFactorPair :: Canon -> Canon -> Bool -> (Canon, Canon)
-- simpleFactorPair n d hF | trace ("simpleFactorPair: (n = " ++ show n ++ ", d = " ++ show d ++ ", hF = " ++ show hF ++ ")") False = undefined
simpleFactorPair n d hF = (applyFcnForHy v cMultOpLevel cFlattenAndGroup, gcd')
                          where (gcd', x', y') = simpleReduce n d hF
                                v              = computeExpr cMultOpLevel [gcd',x'+y']

-- Promote each param so it can be easily manipulated and then demote it and return the answers.
simpleReduce :: Canon -> Canon -> Bool -> (Canon, Canon, Canon)
-- simpleReduce n d hF | trace ("simpleReduce: (n = " ++ show n ++ ", d = " ++ show d ++ ", hF = " ++ show hF ++ ")") False = undefined
simpleReduce n d hF = (gcd', x', y')
  where proc xL@(x@(xP, xE):xs) yL wL wX wY 
                            | null yL       = (wL, (wX ++ xL), wY)
                            | null z        = proc xs yL wL (wX ++ [x]) wY 
                            | length z > 1  = error "Entry occured was not unique in y!"
                            | xE == yE      = proc xs (yL \\ z) (wL ++ [(xP,xE)]) wX wY
                            | xE <  yE      = proc xs (yL \\ z) (wL ++ [(xP,xE)]) wX (wY ++ [(xP,yE -xE)])
                            | otherwise     = proc xs (yL \\ z) (wL ++ [(xP,yE)]) (wX ++ [(xP,xE - yE)]) wY 
                            where z  = filter (\(p,_) -> xP == p) yL
                                  yE = snd $ head z

        proc _                  yL wL wX wY = (wL, wX, (wY ++ yL))
        ((nN, nH'), (dN, dH'))              = (simplePrep n, simplePrep d)
        nHq                                 = if hF then 1 else gcd nN dN -- if hyperFlag set, don't do non-hyper gcd
        dem (a, b, c)                       = (map expDemote a, map expDemote b, map expDemote c)
        (wL', wX', wY')                     = dem $ proc nH' dH' [] [] []
        gcd'                                = computeExpr cMultOpLevel (nHq     :wL')
        x'                                  = computeExpr cMultOpLevel ((nN/nHq):wX')
        y'                                  = computeExpr cMultOpLevel ((dN/nHq):wY')

--  Split into non-hyper and hyper list and "expPromote" the hyper list        
simplePrep :: Canon -> (Canon, [(Canon, Canon)])
simplePrep c = (product nN, map expPromote nH)
  where (nH, nN)  = partition cHyperExpr $ cGetFactors c

-- Promote to exponential form : e.g. Two examples(1 + 3 <^> 4) -> (1 + 3<^>4, 1) and 7 <^ (5 <^> 4) -> (7, 5 <^> 4)
expPromote :: Canon -> (Canon, Canon)
expPromote v     | cGetHyperOp v == cExpOpLevel = (head h, computeExpr cExpOpLevel (tail h))
                 | otherwise                    = (v, c1)
                 where h = cGetHyperList v 

expPromoteFull :: Canon -> Canon
expPromoteFull c | cGetHyperOp c > maxHyperOpDelveLevel = error "expPromoteFull: Can't perform this action.  Max hyper op at base level exceeded."
                 | otherwise                            = simpleHX cMultOpLevel newFactors
                 where (hE, nonHe) = partition cHyperExpr $ cGetFactors $ cQuasiCanonize c
                       prmNonHe :: [(Canon, Canon)]
                       prmNonHe    = map (\(p,e) -> (makeCanon p, e)) $ concat $ map cToGCR nonHe 
                       newFactors :: [Canon]
                       newFactors  = map (\(p,e) -> simpleHX cExpOpLevel [p,e]) $ 
                                     sortOn fst $ prmNonHe ++ (concat $ map (\c' -> map expPromote $ cGetFactors c') hE)                  

-- Demote a pair to an the canon itself or exponential hyper expression
expDemote :: (Canon, Canon) -> Canon
expDemote (p, e) = if e == c1 then p else computeExpr cExpOpLevel [p,e]

-- | cFactor : Factor simple terms from a sum.  If the flag is true, only factor by the gcd if the gcd is a hyper expression
cFactorSum :: Canon -> Bool -> Canon
cFactorSum c@(HX PoA hL _) hF | gcdL == c1 || (hF && not (cHyperExpr gcdL))
                                           = c -- return as is
                              | otherwise  = computeExpr cMultOpLevel ((cGetFactors gcdL) ++ [computeExpr cAddOpLevel (map (\a -> div a gcdL) hL)])
                              where gcdL = foldl1 cGCD hL
cFactorSum c               _  = c
-- To do: any additional poly factorizations

-- | cFactorHorizon: Good for polynomial-like expressions like: (1 + 3<^>4 + 3<^>5) <^ 3 - 1, where there's a mixture of "canonical" and hE exponents.
cFactorHorizon :: Canon -> Canon
cFactorHorizon c | gcdL == c1 || length hL' == 1 = c -- return as is 
                 | otherwise                     = computeExpr cMultOpLevel ((cGetFactors gcdL) ++ [simpleHX cAddOpLevel aL])
                 where gcdL   = foldl1 cGCD hL'
                       hL'    = map expPromoteFull $ cGetAddends $ fst $ cConvertToSum c
                       mL     = map (\a -> cCleanup $ div a gcdL) hL'
                       (b,nB) = partition cBare mL
                       sB     = sum b
                       aL     = if sB == 0 then nB else (nB ++ [sB])

{-
Cleanup / Hyperize / QuasiCanonize examples:
Run cCleanup which is cHyperize . cQuasiCanonize

Identity found as a result: (a <^> x) <^ (a <^> y) = (a <^> (y+1)) <^ (a <^> (y-1))

testsGood = [ -- Worked despite P3 bug
 (7 <^> (2<^2)) <^ 7 <^ (7 <<^>> 5), (2 <<^>> (7<^2 * 25303)) * (2 <<<^>>> (17 * 23 * 317)),
 (2 <<^>> (7<^2 * 25303)) * ((2 * 5) <<<^>>> (17 * 23 * 317)), 77 <<^>> 1239847 * 15 <<<<^>>>> 123947,
 77 <<^>> 1239847 * 15 <<<<^>>>> 123947 * 7, (77 <<^>> 1239847 * 15 <<<<^>>>> 123947 * 7) <^ (79 ~~^~~ 101),
 (77 <<^>> 1239847 * 15 <<<<^>>>> 123947 * 7) <^ (79 ~~^~~ 101), (1 + 3 <<^>> 7) <^> 5, (7 <<^>> 5) <^> 11, 
 (35 <^> 5) <^ (35 <^> 3), 30 ~~^~~ 5, 
 3 * 3 <<^>> 5 * 6 <^> 5,
 13 * (((3 + 5 <^> 7) <^> 4) <^> 5) <^> 7,
 (7 <^ (3 <<^>> 5)) * 7 <^> 4, (3 * 7 <^> 4) <^ 2, (28 <^ (3 <<^>> 5)) * 7 <^> 4, 
 (((7 * 11) <<^>> (7<^2 * 25303)) <^ (13 ~~^~~ 101)) * (((3 * 5) <<<<^>>>> (17 * 23 * 317)) <^ (7 ~~^~~ 103)),
 (77 <<^>> 1239847 * 15 <<<<^>>>> 123947 * 7<^2) <^ (7 ~~^~~ 101),
 (77 <<^>> 1239847 * 15 <<<<^>>>> 123947 * 7) <^ (7 ~~^~~ 101),
 (77 <<^>> 1239847 * 15 <<<<^>>>> 123947 * 7) <^ (7 <<^>> 101),
 10 <<^>> 1239847 * 10 <<<^>>> 123947, 14 <<^>> 1239847 * 10 <<<^>>> 123947,
 60 <^> 4, 60 ~~^~~ 5, 90 ~~^~~ 5, 
 7 <<^>> 7 * 2 <<<<^>>>> 7 * 3 <^> 1234234 * 5 ~~~~^~~~~ 19 ~~~~^~~~~ 23982315987 * ((11*13*19*23*37*41) <^> 19) <^ 3,
 75 <<^>> 11 * 45 <^> 5, 3 <^ 139478 * 9 <^> 6 * 27 <^> 77, 
 (17 <^> 102) <^ (17 <^> 100),(7 <^> 5) <^ (7 <^> 3)] -- -> (17 <^> 101) <^> 2,(7 <^> 4) <^ (7 <^> 4),

testHangDisplay0526Solved = [
  (1 + 3 <<^>> 7) *((7 <^> 4) <^> 5 <^> 7), 
  ((11 * 7 <<^>> 107) <<^>> 1239847 * 15 <<<<^>>>> 123947 * 7) <^ (7 <^> 101),
  (3 * 15 <<^>> 7 * 7 ~^~ 7) <^> 4 * 3 <<^>> 1897 * 5 ~^~ 237,
  (7 * (1 + 3 <<^>> 7) <^> 5) <<^>> 17 * (1 + 3 <<^>> 7) ~~~~^~~~~ (1 + 7 ~~^~~ 1239847230),
  (3 * 15 <<^>> 7 * 7 ~^~ 7) <^> 4 * 3 <<^>> 1897,
  (3 * 15 <<^>> 7 * 7 ~^~ 7) <^> 4 * 3 <<^>> 1897 * 3 <^> 237,
  (3 * 15 <<^>> 7 * 7 ~^~ 7) <^> 4 * 3 <<^>> 1897 * 3 ~^~ 237 * (cApplyHy (makeCanon 1001) [3,5] True),
  (3 * 15 <<^>> 7 * 7 ~^~ 7) <^> 4 * 3 <<^>> 1897 * 3 ~^~ 237 * (cApplyHy (makeCanon 1001) [7,5] True),
  ((11 * 7 <<^>> 107) <<^>> 1239847 * 15 <<<<^>>>> 123947 * 7) <^ (7 <^ 101),
  ((3 * ((3 * 5) <<^>> 7) * (7 ~^~ 7)) <^> (2<^2)) * (3 <<^>> (7 * 271)) * (3 ~^~ (3 * 79)) * (cApplyHy (7 * 11 * 13) [2<^3, 5] True), 
  (7 <<<^>>> 4) <<^>> 3 ] -- P3

testsQCHang0526Solved = [ 
 (7<^ 2 * (7 <^> 4) <<^>> 13) <<<^>>>19, 
 13 * ((7 <^> 4) <^> 5 <^> 7), 
 (7 <<^>> 3) <<^>> 3, 
 (7 <^> 4) <<^>> 3, 
 ((7 <<^>> (2<^2)) * (7 ~^~ (2<^2))) <<^>> 5, -- doing several comparisons
 (7 <<^>> 3) <<^>> 3, 
 (7 <<^>> 4) <<^>> 3, 
 (3 * 3 <<^>> 7) <^> 4,
 (30 <^> 7) ~~^~~ 5,
 (7 <<<^>>> 4) <<^>> 3, -- P3
 ((3<^>17*7 ~^~ 4)) <<^>> 5,   
 ((3*7 ~^~ 4)) <<^>> 5,
 13 <^ (11 <<^>> 4) *((7 <^> 4) <^> 5 <^> 7),
 13 <^ 4 *((7 <^> 4) <^> 5 <^> 7),   
 ((3*7 <^> 4)) <<^>> 5, 
 ((3 <<^>> 5) <^> 7) ~~^~~ 5,
 ((3 <^> 5) <<^>> 7) ~~^~~ 5,
 (3 * 15 <<^>> 7) <^> 4,
 (3 * 15 <<^>> 7 * 7 ~^~ 7) <^> 4,
 (4 <^> 7) ~~^~~ 5,
 (60 <^> 7) ~~^~~ 5, 
 (12 <^> 7) ~~^~~ 5 ]

-- Works, too but needs special functions  (1 + 17 ~~~~~^~~~~~ 1329847 + 37 ~~~|^|~~~ grahamsNumber) ~~~^~~~ 8951237

testsU_P3 = [ -- Does not map them back
 (77 <<^>> 1239847 * 15 <<<<^>>>> 123947 * 7) <^ (7 <^> 101),
 (539 <<^>> 1239847 * 15 <<<<^>>>> 123947 * 7) <^ (7 <^> 101)] 

Correctly doesn't convert:
13 <^> 3

Hangs:
3 ^ 3 * 6 <^> 4 -- Canonical issue
3 * 3 <<^>> 5 * 6 <^> 4 -- Canonical meeets Hyper expression issue
(12 * 28 <^> 5) <^> 7

Utility func for verifying:
v c = map hypMap $ map (\l -> (l !! 0, l !! 1)) $ map cGetHyperList $ cGetFactors $ cQuasiCanonize c

-}

