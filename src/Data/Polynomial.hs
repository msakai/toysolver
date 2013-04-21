{-# LANGUAGE ScopedTypeVariables, TypeFamilies #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Polynomial
-- Copyright   :  (c) Masahiro Sakai 2012-2013
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  non-portable (ScopedTypeVariables, TypeFamilies)
--
-- Polynomials
--
-- References:
--
-- * Monomial order <http://en.wikipedia.org/wiki/Monomial_order>
-- 
-- * Gröbner basis <http://en.wikipedia.org/wiki/Gr%C3%B6bner_basis>
--
-- * グレブナー基底 <http://d.hatena.ne.jp/keyword/%A5%B0%A5%EC%A5%D6%A5%CA%A1%BC%B4%F0%C4%EC>
--
-- * Gröbner Bases and Buchberger’s Algorithm <http://math.rice.edu/~cbruun/vigre/vigreHW6.pdf>
--
-- * Polynomial class for Ruby <http://www.math.kobe-u.ac.jp/~kodama/tips-RubyPoly.html>
--
-- * Docon <http://www.haskell.org/docon/>
--
-- * constructive-algebra package <http://hackage.haskell.org/package/constructive-algebra>
-- 
-----------------------------------------------------------------------------
module Data.Polynomial
  (
  -- * Polynomial type
    Polynomial
  , UPolynomial
  , X (..)

  -- * Conversion
  , var
  , constant
  , terms
  , fromTerms
  , coeffMap
  , fromCoeffMap
  , fromMonomial

  -- * Query
  , leadingTerm
  , deg
  , coeff
  , lookupCoeff
  , variables

  -- * Operations
  , ContPP (..)
  , deriv
  , integral
  , eval
  , evalM
  , subst
  , isRootOf
  , mapVar
  , mapCoeff
  , associatedMonicPolynomial
  , toUPolynomialOf
  , polyDiv
  , polyMod
  , polyDivMod
  , polyGCD
  , polyLCM
  , polyMDivMod
  , reduce

  -- * Monomial
  , Monomial
  , monomialDegree
  , monomialProd
  , monomialDivisible
  , monomialDiv
  , monomialDeriv
  , monomialIntegral

  -- * Monic monomial
  , MonicMonomial
  , mmVar
  , mmOne
  , mmFromList
  , mmFromMap
  , mmFromIntMap
  , mmToList
  , mmToMap
  , mmToIntMap
  , mmDegree
  , mmProd
  , mmDivisible
  , mmDiv
  , mmDeriv
  , mmIntegral
  , mmLCM
  , mmGCD
  , mmMapVar

  -- * Monomial order
  , MonomialOrder
  , lex
  , revlex
  , grlex
  , grevlex

  -- * Pretty Printing
  , renderWith
  , PrettyCoeff (..)
  , PrettyVar (..)
  ) where

import Prelude hiding (lex)
import Control.Exception (assert)
import Control.Monad
import Data.Function
import Data.List
import Data.Monoid
import Data.Ratio
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Data.IntMap as IM
import Data.VectorSpace
import qualified Text.PrettyPrint.HughesPJClass as PP
import Text.PrettyPrint.HughesPJClass (Doc, PrettyLevel, Pretty (..), prettyParen)

{--------------------------------------------------------------------
  Polynomial type
--------------------------------------------------------------------}

-- | Polynomial over commutative ring r
newtype Polynomial k v = Polynomial{ coeffMap :: Map.Map (MonicMonomial v) k }
  deriving (Eq, Ord)

data X = X
  deriving (Eq, Ord, Bounded, Enum, Show)

-- | Univalent polynomials over commutative ring r
type UPolynomial r = Polynomial r X

instance (Eq k, Num k, Ord v, Show v) => Num (Polynomial k v) where
  Polynomial m1 + Polynomial m2 = normalize $ Polynomial $ Map.unionWith (+) m1 m2
  a * b
    | Just c <- asConstant a = scale c b
    | Just c <- asConstant b = scale c a
  Polynomial m1 * Polynomial m2 = normalize $ Polynomial $ Map.fromListWith (+)
      [ (xs1 `mmProd` xs2, c1*c2)
      | (xs1,c1) <- Map.toList m1, (xs2,c2) <- Map.toList m2
      ]
  negate (Polynomial m) = Polynomial $ Map.map negate m
  abs x = x    -- OK?
  signum x = 1 -- OK?
  fromInteger x = constant (fromInteger x)

instance (Eq k, Num k, Ord v, Show v) => AdditiveGroup (Polynomial k v) where
  p ^+^ q = p + q
  zeroV   = 0
  negateV = negate

instance (Eq k, Num k, Ord v, Show v) => VectorSpace (Polynomial k v) where
  type Scalar (Polynomial k v) = k
  k *^ p = scale k p

instance (Show v, Ord v, Show k) => Show (Polynomial k v) where
  showsPrec d p  = showParen (d > 10) $
    showString "fromTerms " . shows (terms p)

normalize :: (Eq k, Num k, Ord v) => Polynomial k v -> Polynomial k v
normalize (Polynomial m) = Polynomial (Map.filter (0/=) m)

asConstant :: Num k => Polynomial k v -> Maybe k
asConstant p =
  case terms p of
    [] -> Just 0
    [(c,xs)] | Map.null (mmToMap xs) -> Just c
    _ -> Nothing

scale :: (Eq k, Num k, Ord v, Show v) => k -> Polynomial k v -> Polynomial k v
scale a (Polynomial m) = normalize $ Polynomial (Map.map (a*) m)

-- | construct a polynomial from a variable
var :: (Eq k, Num k, Ord v) => v -> Polynomial k v
var x = fromMonomial (1, mmVar x)

-- | construct a polynomial from a constant
constant :: (Eq k, Num k, Ord v) => k -> Polynomial k v
constant c = fromMonomial (c, mmOne)

-- | construct a polynomial from a list of monomials
fromTerms :: (Eq k, Num k, Ord v) => [Monomial k v] -> Polynomial k v
fromTerms = normalize . Polynomial . Map.fromListWith (+) . map (\(c,xs) -> (xs,c))

fromCoeffMap :: (Eq k, Num k, Ord v) => Map.Map (MonicMonomial v) k -> Polynomial k v
fromCoeffMap m = normalize $ Polynomial m

-- | construct a polynomial from a monomial
fromMonomial :: (Eq k, Num k, Ord v) => Monomial k v -> Polynomial k v
fromMonomial (c,xs) = normalize $ Polynomial $ Map.singleton xs c

-- | list of monomials
terms :: Polynomial k v -> [Monomial k v]
terms (Polynomial m) = [(c,xs) | (xs,c) <- Map.toList m]

-- | leading term with respect to a given monomial order
leadingTerm :: (Eq k, Num k, Ord v) => MonomialOrder v -> Polynomial k v -> Monomial k v
leadingTerm cmp p =
  case terms p of
    [] -> (0, mmOne) -- should be error?
    ms -> maximumBy (cmp `on` snd) ms

-- | total degree of a given polynomial
deg :: Polynomial k v -> Integer
deg = maximum . (0:) . map monomialDegree . terms

coeff :: (Num k, Ord v) => MonicMonomial v -> Polynomial k v -> k
coeff xs (Polynomial m) = Map.findWithDefault 0 xs m

lookupCoeff :: Ord v => MonicMonomial v -> Polynomial k v -> Maybe k
lookupCoeff xs (Polynomial m) = Map.lookup xs m

variables :: Ord v => Polynomial k v -> Set.Set v
variables p = Set.unions $ [Map.keysSet (mmToMap mm) | (_, mm) <- terms p]  

class ContPP k where
  -- | Content of a polynomial  
  cont :: (Ord v, Show v) => Polynomial k v -> k

  -- | Primitive part of a polynomial
  pp :: (Ord v, Show v) => Polynomial k v -> Polynomial k v

instance ContPP Integer where
  cont 0 = 1
  cont p = foldl1' gcd [abs c | (c,_) <- terms p]

  pp p = mapCoeff f p
    where
      c = cont p
      f x = assert (x `mod` c == 0) $ x `div` c

instance Integral r => ContPP (Ratio r) where
  {-# SPECIALIZE instance ContPP (Ratio Integer) #-}

  cont 0 = 1
  cont p = foldl1' gcd ns % foldl' lcm 1 ds
    where
      ns = [abs (numerator c) | (c,_) <- terms p]
      ds = [denominator c     | (c,_) <- terms p]  

  pp p = mapCoeff (/ c) p
    where
      c = cont p

-- | Formal derivative of polynomials
deriv :: (Eq k, Num k, Ord v, Show v) => Polynomial k v -> v -> Polynomial k v
deriv p x = sum [fromMonomial (monomialDeriv m x) | m <- terms p]

-- | Formal integral of polynomials
integral :: (Eq k, Fractional k, Ord v, Show v) => Polynomial k v -> v -> Polynomial k v
integral p x = sum [fromMonomial (monomialIntegral m x) | m <- terms p]

-- | Evaluation
eval :: (Num k, Ord v) => (v -> k) -> Polynomial k v -> k
eval env p = sum [c * product [(env x) ^ e | (x,e) <- mmToList xs] | (c,xs) <- terms p]

-- | Monadic evaluation
evalM :: (Num k, Ord v, Monad m) => (v -> m k) -> Polynomial k v -> m k
evalM env p = do
  liftM sum $ forM (terms p) $ \(c,xs) -> do
    rs <- mapM (\(x,e) -> liftM (^ e) (env x)) (mmToList xs)
    return (c * product rs)

-- | Substitution or bind
subst :: (Num k, Eq k, Ord v1, Ord v2, Show v2) => Polynomial k v1 -> (v1 -> Polynomial k v2) -> Polynomial k v2
subst p s =
  sum [constant c * product [(s x)^e | (x,e) <- mmToList xs] | (c, xs) <- terms p]

isRootOf :: (Num k, Eq k) => k -> UPolynomial k -> Bool
isRootOf x p = eval (\_ -> x) p == 0

mapVar :: (Num k, Eq k, Ord v1, Ord v2) => (v1 -> v2) -> Polynomial k v1 -> Polynomial k v2
mapVar f (Polynomial m) = normalize $ Polynomial $ Map.mapKeysWith (+) (mmMapVar f) m

mapCoeff :: (Eq k1, Num k1, Ord v) => (k -> k1) -> Polynomial k v -> Polynomial k1 v
mapCoeff f (Polynomial m) = normalize $ Polynomial $ Map.map f m

associatedMonicPolynomial :: (Eq r, Ord v, Fractional r) => MonomialOrder v -> Polynomial r v -> Polynomial r v
associatedMonicPolynomial cmp p
  | c == 0 = p
  | otherwise = mapCoeff (/c) p
  where
    (c,_) = leadingTerm cmp p

toUPolynomialOf :: (Eq k, Ord k, Num k, Ord v, Show v) => Polynomial k v -> v -> UPolynomial (Polynomial k v)
toUPolynomialOf p v = fromTerms $ do
  (c,mm) <- terms p
  let m = mmToMap mm
  return ( fromTerms [(c, mmFromMap (Map.delete v m))]
         , mmFromList [(X, Map.findWithDefault 0 v m)]
         )

-- | Multivariate division algorithm
polyMDivMod
  :: forall k v. (Eq k, Fractional k, Ord v, Show v)
  => MonomialOrder v -> Polynomial k v -> [Polynomial k v] -> ([Polynomial k v], Polynomial k v)
polyMDivMod cmp p fs = go IM.empty p
  where
    ls = [(leadingTerm cmp f, f) | f <- fs]

    go :: IM.IntMap (Polynomial k v) -> Polynomial k v -> ([Polynomial k v], Polynomial k v)
    go qs g =
      case xs of
        [] -> ([IM.findWithDefault 0 i qs | i <- [0 .. length fs - 1]], g)
        (i, b, g') : _ -> go (IM.insertWith (+) i b qs) g'
      where
        ms = sortBy (flip cmp `on` snd) (terms g)
        xs = do
          (i,(a,f)) <- zip [0..] ls
          h <- ms
          guard $ monomialDivisible h a
          let b = fromMonomial $ monomialDiv h a
          return (i, b, g - b * f)

-- | Multivariate division algorithm
reduce
  :: (Eq k, Fractional k, Ord v, Show v)
  => MonomialOrder v -> Polynomial k v -> [Polynomial k v] -> Polynomial k v
reduce cmp p fs = go p
  where
    ls = [(leadingTerm cmp f, f) | f <- fs]
    go g = if null xs then g else go (head xs)
      where
        ms = sortBy (flip cmp `on` snd) (terms g)
        xs = do
          (a,f) <- ls
          h <- ms
          guard $ monomialDivisible h a
          return (g - fromMonomial (monomialDiv h a) * f)

{--------------------------------------------------------------------
  Pretty printing
--------------------------------------------------------------------}

instance (Ord k, Num k, Ord v, PrettyCoeff k, PrettyVar v) => Pretty (Polynomial k v) where
  pPrintPrec = renderWith pPrintVar

renderWith
  :: (Ord k, Num k, Ord v, PrettyCoeff k)
  => (PrettyLevel -> Rational -> v -> Doc)
  -> PrettyLevel -> Rational -> (Polynomial k v) -> Doc
renderWith rv lv prec p =
    case sortBy (flip grlex `on` snd) $ terms p of
      [] -> PP.int 0
      [t] -> renderLeadingTerm prec t
      t:ts ->
        prettyParen (prec > addPrec) $
          PP.hcat (renderLeadingTerm addPrec t : map renderTrailingTerm ts)
    where
      renderLeadingTerm prec (c,xs) =
        if isNegativeCoeff c
        then prettyParen (prec > addPrec) $
               PP.char '-' <> renderMonomial (addPrec+1) (-c) xs
        else renderMonomial prec c xs

      renderTrailingTerm (c,xs) =
        if isNegativeCoeff c
        then PP.space <> PP.char '-' <> PP.space <> renderMonomial (addPrec+1) (-c) xs
        else PP.space <> PP.char '+' <> PP.space <> renderMonomial (addPrec+1) c xs

      renderMonomial prec c xs
        | len == 0  = pPrintCoeff lv (appPrec+1) c
          -- intentionally specify (appPrec+1) to parenthesize any composite expression
        | len == 1 && c == 1 = renderPow prec $ head (mmToList xs)
        | otherwise =
            prettyParen (prec > mulPrec) $
              PP.hcat $ intersperse (PP.char '*') fs
          where
            len = length $ mmToList xs
            fs  = [pPrintCoeff lv (appPrec+1) c | c /= 1] ++ [renderPow (mulPrec+1) p | p <- mmToList xs]
            -- intentionally specify (appPrec+1) to parenthesize any composite expression

      renderPow prec (x,1) = rv lv prec x
      renderPow prec (x,n) =
        prettyParen (prec > expPrec) $
          rv lv (expPrec+1) x <> PP.char '^' <> PP.integer n

class PrettyCoeff a where
  pPrintCoeff :: PrettyLevel -> Rational -> a -> Doc
  isNegativeCoeff :: a -> Bool
  isNegativeCoeff _ = False

instance PrettyCoeff Integer where
  pPrintCoeff = pPrintPrec
  isNegativeCoeff = (0>)

instance (PrettyCoeff a, Integral a) => PrettyCoeff (Ratio a) where
  pPrintCoeff lv p r
    | denominator r == 1 = pPrintCoeff lv p (numerator r)
    | otherwise = 
        prettyParen (p > ratPrec) $
          pPrintCoeff lv (ratPrec+1) (numerator r) <>
          PP.char '/' <>
          pPrintCoeff lv (ratPrec+1) (denominator r)
  isNegativeCoeff x = isNegativeCoeff (numerator x)

instance (Num c, Ord c, PrettyCoeff c, Ord v, PrettyVar v) => PrettyCoeff (Polynomial c v) where
  pPrintCoeff = pPrintPrec

class PrettyVar a where
  pPrintVar :: PrettyLevel -> Rational -> a -> Doc

instance PrettyVar Int where
  pPrintVar _ _ n = PP.char 'x' <> PP.int n

instance PrettyVar X where
  pPrintVar _ _ X = PP.char 'x'

addPrec, mulPrec, ratPrec, expPrec :: Rational
addPrec = 6 -- Precedence of '+'
mulPrec = 7 -- Precedence of '*'
ratPrec = 7 -- Precedence of '/'
expPrec = 8 -- Precedence of '^'
appPrec = 10 -- Precedence of function application

{--------------------------------------------------------------------
  Univalent polynomials
--------------------------------------------------------------------}

-- | division of univalent polynomials
polyDiv :: (Eq k, Fractional k) => UPolynomial k -> UPolynomial k -> UPolynomial k
polyDiv f1 f2 = fst (polyDivMod f1 f2)

-- | division of univalent polynomials
polyMod :: (Eq k, Fractional k) => UPolynomial k -> UPolynomial k -> UPolynomial k
polyMod f1 f2 = snd (polyDivMod f1 f2)

-- | division of univalent polynomials
polyDivMod :: (Eq k, Fractional k) => UPolynomial k -> UPolynomial k -> (UPolynomial k, UPolynomial k)
polyDivMod f1 f2 = go f1
  where
    m2 = leadingTerm lex f2
    go 0 = (0,0)
    go f1
      | m1 `monomialDivisible` m2 =
          case go (f1 - fromMonomial (m1 `monomialDiv` m2) * f2) of
            (q,r) -> (q + fromMonomial (m1 `monomialDiv` m2), r)
      | otherwise = (0, f1)
      where
        m1 = leadingTerm lex f1

-- | GCD of univalent polynomials
polyGCD :: (Eq k, Fractional k) => UPolynomial k -> UPolynomial k -> UPolynomial k
polyGCD f1 0  = associatedMonicPolynomial grlex f1
polyGCD f1 f2 = polyGCD f2 (f1 `polyMod` f2)

-- | LCM of univalent polynomials
polyLCM :: (Eq k, Fractional k) => UPolynomial k -> UPolynomial k -> UPolynomial k
polyLCM _ 0 = 0
polyLCM 0 _ = 0
polyLCM f1 f2 = associatedMonicPolynomial grlex $ (f1 `polyMod` (polyGCD f1 f2)) * f2

{--------------------------------------------------------------------
  Monomial
--------------------------------------------------------------------}

type Monomial k v = (k, MonicMonomial v)

monomialDegree :: Monomial k v -> Integer
monomialDegree (_,xs) = mmDegree xs

monomialProd :: (Num k, Ord v) => Monomial k v -> Monomial k v -> Monomial k v
monomialProd (c1,xs1) (c2,xs2) = (c1*c2, xs1 `mmProd` xs2)

monomialDivisible :: (Fractional k, Ord v) => Monomial k v -> Monomial k v -> Bool
monomialDivisible (c1,xs1) (c2,xs2) = mmDivisible xs1 xs2

monomialDiv :: (Fractional k, Ord v) => Monomial k v -> Monomial k v -> Monomial k v
monomialDiv (c1,xs1) (c2,xs2) = (c1 / c2, xs1 `mmDiv` xs2)

monomialDeriv :: (Eq k, Num k, Ord v) => Monomial k v -> v -> Monomial k v
monomialDeriv (c,xs) x =
  case mmDeriv xs x of
    (s,ys) -> (c * fromIntegral s, ys)

monomialIntegral :: (Eq k, Fractional k, Ord v) => Monomial k v -> v -> Monomial k v
monomialIntegral (c,xs) x =
  case mmIntegral xs x of
    (s,ys) -> (c * fromRational s, ys)

{--------------------------------------------------------------------
  Monic Monomial
--------------------------------------------------------------------}

-- 本当は変数の型に応じて type family で表現を変えたい

-- | Monic monomials
newtype MonicMonomial v = MonicMonomial{ mmToMap :: Map.Map v Integer }
  deriving (Eq, Ord)

instance (Ord v, Show v) => Show (MonicMonomial v) where
  showsPrec d m  = showParen (d > 10) $
    showString "mmFromList " . shows (mmToList m)

mmDegree :: MonicMonomial v -> Integer
mmDegree (MonicMonomial m) = sum $ Map.elems m

mmVar :: Ord v => v -> MonicMonomial v
mmVar x = MonicMonomial $ Map.singleton x 1

mmOne :: MonicMonomial v
mmOne = MonicMonomial $ Map.empty

mmFromList :: Ord v => [(v, Integer)] -> MonicMonomial v
mmFromList xs
  | any (\(x,e) -> 0>e) xs = error "mmFromList: negative exponent"
  | otherwise = MonicMonomial $ Map.fromListWith (+) [(x,e) | (x,e) <- xs, e > 0]

mmFromMap :: Ord v => Map.Map v Integer -> MonicMonomial v
mmFromMap m
  | any (\(x,e) -> 0>e) (Map.toList m) = error "mmFromFromMap: negative exponent"
  | otherwise = MonicMonomial $ Map.filter (>0) m

mmFromIntMap :: IM.IntMap Integer -> MonicMonomial Int
mmFromIntMap = mmFromMap . Map.fromDistinctAscList . IM.toAscList

mmToList :: Ord v => MonicMonomial v -> [(v, Integer)]
mmToList (MonicMonomial m) = Map.toAscList m

mmToIntMap :: MonicMonomial Int -> IM.IntMap Integer
mmToIntMap (MonicMonomial m) = IM.fromDistinctAscList $ Map.toAscList m

mmProd :: Ord v => MonicMonomial v -> MonicMonomial v -> MonicMonomial v
mmProd (MonicMonomial xs1) (MonicMonomial xs2) = MonicMonomial $ Map.unionWith (+) xs1 xs2

mmDivisible :: Ord v => MonicMonomial v -> MonicMonomial v -> Bool
mmDivisible (MonicMonomial xs1) (MonicMonomial xs2) = Map.isSubmapOfBy (<=) xs2 xs1

mmDiv :: Ord v => MonicMonomial v -> MonicMonomial v -> MonicMonomial v
mmDiv (MonicMonomial xs1) (MonicMonomial xs2) = MonicMonomial $ Map.differenceWith f xs1 xs2
  where
    f m n
      | m <= n    = Nothing
      | otherwise = Just (m - n)

mmDeriv :: Ord v => MonicMonomial v -> v -> (Integer, MonicMonomial v)
mmDeriv (MonicMonomial xs) x
  | n==0      = (0, mmOne)
  | otherwise = (n, MonicMonomial $ Map.update f x xs)
  where
    n = Map.findWithDefault 0 x xs
    f m
      | m <= 1    = Nothing
      | otherwise = Just $! m - 1

mmIntegral :: Ord v => MonicMonomial v -> v -> (Rational, MonicMonomial v)
mmIntegral (MonicMonomial xs) x =
  (1 % fromIntegral (n + 1), MonicMonomial $ Map.insert x (n+1) xs)
  where
    n = Map.findWithDefault 0 x xs

mmLCM :: Ord v => MonicMonomial v -> MonicMonomial v -> MonicMonomial v
mmLCM (MonicMonomial m1) (MonicMonomial m2) = MonicMonomial $ Map.unionWith max m1 m2

mmGCD :: Ord v => MonicMonomial v -> MonicMonomial v -> MonicMonomial v
mmGCD (MonicMonomial m1) (MonicMonomial m2) = MonicMonomial $ Map.intersectionWith min m1 m2

mmMapVar :: (Ord v1, Ord v2) => (v1 -> v2) -> MonicMonomial v1 -> MonicMonomial v2
mmMapVar f (MonicMonomial m) = MonicMonomial $ Map.mapKeysWith (+) f m

{--------------------------------------------------------------------
  Monomial Order
--------------------------------------------------------------------}

type MonomialOrder v = MonicMonomial v -> MonicMonomial v -> Ordering

-- | Lexicographic order
lex :: Ord v => MonomialOrder v
lex xs1 xs2 = go (mmToList xs1) (mmToList xs2)
  where
    go [] [] = EQ
    go [] _  = LT -- = cmpare 0 n2
    go _ []  = GT -- = cmpare n1 0
    go ((x1,n1):xs1) ((x2,n2):xs2) =
      case compare x1 x2 of
        LT -> GT -- = compare n1 0
        GT -> LT -- = compare 0 n2
        EQ -> compare n1 n2 `mappend` go xs1 xs2

-- | Reverse lexicographic order
-- Note that revlex is NOT a monomial order.
revlex :: Ord v => MonicMonomial v -> MonicMonomial v -> Ordering
revlex xs1 xs2 = go (reverse (mmToList xs1)) (reverse (mmToList xs2))
  where
    go [] [] = EQ
    go [] _  = GT -- = cmp 0 n2
    go _ []  = LT -- = cmp n1 0
    go ((x1,n1):xs1) ((x2,n2):xs2) =
      case compare x1 x2 of
        LT -> GT -- = cmp 0 n2
        GT -> LT -- = cmp n1 0
        EQ -> cmp n1 n2 `mappend` go xs1 xs2
    cmp n1 n2 = compare n2 n1

-- | graded lexicographic order
grlex :: Ord v => MonomialOrder v
grlex = (compare `on` mmDegree) `mappend` lex

-- | graded reverse lexicographic order
grevlex :: Ord v => MonomialOrder v
grevlex = (compare `on` mmDegree) `mappend` revlex
