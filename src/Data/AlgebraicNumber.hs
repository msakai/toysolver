{-# LANGUAGE Rank2Types #-}

-- WIP

-- http://www.dpmms.cam.ac.uk/~wtg10/galois.html
module Data.AlgebraicNumber where

import Control.Exception (assert)
import Data.Function
import Data.List
import Data.Maybe
import qualified Data.IntSet as IS
import qualified Data.IntMap as IM
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Monoid

import Data.Polynomial
import Data.Polynomial.GBase
import qualified Data.Polynomial.Sturm as Sturm
import Data.Interval (Interval)
import qualified Data.Interval as Interval

type Var = Int

{--------------------------------------------------------------------
  Algebraic numbers

以下の代数的実数の場合にはスツルムの定理による根の分離で色々できているけど、
一般の代数的数の場合にどうすれば良いかはまだちゃんと理解できていない。
なので、一旦色々削除した。
--------------------------------------------------------------------}

{--------------------------------------------------------------------
  Algebraic reals
--------------------------------------------------------------------}

-- TODO: 多項式を因数分解して既約多項式にするようにしないと

data AReal = RealRoot (UPolynomial Integer) (Interval Rational)
  deriving Show

realRoots :: UPolynomial Rational -> [AReal]
realRoots p = [RealRoot p' i | i <- Sturm.separate p]
  where
    p' = toZ p

testRealRoots = (a+b, a*b, a < b, a==b, a > b)
  where
    x = var ()
    [a,b] = realRoots (x^2 - 2)

isZero :: AReal -> Bool
isZero (RealRoot p i) = 0 `Interval.member` i && 0 `isRootOf` p

instance Eq AReal where
  a == b = isZero (a - b)

instance Ord AReal where
  compare a b
    | isZero c = EQ
    | Sturm.numRoots p' ipos == 1 = GT
    | otherwise = assert (Sturm.numRoots p' ineg == 1) LT
    where
      c@(RealRoot p i) = a - b
      p' = mapCoeff fromInteger p
      ipos = Interval.intersection i (Interval.interval (Just (False,0)) Nothing)
      ineg = Interval.intersection i (Interval.interval Nothing (Just (False,0)))

instance Num AReal where
  RealRoot p1 i1 + RealRoot p2 i2 = RealRoot p3 i3
    where
      p3 = rootAdd p1 p2
      i3 = go i1 i2 (Sturm.separate p3')

      p1' = mapCoeff fromInteger p1
      p2' = mapCoeff fromInteger p2
      p3' = mapCoeff fromInteger p3

      go i1 i2 is3 =
        case [i5 | i3 <- is3, let i5 = Interval.intersection i3 i4, Sturm.numRoots p3' i5 > 0] of
          [] -> error "AReal.+: should not happen"
          [i5] -> i5
          is5 ->
            go (Sturm.narrow p1' i1 (Interval.size i1 / 2))
               (Sturm.narrow p2' i2 (Interval.size i2 / 2))
               [Sturm.narrow p3' i5 (Interval.size i5 / 2) | i5 <- is5]
        where
          i4 = i1 + i2

  RealRoot p1 i1 * RealRoot p2 i2 = RealRoot p3 i3
    where
      p3 = rootMul p1 p2
      i3 = go i1 i2 (Sturm.separate p3')

      p1' = mapCoeff fromInteger p1
      p2' = mapCoeff fromInteger p2
      p3' = mapCoeff fromInteger p3

      go i1 i2 is3 =
        case [i5 | i3 <- is3, let i5 = Interval.intersection i3 i4, Sturm.numRoots p3' i5 > 0] of
          [] -> error "AReal.*: should not happen"
          [i5] -> i5
          is5 ->
            go (Sturm.narrow p1' i1 (Interval.size i1 / 2))
               (Sturm.narrow p2' i2 (Interval.size i2 / 2))
               [Sturm.narrow p3' i5 (Interval.size i5 / 2) | i5 <- is5]
        where
          i4 = i1 * i2

  negate (RealRoot p i) = RealRoot (rootNegate p) (-i)

  abs a =
    case compare 0 a of
      EQ -> fromInteger 0
      LT -> a
      GT -> negate a

  signum a = fromInteger $
    case compare 0 a of
      EQ -> 0
      LT -> 1
      GT -> -1

  fromInteger i = RealRoot (x - constant i) (Interval.singleton (fromInteger i))
    where
      x = var ()

instance Fractional AReal where
  fromRational r = RealRoot (toZ (x - constant r)) (Interval.singleton r)
    where
      x = var ()

  recip a@(RealRoot p i)
    | isZero a  = error "AReal.recip: zero division"
    | otherwise = RealRoot (rootRecip p) (recip i)

toRational' :: AReal -> Rational -> Rational
toRational' (RealRoot p i) epsilon = Sturm.approx (mapCoeff toRational p) i epsilon

properFraction' :: Integral b => AReal -> (b, AReal)
properFraction' x =
  case compare x 0 of
    EQ -> (0, 0)
    GT -> (fromInteger floor_x, x - fromInteger floor_x)
    LT -> (fromInteger ceiling_x, x - fromInteger ceiling_x)
  where
    floor_x   = floor' x
    ceiling_x = ceiling' x

truncate' :: Integral b => AReal -> b
truncate' = fst . properFraction'

round' :: Integral b => AReal -> b
round' x = 
  case signum (abs r - 0.5) of
    -1 -> n
    0  -> if even n then n else m
    1  -> m
    _  -> error "round default defn: Bad value"
  where
    (n,r) = properFraction' x
    m = if r < 0 then n - 1 else n + 1

ceiling' :: Integral b => AReal -> b
ceiling' (RealRoot p i) =
  if Sturm.numRoots' chain (Interval.intersection i2 i3) > 1
    then fromInteger ceiling_lb
    else fromInteger ceiling_ub
  where
    chain = Sturm.sturmChain (mapCoeff fromInteger p)
    i2 = Sturm.narrow' chain i (1/2)
    Just (inLB, lb) = Interval.lowerBound i2
    Just (inUB, ub) = Interval.upperBound i2
    ceiling_lb = ceiling lb
    ceiling_ub = ceiling ub
    i3 = Interval.interval Nothing (Just (True, fromInteger ceiling_lb))

floor' :: Integral b => AReal -> b
floor' (RealRoot p i) =
  if Sturm.numRoots' chain (Interval.intersection i2 i3) > 1
    then fromInteger floor_ub
    else fromInteger floor_lb
  where
    chain = Sturm.sturmChain (mapCoeff fromInteger p)
    i2 = Sturm.narrow' chain i (1/2)
    Just (inLB, lb) = Interval.lowerBound i2
    Just (inUB, ub) = Interval.upperBound i2
    floor_lb = floor lb
    floor_ub = floor ub
    i3 = Interval.interval (Just (True, fromInteger floor_ub)) Nothing

-- 代数的数を係数とする多項式の根を、有理数係数多項式の根として表す
simpARealPoly :: UPolynomial AReal -> UPolynomial Integer
simpARealPoly p = rootSimpPoly (\(RealRoot q _) -> q) p

{--------------------------------------------------------------------
  Manipulation of polynomials
--------------------------------------------------------------------}

rootAdd :: UPolynomial Integer -> UPolynomial Integer -> UPolynomial Integer
rootAdd p1 p2 = lift2 (+) p1 p2

rootSub :: UPolynomial Integer -> UPolynomial Integer -> UPolynomial Integer
rootSub p1 p2 = lift2 (flip subtract) p1 p2

rootMul :: UPolynomial Integer -> UPolynomial Integer -> UPolynomial Integer
rootMul p1 p2 = lift2 (*) p1 p2

rootNegate :: UPolynomial Integer -> UPolynomial Integer
rootNegate p = fromTerms [(if (d - mmDegree xs) `mod` 2 == 0 then c else -c, xs) | (c, xs) <- terms p]
  where
    d = deg p

rootScale :: Rational -> UPolynomial Integer -> UPolynomial Integer
rootScale r p = toZ $ fromTerms [(r^(d - mmDegree xs) * fromIntegral c, xs) | (c, xs) <- terms p]
  where
    d = deg p

rootRecip :: UPolynomial Integer -> UPolynomial Integer
rootRecip p = fromTerms [(c, mmFromList [((), d - mmDegree xs)]) | (c, xs) <- terms p]
  where
    d = deg p

-- 代数的数を係数とする多項式の根を、有理数係数多項式の根として表す
rootSimpPoly :: (a -> UPolynomial Integer) -> UPolynomial a -> UPolynomial Integer
rootSimpPoly f p = toZ $ findPoly (var 0) ps
  where
    ys :: [(UPolynomial Integer, Var)]
    ys = zip (Set.toAscList $ Set.fromList [f c | (c, xs) <- terms p]) [1..]

    m :: Map.Map (UPolynomial Integer) Var
    m = Map.fromDistinctAscList ys

    p' :: Polynomial Rational Var
    p' = eval (\() -> var 0) (mapCoeff (\c -> var (m Map.! (f c))) p)

    ps :: [Polynomial Rational Var]
    ps = p' : [mapCoeff fromInteger $ mapVar (\() -> x) q | (q, x) <- ys]

lift2 :: (forall a. Num a => a -> a -> a)
      -> UPolynomial Integer -> UPolynomial Integer -> UPolynomial Integer
lift2 f p1 p2 = toZ $ findPoly f_a_b gbase
  where
    a, b :: Var
    a = 0
    b = 1

    f_a_b :: Polynomial Rational Var
    f_a_b = f (var a) (var b)

    gbase :: [Polynomial Rational Var]
    gbase = map (mapCoeff fromInteger) [ mapVar (\() -> a) p1, mapVar (\() -> b) p2 ]              

-- ps のもとで c を根とする多項式を求める
findPoly :: Polynomial Rational Var -> [Polynomial Rational Var] -> UPolynomial Rational
findPoly c ps = fromTerms [(coeff, mmFromList [((), n)]) | (n,coeff) <- zip [0..] coeffs]
  where  
    vn :: Var
    vn = if Set.null vs then 0 else Set.findMax vs + 1
      where
        vs = Set.fromList [x | p <- (c:ps), (_,xs) <- terms p, (x,_) <- mmToList xs]

    coeffs :: [Rational]
    coeffs = head $ catMaybes $ [isLinearlyDependent cs2 | cs2 <- inits cs]
      where
        cmp = grlex
        ps' = buchberger cmp ps
        cs  = iterate (\p -> reduce cmp (c * p) ps') 1

    isLinearlyDependent :: [Polynomial Rational Var] -> Maybe [Rational]
    isLinearlyDependent cs = if any (0/=) sol then Just sol else Nothing
      where
        cs2 = zip [vn..] cs
        sol = map (\(l,_) -> eval (\_ -> 1) $ reduce cmp2 (var l) gbase2) cs2
        cmp2   = grlex
        gbase2 = buchberger cmp2 es
        es = Map.elems $ Map.fromListWith (+) $ do
          (n,xs) <- terms $ sum [var ln * cn | (ln,cn) <- cs2]
          let xs' = mmToList xs
              ys = mmFromList [(x,m) | (x,m) <- xs', x < vn]
              zs = mmFromList [(x,m) | (x,m) <- xs', x >= vn]
          return (ys, fromMonomial (n,zs))

{--------------------------------------------------------------------
  Test cases
--------------------------------------------------------------------}

tests =
  [ test_rootAdd
  , test_rootSub
  , test_rootMul
  , test_rootNegate
  , test_rootNegate_2
  , test_rootNegate_3
  , test_rootScale
  , test_rootRecip
  , test_simpARealPoly
  , test_eq
  , test_eq_refl
  , test_diseq_1
  , test_diseq_2
  , test_cmp_1
  , test_cmp_2
  , test_cmp_3
  , test_cmp_4
  , test_floor_sqrt2
  , test_floor_neg_sqrt2
  , test_floor_1
  , test_floor_neg_1
  , test_ceiling_sqrt2
  , test_ceiling_neg_sqrt2
  , test_ceiling_1
  , test_ceiling_neg_1
  , test_round_sqrt2
  ]

test_rootAdd = abs valP <= 0.0001
  where
    x = var ()

    p :: UPolynomial Integer
    p = rootAdd (x^2 - 2) (x^2 - 3)

    valP :: Double
    valP = eval (\() -> sqrt 2 + sqrt 3) $ mapCoeff fromInteger p

-- bug?
test_rootAdd_2 = p
  where
    x = var ()    
    p :: UPolynomial Integer
    p = rootAdd (x^2 - 2) (x^6 + 6*x^3 - 2*x^2 + 9)

test_rootSub = abs valP <= 0.0001
  where
    x = var ()

    p :: UPolynomial Integer
    p = rootSub (x^2 - 2) (x^2 - 3)

    valP :: Double
    valP = eval (\() -> sqrt 2 - sqrt 3) $ mapCoeff fromInteger p

test_rootMul = abs valP <= 0.0001
  where
    x = var ()

    p :: UPolynomial Integer
    p = rootMul (x^2 - 2) (x^2 - 3)

    valP :: Double
    valP = eval (\() -> sqrt 2 * sqrt 3) $ mapCoeff fromInteger p

test_rootNegate = abs valP <= 0.0001
  where
    x = var ()

    p :: UPolynomial Integer
    p = rootNegate (x^3 - 3)

    valP :: Double
    valP = eval (\() -> - (3 ** (1/3))) $ mapCoeff fromInteger p

test_rootNegate_2 = rootNegate p == q
  where
    x :: UPolynomial Integer
    x = var ()
    p = x^3 - 3
    q = x^3 + 3

test_rootNegate_3 = rootNegate p == q
  where
    x :: UPolynomial Integer
    x = var ()
    p = (x-2)*(x-3)*(x-4)
    q = (x+2)*(x+3)*(x+4)

test_rootScale = rootScale 2 p == q
  where
    x :: UPolynomial Integer
    x = var ()
    p = (x-2)*(x-3)*(x-4)
    q = (x-4)*(x-6)*(x-8)

test_rootRecip = abs valP <= 0.0001
  where
    x = var ()

    p :: UPolynomial Integer
    p = rootRecip (x^3 - 3)

    valP :: Double
    valP = eval (\() -> 1 / (3 ** (1/3))) $ mapCoeff fromInteger p

test_eq = sqrt2*sqrt2 - 2 == 0

test_eq_refl = sqrt2 == sqrt2

test_diseq_1 = sqrt2 /= sqrt3

test_diseq_2 = sqrt2 /= neg_sqrt2

test_cmp_1 = 0 < sqrt2

test_cmp_2 = neg_sqrt2 < 0

test_cmp_3 = 0 < neg_sqrt2 * neg_sqrt2

test_cmp_4 = neg_sqrt2 * neg_sqrt2 * neg_sqrt2 < 0

test_floor_sqrt2 = floor' sqrt2 == 1

test_floor_neg_sqrt2 = floor' neg_sqrt2 == -2

test_floor_1 = floor' 1 == 1

test_floor_neg_1 = floor' (-1) == -1

test_ceiling_sqrt2 = ceiling' sqrt2 == 2

test_ceiling_neg_sqrt2 = ceiling' neg_sqrt2 == -1

test_ceiling_1 = ceiling' 1 == 1

test_ceiling_neg_1 = ceiling' (-1) == -1

test_round_sqrt2 = round' sqrt2 == 1

-- 期待値は Wolfram Alpha で x^3 - Sqrt[2]*x + 3 を調べて Real root の exact form で得た
test_simpARealPoly = simpARealPoly p == q
  where
    x :: forall k. (Num k, Eq k) => UPolynomial k
    x = var ()
    p = x^3 - constant sqrt2 * x + 3
    q = x^6 + 6*x^3 - 2*x^2 + 9

-- √2
sqrt2 :: AReal
[neg_sqrt2, sqrt2] = realRoots (x^2 - 2)
  where
    x = var ()

-- √3
sqrt3 :: AReal
[neg_sqrt3, sqrt3] = realRoots (x^2 - 3)
  where
    x = var ()
