{-# LANGUAGE Rank2Types #-}

-- WIP

-- http://www.dpmms.cam.ac.uk/~wtg10/galois.html
module Data.AlgebraicNumber where

import Data.Function
import Data.List
import Data.Maybe
import qualified Data.IntSet as IS
import qualified Data.IntMap as IM
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Monoid

import Data.Polynomial

type Var = Int

-- 本当は根の区別をしないといけないけど、それはまだ理解できていない
-- あと多項式を因数分解して最小多項式にするようにしないと
newtype A = Root (UPolynomial Integer)
  deriving (Show, Eq)

instance Num A where
  (+) = add
  (-) = sub
  (*) = prod
  negate = negate'
  abs    = undefined
  signum = undefined
  fromInteger i = Root (var () - constant i) 

instance Fractional A where
  recip = recip'
  fromRational r = Root $ toZ (var () - constant r)

add :: A -> A -> A
add (Root p1) (Root p2) = Root $ lift2 (+) p1 p2

sub :: A -> A -> A
sub (Root p1) (Root p2) = Root $ lift2 (flip subtract) p1 p2

prod :: A -> A -> A
prod (Root p1) (Root p2) = Root $ lift2 (*) p1 p2

lift2 :: (forall a. Num a => a -> a -> a)
      -> UPolynomial Integer -> UPolynomial Integer -> UPolynomial Integer
lift2 f p1 p2 = toZ $ findPoly f_a_b gbase 2
  where
    a, b :: Var
    a = 0
    b = 1

    f_a_b :: Polynomial Rational Var
    f_a_b = f (var a) (var b)

    gbase :: [Polynomial Rational Var]
    gbase = map (mapCoeff fromInteger) [ mapVar (\() -> a) p1, mapVar (\() -> b) p2 ]              

findPoly :: Polynomial Rational Var -> [Polynomial Rational Var] -> Var -> UPolynomial Rational
findPoly c ps vn = fromTerms [(coeff, mmFromList [((), n)]) | (n,coeff) <- zip [0..] coeffs]
  where
    coeffs = head $ catMaybes $ [isLinearlyDependent cs2 | cs2 <- inits cs]
      where
        ps' = buchberger grlex ps
        cs  = iterate (\p -> reduce grlex (c * p) ps') 1

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

test_findPoly_1 = abs valP <= 0.0001
  where
    a = var 0
    b = var 1

    p :: Polynomial Rational ()
    p = findPoly (a+b) [a^2 - 2, b^2 - 3] 2

    valX :: Double
    valX = sqrt 2 + sqrt 3

    valP :: Double
    valP = eval (\() -> valX) $ mapCoeff fromRational p

test_findPoly_2 = abs valP <= 0.0001
  where
    a = var 0
    b = var 1

    p :: Polynomial Rational ()
    p = findPoly (a*b) [a^2 - 2, b^2 - 3] 2

    valX :: Double
    valX = sqrt 2 * sqrt 3

    valP :: Double
    valP = eval (\() -> valX) $ mapCoeff fromRational p

negate' :: A -> A
negate' (Root p) = Root q
  where
    q = fromTerms [(if mmDegree xs `mod` 2 == 0 then c else -c, xs) | (c, xs) <- terms p]

recip' :: A -> A
recip' (Root p) = Root q
  where
    d = deg p
    q = fromTerms [(c, mmFromList [((), d - mmDegree xs)]) | (c, xs) <- terms p]

-- 代数的数を係数とする多項式の根を、有理数係数多項式の根として表す
simpPoly :: UPolynomial A -> UPolynomial Rational
simpPoly p = findPoly (var 0) ps (Set.size coeffsPoly + 1)
  where
    coeffsPoly :: Set.Set (UPolynomial Integer)
    coeffsPoly = Set.fromList [q | (Root q, xs) <- terms p]

    ys :: [(UPolynomial Integer, Var)]
    ys = zip (Set.toAscList coeffsPoly) [1 .. Set.size coeffsPoly]

    m :: Map.Map (UPolynomial Integer) Var
    m = Map.fromAscList ys

    p' :: Polynomial Rational Var
    p' = eval (\() -> var 0) (mapCoeff (\(Root q) -> var (m Map.! q)) p)

    ps :: [Polynomial Rational Var]
    ps = p' : [mapCoeff fromInteger $ mapVar (\() -> x) q | (q, x) <- ys]

-- 期待値は Wolfram Alpha で x^3 - Sqrt[2]*x + 3 を調べて Real root の exact form で得た
test_simpPoly = simpPoly p == q
  where
    x :: forall k. (Num k, Eq k) => UPolynomial k
    x = var ()
    p = x^3 - constant sqrt2 * x + 3
    q = x^6 + 6*x^3 - 2*x^2 + 9

-- √2
sqrt2 :: A
sqrt2 = Root (x^2 - 2)
  where
    x = var ()

-- √3
sqrt3 :: A
sqrt3 = Root (x^2 - 3)
  where
    x = var ()

-- √4
sqrt4 :: A
sqrt4 = Root (x^2 - 4)
  where
    x = var ()

test_add_sqrt2_sqrt2 = add sqrt2 sqrt2
test_add_sqrt2_sqrt3 = add sqrt2 sqrt3
test_add_sqrt2_sqrt4 = add sqrt2 sqrt4
test_add_sqrt3_sqrt3 = add sqrt3 sqrt3
test_add_sqrt3_sqrt4 = add sqrt3 sqrt4
test_add_sqrt4_sqrt4 = add sqrt4 sqrt4

test_sub_sqrt2_sqrt2 = sub sqrt2 sqrt2
test_sub_sqrt2_sqrt3 = sub sqrt2 sqrt3
test_sub_sqrt2_sqrt4 = sub sqrt2 sqrt4
test_sub_sqrt3_sqrt3 = sub sqrt3 sqrt3
test_sub_sqrt3_sqrt4 = sub sqrt3 sqrt4
test_sub_sqrt4_sqrt4 = sub sqrt4 sqrt4

test_negate' = negate' (Root p) == Root q
  where
    x = var ()
    p =   x^3 - 3
    q = - x^3 - 3
