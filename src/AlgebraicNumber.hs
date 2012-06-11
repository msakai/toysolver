-- WIP

-- http://www.dpmms.cam.ac.uk/~wtg10/galois.html
module AlgebraicNumber where

import Data.Function
import qualified Data.IntSet as IS
import qualified Data.IntMap as IM
import qualified Data.Map as Map
import Data.Monoid
import Polynomial

-- 本当は根の区別をしないといけないけど、それはまだ理解できていない
newtype A = A{ unA :: Polynomial Rational }
  deriving (Show, Eq, Ord)

add :: A -> A -> A
add (A p1) (A p2) = A $ lift (+) p1 p2

sub :: A -> A -> A
sub (A p1) (A p2) = A $ lift (flip subtract) p1 p2

prod :: A -> A -> A
prod (A p1) (A p2) = A $ lift (*) p1 p2

lift :: (Polynomial Rational -> Polynomial Rational -> Polynomial Rational)
     -> Polynomial Rational -> Polynomial Rational -> Polynomial Rational
lift f p1 p2 = sum [constant c * var 0 ^ n | (n,c) <- zip [0..] coeffs]
  where
    a, b :: Polynomial Rational
    a = var 0
    b = var 1

    cs = iterate (\p -> reduce cmp (f_a_b * p) gbase) 1
      where
        f_a_b = f a b
        cmp = grlex
        gbase = buchberger cmp
                  [ eval (\_ -> a) $ mapCoeff constant p1
                  , eval (\_ -> b) $ mapCoeff constant p2
                  ]

    cs2 = take (fromInteger (deg p1 * deg p2 + 1)) $ zip [2..] cs

    es = Map.elems $ Map.fromListWith (+) $ do
      (n,xs) <- terms $ sum [var ln * cn | (ln,cn) <- cs2]
      let xs' = mmToList xs
          ys = mmFromList [(x,m) | (x,m) <- xs', var x == a || var x == b]
          zs = mmFromList [(x,m) | (x,m) <- xs', var x /= a && var x /= b]
      return (ys, fromMonomial (n,zs))

    coeffs = map (\l -> eval (\_ -> 1) $ reduce cmp2 (var l) gbase2) $ map fst cs2
      where
        cmp2 = grlex
        gbase2 = buchberger cmp2 es

-- √2
sqrt2 :: A
sqrt2 = A (x^2 - 2)
  where
    x = var 0

-- √3
sqrt3 :: A
sqrt3 = A (x^2 - 3)
  where
    x = var 0

-- √4
sqrt4 :: A
sqrt4 = A (x^2 - 4)
  where
    x = var 0

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