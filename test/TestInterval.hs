{-# LANGUAGE TemplateHaskell #-}

import Control.Monad
import Data.Maybe
import Data.Ratio
import Test.HUnit hiding (Test)
import Test.QuickCheck
import Test.Framework (Test, defaultMain, testGroup)
import Test.Framework.TH
import Test.Framework.Providers.HUnit
import Test.Framework.Providers.QuickCheck2

import Data.Interval (Interval, EndPoint (..), (<=..<=), (<=..<), (<..<=), (<..<), (<!), (<=!), (==!), (>=!), (>!), (<?), (<=?), (==?), (>=?), (>?))
import qualified Data.Interval as Interval

{--------------------------------------------------------------------
  empty
--------------------------------------------------------------------}

prop_empty_is_bottom =
  forAll intervals $ \a ->
    Interval.isSubsetOf Interval.empty a

prop_null_empty =
  forAll intervals $ \a ->
    Interval.null a == (a == Interval.empty)

case_null_empty =
  Interval.null (Interval.empty :: Interval Rational) @?= True

{--------------------------------------------------------------------
  whole
--------------------------------------------------------------------}

prop_whole_is_top =
  forAll intervals $ \a ->
    Interval.isSubsetOf a Interval.whole

case_nonnull_top =
  Interval.null (Interval.whole :: Interval Rational) @?= False

{--------------------------------------------------------------------
  singleton
--------------------------------------------------------------------}

prop_singleton_member =
  forAll arbitrary $ \r ->
    Interval.member (r::Rational) (Interval.singleton r)

prop_singleton_member_intersection =
  forAll intervals $ \a ->
  forAll arbitrary $ \r ->
    let b = Interval.singleton r
    in Interval.member (r::Rational) a
       ==> Interval.intersection a b == b

prop_singleton_nonnull =
  forAll arbitrary $ \r1 ->
    not $ Interval.null $ Interval.singleton (r1::Rational)

prop_distinct_singleton_intersection =
  forAll arbitrary $ \r1 ->
  forAll arbitrary $ \r2 ->
    (r1::Rational) /= r2 ==>
      Interval.intersection (Interval.singleton r1) (Interval.singleton r2)
      == Interval.empty

{--------------------------------------------------------------------
  Intersection
--------------------------------------------------------------------}

prop_intersection_comm =
  forAll intervals $ \a ->
  forAll intervals $ \b ->
    Interval.intersection a b == Interval.intersection b a

prop_intersection_assoc =
  forAll intervals $ \a ->
  forAll intervals $ \b ->
  forAll intervals $ \c ->
    Interval.intersection a (Interval.intersection b c) ==
    Interval.intersection (Interval.intersection a b) c

prop_intersection_unitL =
  forAll intervals $ \a ->
    Interval.intersection Interval.whole a == a

prop_intersection_unitR =
  forAll intervals $ \a ->
    Interval.intersection a Interval.whole == a

prop_intersection_empty =
  forAll intervals $ \a ->
    Interval.intersection a Interval.empty == Interval.empty

prop_intersection_isSubsetOf =
  forAll intervals $ \a ->
  forAll intervals $ \b ->
    Interval.isSubsetOf (Interval.intersection a b) a

prop_intersection_isSubsetOf_equiv =
  forAll intervals $ \a ->
  forAll intervals $ \b ->
    (Interval.intersection a b == a)
    == Interval.isSubsetOf a b

{--------------------------------------------------------------------
  Hull
--------------------------------------------------------------------}

prop_hull_comm =
  forAll intervals $ \a ->
  forAll intervals $ \b ->
    Interval.hull a b == Interval.hull b a

prop_hull_assoc =
  forAll intervals $ \a ->
  forAll intervals $ \b ->
  forAll intervals $ \c ->
    Interval.hull a (Interval.hull b c) ==
    Interval.hull (Interval.hull a b) c

prop_hull_unitL =
  forAll intervals $ \a ->
    Interval.hull Interval.empty a == a

prop_hull_unitR =
  forAll intervals $ \a ->
    Interval.hull a Interval.empty == a

prop_hull_whole =
  forAll intervals $ \a ->
    Interval.hull a Interval.whole == Interval.whole

prop_hull_isSubsetOf =
  forAll intervals $ \a ->
  forAll intervals $ \b ->
    Interval.isSubsetOf a (Interval.hull a b)

prop_hull_isSubsetOf_equiv =
  forAll intervals $ \a ->
  forAll intervals $ \b ->
    (Interval.hull a b == b)
    == Interval.isSubsetOf a b

{--------------------------------------------------------------------
  member
--------------------------------------------------------------------}

prop_member_isSubsetOf =
  forAll arbitrary $ \r ->
  forAll intervals $ \a ->
    Interval.member r a == Interval.isSubsetOf (Interval.singleton r) a

{--------------------------------------------------------------------
  isSubsetOf
--------------------------------------------------------------------}

prop_isSubsetOf_refl =
  forAll intervals $ \a ->
    Interval.isSubsetOf a a

prop_isSubsetOf_trans =
  forAll intervals $ \a ->
  forAll intervals $ \b ->
  forAll intervals $ \c ->
    Interval.isSubsetOf a b && Interval.isSubsetOf b c
    ==> Interval.isSubsetOf a c

-- prop_isSubsetOf_antisym =
--   forAll intervals $ \a ->
--   forAll intervals $ \b ->
--     Interval.isSubsetOf a b && Interval.isSubsetOf b a
--     ==> a == b

{--------------------------------------------------------------------
  pickup
--------------------------------------------------------------------}

prop_pickup_member_null =
  forAll intervals $ \a ->
    case Interval.pickup a of
      Nothing -> Interval.null a
      Just x -> Interval.member x a

case_pickup_empty =
  Interval.pickup (Interval.empty :: Interval Rational) @?= Nothing

case_pickup_whole =
  isJust (Interval.pickup (Interval.whole :: Interval Rational)) @?= True

{--------------------------------------------------------------------
  Comparison
--------------------------------------------------------------------}

case_lt_all_1 = (a <! b) @?= False
  where
    a, b :: Interval Rational
    a = NegInf <..<= Finite 0
    b = Finite 0 <=..< PosInf

case_lt_all_2 = (a <! b) @?= True
  where
    a, b :: Interval Rational
    a = NegInf <..< Finite 0
    b = Finite 0 <=..< PosInf

case_lt_all_3 = (a <! b) @?= True
  where
    a, b :: Interval Rational
    a = NegInf <..<= Finite 0
    b = Finite 0 <..< PosInf

case_lt_all_4 = (a <! b) @?= False
  where
    a, b :: Interval Rational
    a = Finite 0 <=..< PosInf
    b = Finite 1 <=..< PosInf

case_lt_some_1 = (a <? b) @?= False
  where
    a, b :: Interval Rational
    a = Finite 0 <=..< PosInf
    b = NegInf <..<= Finite 0

case_lt_some_2 = (a <? b) @?= False
  where
    a, b :: Interval Rational
    a = Finite 0 <..< PosInf
    b = NegInf <..<= Finite 0

case_lt_some_3 = (a <? b) @?= False
  where
    a, b :: Interval Rational
    a = Finite 0 <=..< PosInf
    b = NegInf <..< Finite 0

case_lt_some_4 = (a <! b) @?= False
  where
    a, b :: Interval Rational
    a = Finite 0 <=..< PosInf
    b = Finite 1 <=..< PosInf

case_le_some_1 = (a <=? b) @?= True
  where
    a, b :: Interval Rational
    a = Finite 0 <=..< PosInf
    b = NegInf <..<= Finite 0

case_le_some_2 = (a <=? b) @?= False
  where
    a, b :: Interval Rational
    a = Finite 0 <..< PosInf
    b = NegInf <..<= Finite 0

case_le_some_3 = (a <=? b) @?= False
  where
    a, b :: Interval Rational
    a = Finite 0 <=..< PosInf
    b = NegInf <..< Finite 0

prop_lt_all_not_refl =
  forAll intervals $ \a -> not (Interval.null a) ==> not (a <! a)

prop_le_some_refl =
  forAll intervals $ \a -> not (Interval.null a) ==> a <=? a

prop_lt_all_singleton =
  forAll arbitrary $ \a ->
  forAll arbitrary $ \b ->
    (a::Rational) < b ==> Interval.singleton a <! Interval.singleton b

prop_lt_all_singleton_2 =
  forAll arbitrary $ \a ->
    not $ Interval.singleton (a::Rational) <! Interval.singleton a

prop_le_all_singleton =
  forAll arbitrary $ \a ->
  forAll arbitrary $ \b ->
    (a::Rational) <= b ==> Interval.singleton a <=! Interval.singleton b

prop_le_all_singleton_2 =
  forAll arbitrary $ \a ->
    Interval.singleton (a::Rational) <=! Interval.singleton a

prop_lt_some_singleton =
  forAll arbitrary $ \a ->
  forAll arbitrary $ \b ->
    (a::Rational) < b ==> Interval.singleton a <? Interval.singleton b

prop_lt_some_singleton_2 =
  forAll arbitrary $ \a ->
    not $ Interval.singleton (a::Rational) <? Interval.singleton a

prop_le_some_singleton =
  forAll arbitrary $ \a ->
  forAll arbitrary $ \b ->
    (a::Rational) <= b ==> Interval.singleton a <=? Interval.singleton b

prop_le_some_singleton_2 =
  forAll arbitrary $ \a ->
    Interval.singleton (a::Rational) <=? Interval.singleton a

{--------------------------------------------------------------------
  Num
--------------------------------------------------------------------}

prop_scale_empty =
  forAll arbitrary $ \r ->
    Interval.singleton (r::Rational) * Interval.empty == Interval.empty

prop_add_comm =
  forAll intervals $ \a ->
  forAll intervals $ \b ->
    a + b == b + a

prop_add_assoc =
  forAll intervals $ \a ->
  forAll intervals $ \b ->
  forAll intervals $ \c ->
    a + (b + c) == (a + b) + c

prop_add_unitL =
  forAll intervals $ \a ->
    Interval.singleton 0 + a == a

prop_add_unitR =
  forAll intervals $ \a ->
    a + Interval.singleton 0 == a

prop_add_member =
  forAll intervals $ \a ->
  forAll intervals $ \b ->
    and [ (x+y) `Interval.member` (a+b)
        | x <- maybeToList $ Interval.pickup a
        , y <- maybeToList $ Interval.pickup b
        ]

prop_mult_comm =
  forAll intervals $ \a ->
  forAll intervals $ \b ->
    a * b == b * a

prop_mult_assoc =
  forAll intervals $ \a ->
  forAll intervals $ \b ->
  forAll intervals $ \c ->
    a * (b * c) == (a * b) * c

prop_mult_unitL =
  forAll intervals $ \a ->
    Interval.singleton 1 * a == a

prop_mult_unitR =
  forAll intervals $ \a ->
    a * Interval.singleton 1 == a

prop_mult_dist =
  forAll intervals $ \a ->
  forAll intervals $ \b ->
  forAll intervals $ \c ->
    (a * (b + c)) `Interval.isSubsetOf` (a * b + a * c)

prop_mult_empty =
  forAll intervals $ \a ->
    Interval.empty * a == Interval.empty

prop_mult_zero = 
  forAll intervals $ \a ->
    not (Interval.null a) ==> Interval.singleton 0 * a ==  Interval.singleton 0

prop_mult_member =
  forAll intervals $ \a ->
  forAll intervals $ \b ->
    and [ (x*y) `Interval.member` (a*b)
        | x <- maybeToList $ Interval.pickup a
        , y <- maybeToList $ Interval.pickup b
        ]

case_mult_test1 = ival1 * ival2 @?= ival3
  where
    ival1 = Finite 1 <=..<= Finite 2
    ival2 = Finite 1 <=..<= Finite 2
    ival3 = Finite 1 <=..<= Finite 4

case_mult_test2 = ival1 * ival2 @?= ival3
  where
    ival1 = Finite 1 <=..<= Finite 2
    ival2 = Finite 1 <..< Finite 2
    ival3 = Finite 1 <..< Finite 4

case_mult_test3 = ival1 * ival2 @?= ival3
  where
    ival1 = Finite 1 <..< Finite 2
    ival2 = Finite 1 <..< Finite 2
    ival3 = Finite 1 <..< Finite 4

case_mult_test4 = ival1 * ival2 @?= ival3
  where
    ival1 = Finite 2 <..< PosInf
    ival2 = Finite 3 <..< PosInf
    ival3 = Finite 6 <..< PosInf

case_mult_test5 = ival1 * ival2 @?= ival3
  where
    ival1 = NegInf <..< Finite (-3)
    ival2 = NegInf <..< Finite (-2)
    ival3 = Finite 6 <..< PosInf

case_mult_test6 = ival1 * ival2 @?= ival3
  where
    ival1 = Finite 2 <..< PosInf
    ival2 = NegInf <..< Finite (-2)
    ival3 = NegInf <..< Finite (-4)

{--------------------------------------------------------------------
  Fractional
--------------------------------------------------------------------}

prop_recip_singleton =
  forAll arbitrary $ \r ->
    let n = fromIntegral (numerator r)
        d = fromIntegral (denominator r)
    in Interval.singleton n / Interval.singleton d == Interval.singleton (r::Rational)

case_recip_pos =
  recip pos @?= pos

case_recip_neg =
  recip neg @?= neg

case_recip_test1 = recip i1 @?= i2
  where
    i1, i2 :: Interval Rational
    i1 = Finite 2 <=..< PosInf
    i2 = Finite 0 <..<= Finite (1/2)

{--------------------------------------------------------------------
  Read
--------------------------------------------------------------------}

prop_show_read_invariance =
  forAll intervals $ \i -> do
    i == read (show i)

{--------------------------------------------------------------------
  Generators
--------------------------------------------------------------------}

instance Arbitrary r => Arbitrary (EndPoint r) where
  arbitrary = 
    oneof
    [ return NegInf
    , return PosInf
    , liftM Finite arbitrary
    ]

intervals :: Gen (Interval Rational)
intervals = do
  lb <- arbitrary
  ub <- arbitrary
  return $ Interval.interval lb ub

pos :: Interval Rational
pos = Finite 0 <..< PosInf

neg :: Interval Rational
neg = NegInf <..< Finite 0

nonpos :: Interval Rational
nonpos = NegInf <..<= Finite 0

nonneg :: Interval Rational
nonneg = Finite 0 <=..< PosInf

------------------------------------------------------------------------
-- Test harness

main :: IO ()
main = $(defaultMainGenerator)
