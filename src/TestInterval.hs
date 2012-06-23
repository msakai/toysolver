{-# LANGUAGE TemplateHaskell #-}

import Data.Maybe
import Test.HUnit hiding (Test)
import Test.QuickCheck
import Test.Framework (Test, defaultMain, testGroup)
import Test.Framework.TH
import Test.Framework.Providers.HUnit
import Test.Framework.Providers.QuickCheck2

import Data.Interval (Interval)
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
  univ
--------------------------------------------------------------------}

prop_univ_is_top =
  forAll intervals $ \a ->
    Interval.isSubsetOf a Interval.univ

case_nonnull_top =
  Interval.null (Interval.univ :: Interval Rational) @?= False

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
    Interval.intersection Interval.univ a == a

prop_intersection_unitR =
  forAll intervals $ \a ->
    Interval.intersection a Interval.univ == a

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
  Join
--------------------------------------------------------------------}

prop_join_comm =
  forAll intervals $ \a ->
  forAll intervals $ \b ->
    Interval.join a b == Interval.join b a

prop_join_assoc =
  forAll intervals $ \a ->
  forAll intervals $ \b ->
  forAll intervals $ \c ->
    Interval.join a (Interval.join b c) ==
    Interval.join (Interval.join a b) c

prop_join_unitL =
  forAll intervals $ \a ->
    Interval.join Interval.empty a == a

prop_join_unitR =
  forAll intervals $ \a ->
    Interval.join a Interval.empty == a

prop_join_univ =
  forAll intervals $ \a ->
    Interval.join a Interval.univ == Interval.univ

prop_join_isSubsetOf =
  forAll intervals $ \a ->
  forAll intervals $ \b ->
    Interval.isSubsetOf a (Interval.join a b)

prop_join_isSubsetOf_equiv =
  forAll intervals $ \a ->
  forAll intervals $ \b ->
    (Interval.join a b == b)
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

case_pickup_univ =
  isJust (Interval.pickup (Interval.univ :: Interval Rational)) @?= True

{--------------------------------------------------------------------
  Generators
--------------------------------------------------------------------}

intervals :: Gen (Interval Rational)
intervals = do
  lb <- arbitrary
  ub <- arbitrary
  return $ Interval.interval lb ub

------------------------------------------------------------------------
-- Test harness

main :: IO ()
main = $(defaultMainGenerator)
