{-# OPTIONS_GHC -Wall -fno-warn-orphans #-}
{-# LANGUAGE TemplateHaskell, ScopedTypeVariables #-}
module Test.BoolExpr (boolExprTestGroup) where

import Control.Applicative
import Test.QuickCheck.Function
import Test.Tasty
import Test.Tasty.QuickCheck hiding ((.&&.), (.||.))
import Test.Tasty.TH
import ToySolver.Data.BoolExpr

-- ---------------------------------------------------------------------
-- BoolExpr

instance Arbitrary a => Arbitrary (BoolExpr a) where
  arbitrary = sized f
    where
      f n | n <= 0 = Atom <$> arbitrary
      f n =
        oneof
        [ Atom <$> arbitrary
        , And <$> list (n-1)
        , Or <$> list (n-1)
        , Not <$> (f (n-1))
        , uncurry Imply <$> pair (n-1)
        , uncurry Equiv <$> pair (n-1)
        , triple (n-1) >>= \(c,t,e) -> return (ITE c t e)
        ]

      pair n | n <= 0 = do
        a <- f 0
        b <- f 0
        return (a,b)
      pair n = do
        m <- choose (0,n)
        a <- f m
        b <- f (n-m)
        return (a,b)

      triple n | n <= 0 = do
        a <- f 0
        b <- f 0
        c <- f 0
        return (a,b,c)
      triple n = do
        m <- choose (0, n)
        o <- choose (0, n-m)
        a <- f m
        b <- f o
        c <- f (n - m - o)
        return (a,b,c)

      list n | n <= 0 = return []
      list n = oneof $
        [ return []
        , do m <- choose (0,n)
             x  <- f m
             xs <- list (n-m-1)
             return (x:xs)
        ]

prop_BoolExpr_Functor_identity :: Property
prop_BoolExpr_Functor_identity =
  forAll arbitrary $ \(b :: BoolExpr Int) ->
    fmap id b == b

prop_BoolExpr_Functor_compsition :: Property
prop_BoolExpr_Functor_compsition =
  forAll arbitrary $ \(b :: BoolExpr Int) ->
    forAll arbitrary $ \(f :: Fun Int Int) ->
      forAll arbitrary $ \(g :: Fun Int Int) ->
        fmap (apply f . apply g) b == fmap (apply f) (fmap (apply g) b)

prop_BoolExpr_Applicative_identity :: Property
prop_BoolExpr_Applicative_identity =
  forAll arbitrary $ \(b :: BoolExpr Int) ->
    (pure id <*> b) == b

prop_BoolExpr_Applicative_composition :: Property
prop_BoolExpr_Applicative_composition =
  forAll arbitrary $ \(w :: BoolExpr Int) ->
    forAll arbitrary $ \(u :: BoolExpr (Fun Int Int)) ->
      forAll arbitrary $ \(v :: BoolExpr (Fun Int Int)) ->
        (pure (.) <*> fmap apply u <*> fmap apply v <*> w) == (fmap apply u <*> (fmap apply v <*> w))

prop_BoolExpr_Applicative_homomorphism :: Property
prop_BoolExpr_Applicative_homomorphism =
  forAll arbitrary $ \(x :: Int) ->
    forAll arbitrary $ \(f :: Fun Int Int) ->
      (pure (apply f) <*> pure x) == (pure (apply f x) :: BoolExpr Int)

prop_BoolExpr_Applicative_interchange :: Property
prop_BoolExpr_Applicative_interchange =
  forAll arbitrary $ \(y :: Int) ->
    forAll arbitrary $ \(u :: BoolExpr (Fun Int Int)) ->
      (fmap apply u <*> pure y) == (pure ($ y) <*> fmap apply u)

prop_BoolExpr_Monad_left_identity :: Property
prop_BoolExpr_Monad_left_identity =
  forAll arbitrary $ \(b :: BoolExpr Int) ->
    forAll arbitrary $ \(f :: Fun Int (BoolExpr Int)) ->
        (b >>= (\x -> return x >>= apply f)) == (b >>= apply f)

prop_BoolExpr_Monad_bind_right_identity :: Property
prop_BoolExpr_Monad_bind_right_identity =
  forAll arbitrary $ \(b :: BoolExpr Int) ->
    forAll arbitrary $ \(f :: Fun Int (BoolExpr Int)) ->
        (b >>= (\x -> apply f x >>= return)) == (b >>= apply f)

prop_BoolExpr_Monad_bind_associativity :: Property
prop_BoolExpr_Monad_bind_associativity =
  forAll arbitrary $ \(b :: BoolExpr Int) ->
    forAll arbitrary $ \(f :: Fun Int (BoolExpr Int)) ->
      forAll arbitrary $ \(g :: Fun Int (BoolExpr Int)) ->
        (b >>= apply f >>= apply g) == (b >>= (\x -> apply f x >>= apply g))

------------------------------------------------------------------------
-- Test harness

boolExprTestGroup :: TestTree
boolExprTestGroup = $(testGroupGenerator)
