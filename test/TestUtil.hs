{-# LANGUAGE TemplateHaskell, ScopedTypeVariables #-}
module Main (main) where

import Control.Applicative
import Control.Monad
import Test.HUnit hiding (Test)
import Test.QuickCheck hiding ((.&&.), (.||.))
import Test.QuickCheck.Function
import Test.Framework (Test, defaultMain, testGroup)
import Test.Framework.TH
import Test.Framework.Providers.QuickCheck2
import Test.Framework.Providers.HUnit
import ToySolver.Data.Boolean
import ToySolver.Data.BoolExpr
import qualified ToySolver.Internal.Data.Vec as Vec
import ToySolver.Internal.Util
import ToySolver.Internal.TextUtil
import qualified ToySolver.Knapsack as Knapsack
import qualified ToySolver.Knapsack.DP as KnapsackDP
import qualified ToySolver.Wang as Wang

case_showRationalAsDecimal :: IO ()
case_showRationalAsDecimal = do
  showRationalAsFiniteDecimal 0      @?= Just "0.0"
  showRationalAsFiniteDecimal 1      @?= Just "1.0"
  showRationalAsFiniteDecimal (-1)   @?= Just "-1.0"
  showRationalAsFiniteDecimal 0.1    @?= Just "0.1"
  showRationalAsFiniteDecimal (-0.1) @?= Just "-0.1"
  showRationalAsFiniteDecimal 1.1    @?= Just "1.1"
  showRationalAsFiniteDecimal (-1.1) @?= Just "-1.1"
  showRationalAsFiniteDecimal (5/4)  @?= Just "1.25"
  showRationalAsFiniteDecimal (-5/4) @?= Just "-1.25"
  showRationalAsFiniteDecimal (4/3)  @?= Nothing
  showRationalAsFiniteDecimal (-4/3) @?= Nothing

case_readUnsignedInteger_maxBound_bug :: IO ()
case_readUnsignedInteger_maxBound_bug =
  readUnsignedInteger "006666666666666667" @?= 6666666666666667

prop_readUnsignedInteger = 
  forAll (choose (0, 2^128)) $ \i -> 
    readUnsignedInteger (show i) == i

case_knapsack_1 :: IO ()
case_knapsack_1 = Knapsack.solve [(5,4), (6,5), (3,2)] 9 @?= (11, 9, [True,True,False])

case_knapsack_2 :: IO ()
case_knapsack_2 = Knapsack.solve [(16,2), (19,3), (23,4), (28,5)] 7 @?= (44, 7, [True,False,False,True])

case_knapsack_DP_1 :: IO ()
case_knapsack_DP_1 = KnapsackDP.solve [(5,4), (6,5), (3,2)] 9 @?= (11, 9, [True,True,False])

case_knapsack_DP_2 :: IO ()
case_knapsack_DP_2 = KnapsackDP.solve [(16,2), (19,3), (23,4), (28,5)] 7 @?= (44, 7, [True,False,False,True])

case_Vec :: IO ()
case_Vec = do
  (v::Vec.UVec Int) <- Vec.new
  let xs = [0..100]
  forM_ xs $ \i -> Vec.push v i
  ys <- Vec.getElems v
  ys @?= xs

  Vec.resize v 4
  zs <- Vec.getElems v
  zs @?= take 4 xs

  Vec.push v 1
  Vec.push v 2
  Vec.push v 3

  ws <- Vec.getElems v
  ws @?= take 4 xs ++ [1,2,3]

  x3 <- Vec.unsafePop v
  x3 @?= 3
  s <- Vec.getSize v
  s @?= 6
  ws <- Vec.getElems v
  ws @?= take 4 xs ++ [1,2]

case_Vec_clone :: IO ()
case_Vec_clone = do
  (v::Vec.UVec Int) <- Vec.new  
  Vec.push v 0
  v2 <- Vec.clone v
  Vec.write v2 0 1

  a <- Vec.read v 0
  a @?= 0

  b <- Vec.read v2 0
  b @?= 1

-- ---------------------------------------------------------------------
-- BoolExpr

instance Arbitrary a => Arbitrary (BoolExpr a) where
  arbitrary = sized f
    where
      f n =        
        oneof
        [ Atom <$> arbitrary
        , And <$> list (n-1)
        , Or <$> list (n-1)
        , Not <$> (f (n-1))
        , uncurry Imply <$> pair (n-1)
        , uncurry Equiv <$> pair (n-1)
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
      list n | n <= 0 = return []
      list n = oneof $
        [ return []
        , do m <- choose (0,n)
             x  <- f m
             xs <- list (n-m-1)
             return (x:xs)
        ]

prop_BoolExpr_Functor_identity =
  forAll arbitrary $ \(b :: BoolExpr Int) ->
    fmap id b == b

prop_BoolExpr_Functor_compsition =
  forAll arbitrary $ \(b :: BoolExpr Int) ->
    forAll arbitrary $ \(f :: Fun Int Int) ->
      forAll arbitrary $ \(g :: Fun Int Int) ->
        fmap (apply f . apply g) b == fmap (apply f) (fmap (apply g) b)

prop_BoolExpr_Applicative_identity =
  forAll arbitrary $ \(b :: BoolExpr Int) ->
    (pure id <*> b) == b

prop_BoolExpr_Applicative_composition =
  forAll arbitrary $ \(w :: BoolExpr Int) ->
    forAll arbitrary $ \(u :: BoolExpr (Fun Int Int)) ->
      forAll arbitrary $ \(v :: BoolExpr (Fun Int Int)) ->
        (pure (.) <*> fmap apply u <*> fmap apply v <*> w) == (fmap apply u <*> (fmap apply v <*> w))

prop_BoolExpr_Applicative_homomorphism =
  forAll arbitrary $ \(x :: Int) ->
    forAll arbitrary $ \(f :: Fun Int Int) ->
      (pure (apply f) <*> pure x) == (pure (apply f x) :: BoolExpr Int)

prop_BoolExpr_Applicative_interchange =
  forAll arbitrary $ \(y :: Int) ->
    forAll arbitrary $ \(u :: BoolExpr (Fun Int Int)) ->
      (fmap apply u <*> pure y) == (pure ($ y) <*> fmap apply u)

prop_BoolExpr_Monad_left_identity =
  forAll arbitrary $ \(b :: BoolExpr Int) ->
    forAll arbitrary $ \(f :: Fun Int (BoolExpr Int)) ->
        (b >>= (\x -> return x >>= apply f)) == (b >>= apply f)

prop_BoolExpr_Monad_bind_right_identity =
  forAll arbitrary $ \(b :: BoolExpr Int) ->
    forAll arbitrary $ \(f :: Fun Int (BoolExpr Int)) ->
        (b >>= (\x -> apply f x >>= return)) == (b >>= apply f)

prop_BoolExpr_Monad_bind_associativity =
  forAll arbitrary $ \(b :: BoolExpr Int) ->
    forAll arbitrary $ \(f :: Fun Int (BoolExpr Int)) ->
      forAll arbitrary $ \(g :: Fun Int (BoolExpr Int)) ->
        (b >>= apply f >>= apply g) == (b >>= (\x -> apply f x >>= apply g))


-- ---------------------------------------------------------------------
-- Wang

-- (x1 ∨ x2) ∧ (x1 ∨ ¬x2) ∧ (¬x1 ∨ ¬x2) is satisfiable
-- ¬((x1 ∨ x2) ∧ (x1 ∨ ¬x2) ∧ (¬x1 ∨ ¬x2)) is invalid
case_Wang_1 =
  Wang.isValid ([], [phi]) @?= False
  where
    phi = notB $ andB [x1 .||. x2, x1 .||. notB x2, notB x1 .||. notB x2]
    x1 = Atom 1
    x2 = Atom 2

-- (x1 ∨ x2) ∧ (¬x1 ∨ x2) ∧ (x1 ∨ ¬x2) ∧ (¬x1 ∨ ¬x2) is unsatisfiable
-- ¬((x1 ∨ x2) ∧ (¬x1 ∨ x2) ∧ (x1 ∨ ¬x2) ∧ (¬x1 ∨ ¬x2)) is valid
case_Wang_2 =
  Wang.isValid ([], [phi]) @?= True
  where
    phi = notB $ andB [x1 .||. x2, notB x1 .||. x2, x1 .||. notB x2, notB x1 .||. notB x2]
    x1 = Atom 1
    x2 = Atom 2

case_Wang_EM =
  Wang.isValid ([], [phi]) @?= True
  where
    phi = x1 .||. notB x1
    x1 = Atom 1

case_Wang_DNE =
  Wang.isValid ([], [phi]) @?= True
  where
    phi = notB (notB x1) .<=>. x1
    x1 = Atom 1

case_Wang_Peirces_Law =
  Wang.isValid ([], [phi]) @?= True
  where
    phi = ((x1 .=>. x2) .=>. x1) .=>. x1
    x1 = Atom 1
    x2 = Atom 2

------------------------------------------------------------------------
-- Test harness

main :: IO ()
main = $(defaultMainGenerator)
