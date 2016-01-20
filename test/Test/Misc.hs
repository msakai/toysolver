{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE TemplateHaskell, ScopedTypeVariables #-}
module Test.Misc (miscTestGroup) where

import Control.Monad
import Test.Tasty
import Test.Tasty.QuickCheck hiding ((.&&.), (.||.))
import Test.Tasty.HUnit
import Test.Tasty.TH
import ToySolver.Data.Boolean
import ToySolver.Data.BoolExpr
import qualified ToySolver.Internal.Data.Vec as Vec
import ToySolver.Internal.Util
import ToySolver.Internal.TextUtil
import qualified ToySolver.Wang as Wang

case_showRationalAsDecimal :: Assertion
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

case_readUnsignedInteger_maxBound_bug :: Assertion
case_readUnsignedInteger_maxBound_bug =
  readUnsignedInteger "006666666666666667" @?= 6666666666666667

prop_readUnsignedInteger :: Property
prop_readUnsignedInteger = 
  forAll (choose (0, 2^(128::Int))) $ \i -> 
    readUnsignedInteger (show i) == i

-- ---------------------------------------------------------------------
-- Vec

case_Vec :: Assertion
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

case_Vec_clone :: Assertion
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
-- Wang

-- (x1 ∨ x2) ∧ (x1 ∨ ¬x2) ∧ (¬x1 ∨ ¬x2) is satisfiable
-- ¬((x1 ∨ x2) ∧ (x1 ∨ ¬x2) ∧ (¬x1 ∨ ¬x2)) is invalid
case_Wang_1 :: Assertion
case_Wang_1 =
  Wang.isValid ([], [phi]) @?= False
  where
    phi = notB $ andB [x1 .||. x2, x1 .||. notB x2, notB x1 .||. notB x2]
    x1, x2 :: BoolExpr Int
    x1 = Atom 1
    x2 = Atom 2

-- (x1 ∨ x2) ∧ (¬x1 ∨ x2) ∧ (x1 ∨ ¬x2) ∧ (¬x1 ∨ ¬x2) is unsatisfiable
-- ¬((x1 ∨ x2) ∧ (¬x1 ∨ x2) ∧ (x1 ∨ ¬x2) ∧ (¬x1 ∨ ¬x2)) is valid
case_Wang_2 :: Assertion
case_Wang_2 =
  Wang.isValid ([], [phi]) @?= True
  where
    phi = notB $ andB [x1 .||. x2, notB x1 .||. x2, x1 .||. notB x2, notB x1 .||. notB x2]
    x1, x2 :: BoolExpr Int
    x1 = Atom 1
    x2 = Atom 2

case_Wang_EM :: Assertion
case_Wang_EM =
  Wang.isValid ([], [phi]) @?= True
  where
    phi = x1 .||. notB x1
    x1 :: BoolExpr Int
    x1 = Atom 1

case_Wang_DNE :: Assertion
case_Wang_DNE =
  Wang.isValid ([], [phi]) @?= True
  where
    phi = notB (notB x1) .<=>. x1
    x1 :: BoolExpr Int
    x1 = Atom 1

case_Wang_Peirces_Law :: Assertion
case_Wang_Peirces_Law =
  Wang.isValid ([], [phi]) @?= True
  where
    phi = ((x1 .=>. x2) .=>. x1) .=>. x1
    x1, x2 :: BoolExpr Int
    x1 = Atom 1
    x2 = Atom 2

------------------------------------------------------------------------
-- Test harness

miscTestGroup :: TestTree
miscTestGroup = $(testGroupGenerator)
