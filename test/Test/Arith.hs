{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
module Test.Arith (arithTestGroup) where

import Control.Monad
import Data.List
import Data.Default.Class
import qualified Data.IntMap as IM
import qualified Data.IntSet as IS
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Maybe
import Data.VectorSpace

import Test.Tasty
import Test.Tasty.QuickCheck hiding ((.&&.), (.||.))
import Test.Tasty.HUnit
import Test.Tasty.TH
import qualified Test.QuickCheck as QC
import qualified Test.QuickCheck.Monadic as QM

import qualified Data.Interval as Interval
import Data.OptDir

import ToySolver.Data.AlgebraicNumber.Real
import ToySolver.Data.OrdRel
import ToySolver.Data.FOL.Arith
import qualified ToySolver.Data.LA as LA
import qualified ToySolver.Data.Polynomial as P
import ToySolver.Data.IntVar

import qualified ToySolver.Arith.FourierMotzkin as FourierMotzkin
import qualified ToySolver.Arith.FourierMotzkin.Optimization as FMOpt
import qualified ToySolver.Arith.OmegaTest as OmegaTest
import qualified ToySolver.Arith.OmegaTest.Base as OmegaTest
import qualified ToySolver.Arith.Cooper as Cooper
import qualified ToySolver.Arith.CAD as CAD
import qualified ToySolver.Arith.Simplex as Simplex
import qualified ToySolver.Arith.Simplex.Simple as SimplexSimple
import qualified ToySolver.Arith.ContiTraverso as ContiTraverso
import qualified ToySolver.Arith.VirtualSubstitution as VirtualSubstitution

------------------------------------------------------------------------

{-
Example from the OmegaTest paper

7x + 12y + 31z = 17
3x + 5y + 14z = 7
1 ≤ x ≤ 40
-50 ≤ y ≤ 50

satisfiable in R
satisfiable in Z

(declare-fun x () Int)
(declare-fun y () Int)
(declare-fun z () Int)
(assert (= (+ (* 7 x) (* 12 y) (* 31 z)) 17))
(assert (= (+ (* 3 x) (* 5 y) (* 14 z)) 7))
(assert (<= 1 x))
(assert (<= x 40))
(assert (<= (- 50) y))
(assert (<= y 50))
(check-sat) ; => sat
(get-model)

Just (DNF {unDNF = [[Nonneg (fromTerms [(-17,-1),(7,0),(12,1),(31,2)]),Nonneg (fromTerms [(17,-1),(-7,0),(-12,1),(-31,2)]),Nonneg (fromTerms [(-7,-1),(3,0),(5,1),(14,2)]),Nonneg (fromTerms [(7,-1),(-3,0),(-5,1),(-14,2)]),Nonneg (fromTerms [(-1,-1),(1,0)]),Nonneg (fromTerms [(40,-1),(-1,0)]),Nonneg (fromTerms [(50,-1),(1,1)]),Nonneg (fromTerms [(50,-1),(-1,1)])]]})

7x+12y+31z  - 17 >= 0
-7x-12y-31z + 17 >= 0
3x+5y+14z - 7  >= 0
-3x-5y-14z + 7 >= 0
x - 1 >= 0
-x + 40 >= 0
y + 50  >= 0
-y + 50 >= 0
-}
test1 :: Formula (Atom Rational)
test1 = c1 .&&. c2 .&&. c3 .&&. c4
  where
    x = Var 0
    y = Var 1
    z = Var 2
    c1 = 7*x + 12*y + 31*z .==. 17
    c2 = 3*x + 5*y + 14*z .==. 7
    c3 = 1 .<=. x .&&. x .<=. 40
    c4 = (-50) .<=. y .&&. y .<=. 50

test1' :: (VarSet, [LA.Atom Rational])
test1' = (IS.fromList [0,1,2], [c1, c2] ++ c3 ++ c4)
  where
    x = LA.var 0
    y = LA.var 1
    z = LA.var 2
    c1 = 7*^x ^+^ 12*^y ^+^ 31*^z .==. LA.constant 17
    c2 = 3*^x ^+^ 5*^y ^+^ 14*^z .==. LA.constant 7
    c3 = [LA.constant 1 .<=. x, x .<=. LA.constant 40]
    c4 = [LA.constant (-50) .<=. y, y .<=. LA.constant 50]


{-
Example from the OmegaTest paper

27 ≤ 11x+13y ≤ 45
-10 ≤ 7x-9y ≤ 4

satisfiable in R
but unsatisfiable in Z

(declare-fun x () Int)
(declare-fun y () Int)
(define-fun t1 () Int (+ (* 11 x) (* 13 y)))
(define-fun t2 () Int (- (* 7 x) (* 9 y)))
(assert (<= 27 t1))
(assert (<= t1 45))
(assert (<= (- 10) t2))
(assert (<= t2 4))
(check-sat) ; unsat
(get-model)
-}
test2 :: Formula (Atom Rational)
test2 = c1 .&&. c2
  where
    x = Var 0
    y = Var 1
    t1 = 11*x + 13*y
    t2 = 7*x - 9*y
    c1 = 27 .<=. t1 .&&. t1 .<=. 45
    c2 = (-10) .<=. t2 .&&. t2 .<=. 4

test2' :: (VarSet, [LA.Atom Rational])
test2' =
  ( IS.fromList [0,1]
  , [ LA.constant 27 .<=. t1
    , t1 .<=. LA.constant 45
    , LA.constant (-10) .<=. t2
    , t2 .<=. LA.constant 4
    ]
  )
  where
    x = LA.var 0
    y = LA.var 1
    t1 = 11*^x ^+^ 13*^y
    t2 = 7*^x ^-^ 9*^y


genLAExpr :: [Var] -> Gen (LA.Expr Rational)
genLAExpr vs = do
  size <- choose (0,3)
  liftM LA.fromTerms $ replicateM size $ do
    x <- elements (LA.unitVar : vs)
    c <- arbitrary
    return (c,x)
    
genLAExprSmallInt :: [Var] -> Gen (LA.Expr Rational)
genLAExprSmallInt vs = do
  size <- choose (0,3)
  liftM LA.fromTerms $ replicateM size $ do
    x <- elements (LA.unitVar : vs)
    c <- choose (-10,10)
    return (fromInteger c,x)

genQFLAConj :: Gen (VarSet, [LA.Atom Rational])
genQFLAConj = do
  nv <- choose (0, 5)
  nc <- choose (0, 5)
  let vs = IS.fromList [1..nv]
  cs <- replicateM nc $ do
    op  <- elements [Lt, Le, Ge, Gt, Eql] -- , NEq
    lhs <- genLAExpr [1..nv]
    rhs <- genLAExpr [1..nv]
    return $ ordRel op lhs rhs
  return (vs, cs)
  
genQFLAConjSmallInt :: Gen (VarSet, [LA.Atom Rational])
genQFLAConjSmallInt = do
  nv <- choose (0, 3)
  nc <- choose (0, 3)
  let vs = IS.fromList [1..nv]
  cs <- replicateM nc $ do
    op  <- elements [Lt, Le, Ge, Gt, Eql] -- , NEq
    lhs <- genLAExprSmallInt [1..nv]
    rhs <- genLAExprSmallInt [1..nv]
    return $ ordRel op lhs rhs
  return (vs, cs)

genModel :: Arbitrary a => VarSet -> Gen (Model a)
genModel xs = do
  liftM IM.fromList $ forM (IS.toList xs) $ \x -> do
    val <- arbitrary
    return (x,val)

------------------------------------------------------------------------
 
prop_FourierMotzkin_solve :: Property
prop_FourierMotzkin_solve =
  forAll genQFLAConj $ \(vs,cs) ->
    case FourierMotzkin.solve vs cs of
      Nothing -> forAll (genModel vs) $ \(m :: Model Rational) -> all (LA.eval m) cs == False
      Just m  -> property $ all (LA.eval m) cs

case_FourierMotzkin_test1 :: Assertion
case_FourierMotzkin_test1 = 
  case uncurry FourierMotzkin.solve test1' of
    Nothing -> assertFailure "expected: Just\n but got: Nothing"
    Just m  ->
      forM_ (snd test1') $ \a -> do
        LA.eval m a @?= True

case_FourierMotzkin_test2 :: Assertion
case_FourierMotzkin_test2 = 
  case uncurry FourierMotzkin.solve test2' of
    Nothing -> assertFailure "expected: Just\n but got: Nothing"
    Just m  ->
      forM_ (snd test2') $ \a -> do
        LA.eval m a @?= True

{-
Maximize
 obj: x1 + 2 x2 + 3 x3 + x4
Subject To
 c1: - x1 + x2 + x3 + 10 x4 <= 20
 c2: x1 - 3 x2 + x3 <= 30
 c3: x2 - 3.5 x4 = 0
Bounds
 0 <= x1 <= 40
 2 <= x4 <= 3
End
-}
case_FourierMotzkinOptimization_test1 :: Assertion
case_FourierMotzkinOptimization_test1 = do
  Interval.upperBound' i @?= (3005/24, True)
  and [LA.eval m c | c <- cs] @?= True
  where
    (i, f) = FMOpt.optimize (IS.fromList vs) OptMax obj cs
    m = f (3005/24)

    vs@[x1,x2,x3,x4] = [1..4]
    obj = LA.fromTerms [(1,x1), (2,x2), (3,x3), (1,x4)]
    cs = [ LA.fromTerms [(-1,x1), (1,x2), (1,x3), (10,x4)] .<=. LA.constant 20
         , LA.fromTerms [(1,x1), (-3,x2), (1,x3)] .<=. LA.constant 30
         , LA.fromTerms [(1,x2), (-3.5,x4)] .==. LA.constant 0
         , LA.fromTerms [(1,x1)] .>=. LA.constant 0
         , LA.fromTerms [(1,x1)] .<=. LA.constant 40
         , LA.fromTerms [(1,x2)] .>=. LA.constant 0
         , LA.fromTerms [(1,x3)] .>=. LA.constant 0
         , LA.fromTerms [(1,x4)] .>=. LA.constant 2
         , LA.fromTerms [(1,x4)] .<=. LA.constant 3
         ]

------------------------------------------------------------------------
        
prop_VirtualSubstitution_solve :: Property
prop_VirtualSubstitution_solve =
   forAll genQFLAConj $ \(vs,cs) ->
     case VirtualSubstitution.solve vs cs of
       Nothing -> forAll (genModel vs) $ \(m :: Model Rational) -> all (LA.eval m) cs == False
       Just m  -> property $ all (LA.eval m) cs

case_VirtualSubstitution_test1 :: Assertion
case_VirtualSubstitution_test1 = 
  case uncurry VirtualSubstitution.solve test1' of
    Nothing -> assertFailure "expected: Just\n but got: Nothing"
    Just m  ->
      forM_ (snd test1') $ \a -> do
        LA.eval m a @?= True

case_VirtualSubstitution_test2 :: Assertion
case_VirtualSubstitution_test2 = 
  case uncurry VirtualSubstitution.solve test2' of
    Nothing -> assertFailure "expected: Just\n but got: Nothing"
    Just m  ->
      forM_ (snd test2') $ \a -> do
        LA.eval m a @?= True

------------------------------------------------------------------------
        
-- too slow
disabled_prop_CAD_solve :: Property
disabled_prop_CAD_solve =
   forAll genQFLAConj $ \(vs,cs) ->
     let vs' = Set.fromAscList $ IS.toAscList vs
         cs' = map toPRel cs
     in case CAD.solve vs' cs' of
          Nothing ->
            forAll (genModel vs) $ \m ->
              let m' = Map.fromAscList [(x, fromRational v) | (x,v) <- IM.toAscList m]
              in all (evalPAtom m') cs' == False
          Just m  -> property $ all (evalPAtom m) cs'

case_CAD_test1 :: Assertion
case_CAD_test1 = 
  case CAD.solve vs cs of
    Nothing -> assertFailure "expected: Just\n but got: Nothing"
    Just m  ->
      forM_ cs $ \a -> do
        evalPAtom m a @?= True
  where
    vs = Set.fromAscList $ IS.toAscList $ fst test1'
    cs = map toPRel $ snd test1'

case_CAD_test2 :: Assertion
case_CAD_test2 = 
  case CAD.solve vs cs of
    Nothing -> assertFailure "expected: Just\n but got: Nothing"
    Just m  ->
      forM_ cs $ \a -> do
        evalPAtom m a @?= True
  where
    vs = Set.fromAscList $ IS.toAscList $ fst test2'
    cs = map toPRel $ snd test2'

case_CAD_test_nonlinear_multivariate :: Assertion
case_CAD_test_nonlinear_multivariate =
  case CAD.solve vs cs of
    Nothing -> assertFailure "expected: Just\n but got: Nothing"
    Just m  ->
      forM_ cs $ \a -> do
        evalPAtom m a @?= True
  where
    vs = Set.fromList [0,1]
    cs = [x^2 - y^2 - 2 .==. 0, 2*y*x .==. 0]
    x = P.var (0::Int)
    y = P.var 1

toP :: LA.Expr Rational -> P.Polynomial Rational Int
toP e = P.fromTerms [(c, if x == LA.unitVar then P.mone else P.var x) | (c,x) <- LA.terms e]

toPRel :: LA.Atom Rational -> OrdRel (P.Polynomial Rational Int)
toPRel = fmap toP

evalP :: Map.Map Int AReal -> P.Polynomial Rational Int -> AReal
evalP m p = P.eval (m Map.!) $ P.mapCoeff fromRational p

evalPAtom :: Map.Map Int AReal -> OrdRel (P.Polynomial Rational Int) -> Bool
evalPAtom m (OrdRel lhs op rhs) =　evalOp op (evalP m lhs) (evalP m rhs)

------------------------------------------------------------------------

prop_OmegaTest_solve :: Property
prop_OmegaTest_solve =
   forAll genQFLAConjSmallInt $ \(vs,cs) ->
     case OmegaTest.solve def vs cs of
       Nothing ->
         forAll (liftM (fmap fromInteger) $ genModel vs) $ \(m :: Model Rational) -> all (LA.eval m) cs == False
       Just m  -> property $ all (LA.eval (fmap fromInteger m :: Model Rational)) cs

case_OmegaTest_test1 :: Assertion
case_OmegaTest_test1 = 
  case uncurry (OmegaTest.solve def) test1' of
    Nothing -> assertFailure "expected: Just\n but got: Nothing"
    Just m  -> do
      forM_ (snd test1') $ \a -> do
        LA.eval (IM.map fromInteger m :: Model Rational) a @?= True

case_OmegaTest_test2 :: Assertion
case_OmegaTest_test2 = 
  case uncurry (OmegaTest.solve def) test2' of
    Just _  -> assertFailure "expected: Nothing\n but got: Just"
    Nothing -> return ()

prop_OmegaTest_zmod =
  forAll arbitrary $ \a ->
  forAll arbitrary $ \b ->
    b /= 0 ==>
      let c = a `OmegaTest.zmod` b
      in (a - c) `mod` b == 0 && abs c <= abs b `div` 2

------------------------------------------------------------------------

prop_Cooper_solve :: Property
prop_Cooper_solve =
   forAll genQFLAConjSmallInt $ \(vs,cs) ->
     case Cooper.solve vs cs of
       Nothing ->
         (forAll (liftM (fmap fromInteger) $ genModel vs) $ \(m :: Model Rational) -> all (LA.eval m) cs == False)
         QC..&&.
         property (OmegaTest.solve def vs cs == Nothing)
       Just m  -> property $ all (LA.eval (fmap fromInteger m :: Model Rational)) cs

case_Cooper_test1 :: Assertion
case_Cooper_test1 = 
  case uncurry Cooper.solve test1' of
    Nothing -> assertFailure "expected: Just\n but got: Nothing"
    Just m  -> do
      forM_ (snd test1') $ \a -> do
        LA.eval (IM.map fromInteger m :: Model Rational) a @?= True

case_Cooper_test2 :: Assertion
case_Cooper_test2 = 
  case uncurry Cooper.solve test2' of
    Just _  -> assertFailure "expected: Nothing\n but got: Just"
    Nothing -> return ()

------------------------------------------------------------------------
    
prop_Simplex_solve :: Property
prop_Simplex_solve = forAll genQFLAConj $ \(vs,cs) -> do
  case SimplexSimple.check vs cs of
    Nothing -> True
    Just m -> all (LA.eval m) cs

case_Simplex_test1 :: Assertion
case_Simplex_test1 =
  isJust (uncurry SimplexSimple.check test1') @?= True

case_Simplex_test2 :: Assertion
case_Simplex_test2 = do
  isJust (uncurry SimplexSimple.check test2') @?= True

prop_Simplex_backtrack :: Property
prop_Simplex_backtrack = QM.monadicIO $ do
   (vs,cs) <- QM.pick genQFLAConj
   (vs2,cs2) <- QM.pick genQFLAConj
   config <- QM.pick arbitrary

   join $ QM.run $ do
     solver <- Simplex.newSolver
     Simplex.setConfig solver config
     m <- liftM IM.fromList $ forM (IS.toList (vs `IS.union` vs2)) $ \v -> do
       v2 <- Simplex.newVar solver
       return (v, LA.var v2)
     forM_ cs $ \c -> do
       Simplex.assertAtomEx solver (LA.applySubstAtom m c)
     ret <- Simplex.check solver
     if ret then do
       Simplex.pushBacktrackPoint solver
       forM_ cs2 $ \c -> do
         Simplex.assertAtomEx solver (LA.applySubstAtom m c)
       _ <- Simplex.check solver
       Simplex.popBacktrackPoint solver
       ret2 <- Simplex.check solver
       return $ QM.assert ret2
     else do
       return $ return ()

prop_Simplex_explain :: Property
prop_Simplex_explain = QM.monadicIO $ do
   (vs,cs) <- QM.pick genQFLAConj
   config <- QM.pick arbitrary

   let f p = QM.run $ do
         solver <- Simplex.newSolver
         Simplex.setConfig solver config
         m <- liftM IM.fromList $ forM (IS.toList vs) $ \v -> do
           v2 <- Simplex.newVar solver
           return (v, LA.var v2)
         forM (zip [0..] cs) $ \(i,c) -> do
           when (p i) $
             Simplex.assertAtomEx' solver (LA.applySubstAtom m c) (Just i)
         ret <- Simplex.check solver
         if ret then do
           return Nothing
         else do
           liftM Just $ Simplex.explain solver

   ret <- f (const True)
   case ret of
     Nothing -> return ()
     Just e -> do
       ret2 <- f (`IS.member` e)
       QM.assert (ret2 == Just e)
       forM_ (IS.toList e) $ \i -> do
         ret3 <- f (`IS.member` (IS.delete i e))
         QM.assert (isNothing ret3)

instance Arbitrary Simplex.Config where
  arbitrary = do
    ps <- arbitrary
    enableBoundTightening <- arbitrary
    return $
      Simplex.Config
      { Simplex.configPivotStrategy = ps
      , Simplex.configEnableBoundTightening = enableBoundTightening
      }

instance Arbitrary Simplex.PivotStrategy where
  arbitrary = arbitraryBoundedEnum

------------------------------------------------------------------------

-- Too slow

disabled_case_ContiTraverso_test1 :: Assertion
disabled_case_ContiTraverso_test1 = 
  case ContiTraverso.solve P.grlex (fst test1') OptMin (LA.constant 0) (snd test1') of
    Nothing -> assertFailure "expected: Just\n but got: Nothing"
    Just m  -> do
      forM_ (snd test1') $ \a -> do
        LA.eval (IM.map fromInteger m :: Model Rational) a @?= True

disabled_case_ContiTraverso_test2 :: Assertion
disabled_case_ContiTraverso_test2 = 
  case ContiTraverso.solve P.grlex (fst test2') OptMin (LA.constant 0) (snd test2') of
    Just _  -> assertFailure "expected: Nothing\n but got: Just"
    Nothing -> return ()
------------------------------------------------------------------------
-- Test harness

arithTestGroup :: TestTree
arithTestGroup = $(testGroupGenerator)
