{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
module Test.SAT.Encoder (satEncoderTestGroup) where

import Control.Monad
import Data.Array.IArray
import qualified Data.IntMap.Strict as IntMap
import Data.IORef
import Data.List
import Data.Maybe
import qualified Data.Vector as V
import System.IO.Unsafe

import Test.Tasty
import Test.Tasty.QuickCheck hiding ((.&&.), (.||.))
import Test.Tasty.HUnit
import Test.Tasty.TH
import qualified Test.QuickCheck.Monadic as QM

import ToySolver.Data.Boolean
import ToySolver.Data.LBool
import qualified ToySolver.FileFormat.CNF as CNF
import qualified ToySolver.SAT as SAT
import qualified ToySolver.SAT.Types as SAT
import qualified ToySolver.SAT.Encoder.Tseitin as Tseitin
import ToySolver.SAT.Encoder.Tseitin (Formula (..))
import qualified ToySolver.SAT.Encoder.Cardinality as Cardinality
import qualified ToySolver.SAT.Encoder.Cardinality.Internal.Totalizer as Totalizer
import qualified ToySolver.SAT.Encoder.PB as PB
import qualified ToySolver.SAT.Encoder.PB.Internal.Sorter as PBEncSorter
import qualified ToySolver.SAT.Encoder.PB.Internal.BCCNF as BCCNF
import qualified ToySolver.SAT.Store.CNF as CNFStore

import Test.SAT.Utils

case_fold_sharing :: Assertion
case_fold_sharing = do
  ref <- newIORef IntMap.empty
  let [x1, x2, x3, x4, x5] = map Atom [1..5]
      formula = orB [x1 .=>. x3 .&&. x4, x2 .=>. x3 .&&. x5]
      f x = unsafePerformIO $ do
        modifyIORef' ref (IntMap.insertWith (+) x (1::Int))
        return $ Atom x
      formula' = Tseitin.fold f formula
  ret <- seq formula' $ readIORef ref
  ret @?= IntMap.fromList [(1, 1), (2, 1), (3, 1), (4, 1), (5, 1)]

case_addFormula :: Assertion
case_addFormula = do
  solver <- SAT.newSolver
  enc <- Tseitin.newEncoder solver

  [x1,x2,x3,x4,x5] <- replicateM 5 $ liftM Atom $ SAT.newVar solver
  Tseitin.addFormula enc $ orB [x1 .=>. x3 .&&. x4, x2 .=>. x3 .&&. x5]
  -- x6 = x3 ∧ x4
  -- x7 = x3 ∧ x5
  Tseitin.addFormula enc $ x1 .||. x2
  Tseitin.addFormula enc $ x4 .=>. notB x5
  ret <- SAT.solve solver
  ret @?= True

  Tseitin.addFormula enc $ x2 .<=>. x4
  ret <- SAT.solve solver
  ret @?= True

  Tseitin.addFormula enc $ x1 .<=>. x5
  ret <- SAT.solve solver
  ret @?= True

  Tseitin.addFormula enc $ notB x1 .=>. x3 .&&. x5
  ret <- SAT.solve solver
  ret @?= True

  Tseitin.addFormula enc $ notB x2 .=>. x3 .&&. x4
  ret <- SAT.solve solver
  ret @?= False

case_addFormula_Peirces_Law :: Assertion
case_addFormula_Peirces_Law = do
  solver <- SAT.newSolver
  enc <- Tseitin.newEncoder solver
  [x1,x2] <- replicateM 2 $ liftM Atom $ SAT.newVar solver
  Tseitin.addFormula enc $ notB $ ((x1 .=>. x2) .=>. x1) .=>. x1
  ret <- SAT.solve solver
  ret @?= False

case_encodeConj :: Assertion
case_encodeConj = do
  solver <- SAT.newSolver
  enc <- Tseitin.newEncoder solver
  x1 <- SAT.newVar solver
  x2 <- SAT.newVar solver
  x3 <- Tseitin.encodeConj enc [x1,x2]

  ret <- SAT.solveWith solver [x3]
  ret @?= True
  m <- SAT.getModel solver
  SAT.evalLit m x1 @?= True
  SAT.evalLit m x2 @?= True
  SAT.evalLit m x3 @?= True

  ret <- SAT.solveWith solver [-x3]
  ret @?= True
  m <- SAT.getModel solver
  (SAT.evalLit m x1 && SAT.evalLit m x2) @?= False
  SAT.evalLit m x3 @?= False

case_encodeDisj :: Assertion
case_encodeDisj = do
  solver <- SAT.newSolver
  enc <- Tseitin.newEncoder solver
  x1 <- SAT.newVar solver
  x2 <- SAT.newVar solver
  x3 <- Tseitin.encodeDisj enc [x1,x2]

  ret <- SAT.solveWith solver [x3]
  ret @?= True
  m <- SAT.getModel solver
  (SAT.evalLit m x1 || SAT.evalLit m x2) @?= True
  SAT.evalLit m x3 @?= True

  ret <- SAT.solveWith solver [-x3]
  ret @?= True
  m <- SAT.getModel solver
  SAT.evalLit m x1 @?= False
  SAT.evalLit m x2 @?= False
  SAT.evalLit m x3 @?= False

case_evalFormula :: Assertion
case_evalFormula = do
  solver <- SAT.newSolver
  xs <- SAT.newVars solver 5
  let f = (x1 .=>. x3 .&&. x4) .||. (x2 .=>. x3 .&&. x5)
        where
          [x1,x2,x3,x4,x5] = map Atom xs
      g :: SAT.Model -> Bool
      g m = (not x1 || (x3 && x4)) || (not x2 || (x3 && x5))
        where
          [x1,x2,x3,x4,x5] = elems m
  forM_ (allAssignments 5) $ \m -> do
    Tseitin.evalFormula m f @?= g m

prop_PBEncoder_addPBAtLeast :: Property
prop_PBEncoder_addPBAtLeast = QM.monadicIO $ do
  let nv = 4
  (lhs,rhs) <- QM.pick $ do
    lhs <- arbitraryPBLinSum nv
    rhs <- arbitrary
    return $ SAT.normalizePBLinAtLeast (lhs, rhs)
  strategy <- QM.pick arbitrary
  (cnf,defs) <- QM.run $ do
    db <- CNFStore.newCNFStore
    SAT.newVars_ db nv
    tseitin <- Tseitin.newEncoder db
    pb <- PB.newEncoderWithStrategy tseitin strategy
    SAT.addPBAtLeast pb lhs rhs
    cnf <- CNFStore.getCNFFormula db
    defs <- Tseitin.getDefinitions tseitin
    return (cnf, defs)
  forM_ (allAssignments 4) $ \m -> do
    let m2 :: Array SAT.Var Bool
        m2 = array (1, CNF.cnfNumVars cnf) $ assocs m ++ [(v, Tseitin.evalFormula m2 phi) | (v,phi) <- defs]
        b1 = SAT.evalPBLinAtLeast m (lhs,rhs)
        b2 = evalCNF (array (bounds m2) (assocs m2)) cnf
    QM.assert $ b1 == b2

prop_PBEncoder_encodePBLinAtLeastWithPolarity :: Property
prop_PBEncoder_encodePBLinAtLeastWithPolarity = QM.monadicIO $ do
  let nv = 4
  constr <- QM.pick $ do
    lhs <- arbitraryPBLinSum nv
    rhs <- arbitrary
    return (lhs, rhs)
  strategy <- QM.pick arbitrary
  polarity <- QM.pick arbitrary
  (l,cnf,defs,defs2) <- QM.run $ do
    db <- CNFStore.newCNFStore
    SAT.newVars_ db nv
    tseitin <- Tseitin.newEncoder db
    encoder@(PB.Encoder card _) <- PB.newEncoderWithStrategy tseitin strategy
    l <- PB.encodePBLinAtLeastWithPolarity encoder polarity constr
    cnf <- CNFStore.getCNFFormula db
    defs <- Tseitin.getDefinitions tseitin
    defs2 <- Cardinality.getTotalizerDefinitions card
    return (l, cnf, defs, defs2)
  forM_ (allAssignments nv) $ \m -> do
    let m2 :: Array SAT.Var Bool
        m2 = array (1, CNF.cnfNumVars cnf) $
               assocs m ++
               [(v, Tseitin.evalFormula m2 phi) | (v,phi) <- defs] ++
               Cardinality.evalTotalizerDefinitions m2 defs2
        b1 = evalCNF (array (bounds m2) (assocs m2)) cnf
        cmp a b = isJust $ do
          when (Tseitin.polarityPosOccurs polarity) $ guard (not a || b)
          when (Tseitin.polarityNegOccurs polarity) $ guard (not b || a)
    QM.assert $ not b1 || (SAT.evalLit m2 l `cmp` SAT.evalPBLinAtLeast m constr)

prop_PBEncoder_encodePBLinAtLeastWithPolarity_2 :: Property
prop_PBEncoder_encodePBLinAtLeastWithPolarity_2 = QM.monadicIO $ do
  nv <- QM.pick $ choose (1, 10)
  constr <- QM.pick $ do
    lhs <- arbitraryPBLinSum nv
    rhs <- arbitrary
    return (lhs, rhs)
  strategy <- QM.pick arbitrary
  polarity <- QM.pick arbitrary
  join $ QM.run $ do
    solver <- SAT.newSolver
    SAT.newVars_ solver nv
    tseitin <- Tseitin.newEncoder solver
    encoder <- PB.newEncoderWithStrategy tseitin strategy
    l <- PB.encodePBLinAtLeastWithPolarity encoder polarity constr
    ret <- SAT.solve solver
    if not ret then do
      return $ QM.assert False
    else do
      m <- SAT.getModel solver
      let a = SAT.evalLit m l
          b = SAT.evalPBLinAtLeast m constr
      return $ do
        QM.monitor $ counterexample (show (a,b))
        when (Tseitin.polarityPosOccurs polarity) $ QM.assert (not a || b)
        when (Tseitin.polarityNegOccurs polarity) $ QM.assert (not b || a)

prop_PBEncoder_Sorter_genSorter :: [Int] -> Bool
prop_PBEncoder_Sorter_genSorter xs =
  V.toList (PBEncSorter.sortVector (V.fromList xs)) == sort xs

prop_PBEncoder_Sorter_decode_encode :: Property
prop_PBEncoder_Sorter_decode_encode =
  forAll arbitrary $ \base' ->
    forAll arbitrary $ \(NonNegative x) ->
      let base = [b | Positive b <- base']
      in PBEncSorter.isRepresentable base x
         ==>
         (PBEncSorter.decode base . PBEncSorter.encode base) x == x


arbitraryAtLeast :: Int -> Gen SAT.AtLeast
arbitraryAtLeast nv = do
  lhs <- liftM catMaybes $ forM [1..nv] $ \i -> do
    b <- arbitrary
    if b then
      Just <$> elements [i, -i]
    else
      return Nothing
  rhs <- choose (-1, nv+2)
  return $ (lhs, rhs)


prop_CardinalityEncoder_addAtLeast :: Property
prop_CardinalityEncoder_addAtLeast = QM.monadicIO $ do
  let nv = 4
  (lhs,rhs) <- QM.pick $ arbitraryAtLeast nv
  strategy <- QM.pick arbitrary
  (cnf,defs,defs2) <- QM.run $ do
    db <- CNFStore.newCNFStore
    SAT.newVars_ db nv
    tseitin <- Tseitin.newEncoder db
    card <- Cardinality.newEncoderWithStrategy tseitin strategy
    SAT.addAtLeast card lhs rhs
    cnf <- CNFStore.getCNFFormula db
    defs <- Tseitin.getDefinitions tseitin
    defs2 <- Cardinality.getTotalizerDefinitions card
    return (cnf, defs, defs2)
  forM_ (allAssignments nv) $ \m -> do
    let m2 :: Array SAT.Var Bool
        m2 = array (1, CNF.cnfNumVars cnf) $
               assocs m ++
               [(v, Tseitin.evalFormula m2 phi) | (v,phi) <- defs] ++
               Cardinality.evalTotalizerDefinitions m2 defs2
        b1 = SAT.evalAtLeast m (lhs,rhs)
        b2 = evalCNF (array (bounds m2) (assocs m2)) cnf
    QM.assert $ b1 == b2


case_Totalizer_unary :: Assertion
case_Totalizer_unary = do
  solver <- SAT.newSolver
  tseitin <- Tseitin.newEncoder solver
  totalizer <- Totalizer.newEncoder tseitin
  SAT.newVars_ solver 5
  xs <- Totalizer.encodeSum totalizer [1,2,3,4,5]
  SAT.addClause solver [xs !! 2]
  SAT.addClause solver [- (xs !! 1)]
  ret <- SAT.solve solver
  ret @?= False


-- -- This does not hold:
-- case_Totalizer_pre_unary :: Assertion
-- case_Totalizer_pre_unary = do
--   solver <- SAT.newSolver
--   tseitin <- Tseitin.newEncoder solver
--   totalizer <- Totalizer.newEncoder tseitin
--   SAT.newVars_ solver 5
--   xs <- Totalizer.encodeSum totalizer [1,2,3,4,5]
--   SAT.addClause solver [xs !! 2]
--   v0 <- SAT.getLitFixed solver (xs !! 0)
--   v1 <- SAT.getLitFixed solver (xs !! 1)
--   v0 @?= lTrue
--   v1 @?= lTrue


prop_Totalizer_forward_propagation :: Property
prop_Totalizer_forward_propagation = QM.monadicIO $ do
  nv <- QM.pick $ choose (2, 10) -- inclusive range
  let xs = [1..nv]
  (xs1, xs2) <- QM.pick $ do
    cs <- forM xs $ \x -> do
      c <- arbitrary
      return (x,c)
    return ([x | (x, Just True) <- cs], [x | (x, Just False) <- cs])
  let p = length xs1
      q = length xs2
  lbs <- QM.run $ do
    solver <- SAT.newSolver
    tseitin <- Tseitin.newEncoder solver
    totalizer <- Totalizer.newEncoder tseitin
    SAT.newVars_ solver nv
    ys <- Totalizer.encodeSum totalizer xs
    forM_ xs1 $ \x -> SAT.addClause solver [x]
    forM_ xs2 $ \x -> SAT.addClause solver [-x]
    forM ys $ SAT.getLitFixed solver
  QM.monitor $ counterexample (show lbs)
  QM.assert $ lbs == replicate p lTrue ++ replicate (nv - p - q) lUndef ++ replicate q lFalse


prop_Totalizer_backward_propagation :: Property
prop_Totalizer_backward_propagation = QM.monadicIO $ do
  nv <- QM.pick $ choose (2, 10) -- inclusive range
  let xs = [1..nv]
  (xs1, xs2) <- QM.pick $ do
    cs <- forM xs $ \x -> do
      c <- arbitrary
      return (x,c)
    return ([x | (x, Just True) <- cs], [x | (x, Just False) <- cs])
  let p = length xs1
      q = length xs2
  e <- QM.pick arbitrary
  lbs <- QM.run $ do
    solver <- SAT.newSolver
    tseitin <- Tseitin.newEncoder solver
    totalizer <- Totalizer.newEncoder tseitin
    SAT.newVars_ solver nv
    ys <- Totalizer.encodeSum totalizer xs
    forM_ xs1 $ \x -> SAT.addClause solver [x]
    forM_ xs2 $ \x -> SAT.addClause solver [-x]
    forM_ (take (nv - p - q) (drop p ys)) $ \x -> do
      SAT.addClause solver [if e then x else - x]
    forM xs $ SAT.getLitFixed solver
  QM.monitor $ counterexample (show lbs)
  QM.assert $ and [x `elem` xs1 || x `elem` xs2 || lbs !! (x-1) == liftBool e | x <- xs]


prop_encodeAtLeastWithPolarity :: Property
prop_encodeAtLeastWithPolarity = QM.monadicIO $ do
  let nv = 4
  (lhs,rhs) <- QM.pick $ arbitraryAtLeast nv
  strategy <- QM.pick arbitrary
  polarity <- QM.pick arbitrary
  (l,cnf,defs,defs2) <- QM.run $ do
    db <- CNFStore.newCNFStore
    SAT.newVars_ db nv
    tseitin <- Tseitin.newEncoder db
    card <- Cardinality.newEncoderWithStrategy tseitin strategy
    l <- Cardinality.encodeAtLeastWithPolarity card polarity (lhs, rhs)
    cnf <- CNFStore.getCNFFormula db
    defs <- Tseitin.getDefinitions tseitin
    defs2 <- Cardinality.getTotalizerDefinitions card
    return (l, cnf, defs, defs2)
  forM_ (allAssignments nv) $ \m -> do
    let m2 :: Array SAT.Var Bool
        m2 = array (1, CNF.cnfNumVars cnf) $
               assocs m ++
               [(v, Tseitin.evalFormula m2 phi) | (v,phi) <- defs] ++
               Cardinality.evalTotalizerDefinitions m2 defs2
        b1 = evalCNF (array (bounds m2) (assocs m2)) cnf
        cmp a b = isJust $ do
          when (Tseitin.polarityPosOccurs polarity) $ guard (not a || b)
          when (Tseitin.polarityNegOccurs polarity) $ guard (not b || a)
    QM.assert $ not b1 || (SAT.evalLit m2 l `cmp` SAT.evalAtLeast m (lhs,rhs))

prop_encodeAtLeastWithPolarity_2 :: Property
prop_encodeAtLeastWithPolarity_2 = QM.monadicIO $ do
  nv <- QM.pick $ choose (1, 10)
  constr <- QM.pick $ arbitraryAtLeast nv
  strategy <- QM.pick arbitrary
  polarity <- QM.pick arbitrary
  join $ QM.run $ do
    solver <- SAT.newSolver
    SAT.newVars_ solver nv
    tseitin <- Tseitin.newEncoder solver
    card <- Cardinality.newEncoderWithStrategy tseitin strategy
    l <- Cardinality.encodeAtLeastWithPolarity card polarity constr
    ret <- SAT.solve solver
    if not ret then do
      return $ QM.assert False
    else do
      m <- SAT.getModel solver
      let a = SAT.evalLit m l
          b = SAT.evalAtLeast m constr
      return $ do
        QM.monitor $ counterexample (show (a,b))
        when (Tseitin.polarityPosOccurs polarity) $ QM.assert (not a || b)
        when (Tseitin.polarityNegOccurs polarity) $ QM.assert (not b || a)

-- ------------------------------------------------------------------------

case_BCCNF_example :: Assertion
case_BCCNF_example = do
  let -- 5 x1 + 3 x2 + 3 x3 + 3 x4 + 3 x5 + x6 >= 9
      input = ([(5,1),(3,2),(3,3),(3,4),(3,5),(1,6)], 9)
      -- (s1 ≥ 1 ∨ s5 ≥ 3) ∧ (s6 ≥ 3)
      expected =
        [ [([1], 1), ([1,2,3,4,5], 3)]
        , [([1,2,3,4,5,6], 3)]
        ]

  -- 2 s1 + 2 s5 + s6
  let lhs' = [(2,1,[1]), (2,5,[1..5]), (1,6,[1..6])]
  BCCNF.toPrefixSum (fst input) @?= lhs'

  let _bccnf0, bccnf1 :: BCCNF.BCCNF
      _bccnf0 =
        [ [(1,[1..1],1), (2,[1..2],2)]
        , [(1,[1..1],1), (5,[1..5],3), (6,[1..6],5)]
        , [(1,[1..1],1), (5,[1..5],4), (6,[1..6],3)]
        , [(1,[1..1],1), (5,[1..5],5), (6,[1..6],1)]
        , [(5,[1..5],1)]
        , [(5,[1..5],2), (6,[1..6],5)]
        , [(5,[1..5],3), (6,[1..6],3)]
        , [(5,[1..5],4), (6,[1..6],1)]
        ]
      bccnf1 =
        [ [(1,[1..1],1), (5,[1..5],3)]
        , [(5,[1..5],2)]
        , [(5,[1..5],3), (6,[1..6],3)]
        ]
      bccnf2 =
        [ [(1,[1..1],1), (5,[1..5],3)]
        , [(6,[1..6],3)]
        ]
  BCCNF.encodePrefixSum lhs' 9 @?= bccnf1

  assertBool "(s5 >= 3) should imply (s6 >= 3)" $ BCCNF.implyBCLit (5,[1..5],3) (6,[1..6],3)
  assertBool "(s6 >= 3) should imply (s5 >= 2)" $ BCCNF.implyBCLit (6,[1..6],3) (5,[1..5],2)
  assertBool "((s5 >= 3) or (s6 >= 3)) should imply (s5 >= 2) as clauses" $ BCCNF.implyBCClause [(5,[1..5],3), (6,[1..6],3)] [(5,[1..5],2)]
  assertBool "(s6 >= 3) should imply (s5 >= 2) as clauses" $ BCCNF.implyBCClause [(6,[1..6],3)] [(5,[1..5],2)]

  BCCNF.reduceBCCNF bccnf1 @?= bccnf2

  BCCNF.encode input @?= expected

case_BCCNF_algorithm2_bug :: Assertion
case_BCCNF_algorithm2_bug = do
  let lhs = [(7,1),(6,2),(5,3),(4,4),(3,5)]
      rhs = 14
      lhs' = BCCNF.toPrefixSum lhs
      bccnf = BCCNF.encodePrefixSumBuggy lhs' rhs
      m :: SAT.Model
      m = array (1,5) [(1,True),(2,False),(3,False),(4,True),(5,True)]
      a = SAT.evalPBLinAtLeast m (lhs,rhs)
      b = eval m bccnf
  assertBool ("Original constraint should be true under (" ++ show m ++ ")") a
  assertBool ("Encoded BCNF is false under (" ++ show m ++ ") due to the bug of Algorithm 2") (not b)
  where
    eval m = and . map (or . map (SAT.evalAtLeast m . BCCNF.toAtLeast))

case_BCCNF_algorithm2_bug_fixed :: Assertion
case_BCCNF_algorithm2_bug_fixed = do
  let lhs = [(7,1),(6,2),(5,3),(4,4),(3,5)]
      rhs = 14
      lhs' = BCCNF.toPrefixSum lhs
      bccnf = BCCNF.encodePrefixSum lhs' rhs
  forM_ (allAssignments 5) $ \m -> do
    assertEqual ("evalution under " ++ show m)
      (SAT.evalPBLinAtLeast m (lhs,rhs)) (eval m bccnf)
  where
    eval m = and . map (or . map (SAT.evalAtLeast m . BCCNF.toAtLeast))

arbitraryPBLinSumForBCCNF :: Int -> Gen SAT.PBLinAtLeast
arbitraryPBLinSumForBCCNF n = BCCNF.preprocess <$> ((,) <$> arbitraryPBLinSum n <*> arbitrary)
{-
arbitraryPBLinSumForBCCNF n = do
  as <- vectorOf n (liftM getPositive arbitrary)
  let bs = init $ scanr (+) 0 as
  c <- arbitrary
  return (zip bs [1..], c)  
-}

prop_BCCNF_encodePrefixSumNaive :: Property
prop_BCCNF_encodePrefixSumNaive =
  forAll (choose (1, 8)) $ \nv ->
    forAll (arbitraryPBLinSumForBCCNF nv) $ \constr@(lhs, rhs) ->
      let lhs' = BCCNF.toPrefixSum lhs
          bccnf = BCCNF.encodePrefixSumNaive lhs' rhs
       in counterexample (show lhs') $ counterexample (show bccnf) $ conjoin
          [ counterexample (show m) $
            counterexample (show (map (map (SAT.evalAtLeast m . BCCNF.toAtLeast)) bccnf)) $
              eval m bccnf === SAT.evalPBLinAtLeast m constr
          | m <- allAssignments nv
          ]
  where
    eval m = and . map (or . map (SAT.evalAtLeast m . BCCNF.toAtLeast))

prop_BCCNF_encodePrefixSum :: Property
prop_BCCNF_encodePrefixSum =
  forAll (choose (1, 10)) $ \nv ->
    forAll (arbitraryPBLinSumForBCCNF nv) $ \constr@(lhs, rhs) ->
      let lhs' = BCCNF.toPrefixSum lhs
          bccnf = BCCNF.encodePrefixSum lhs' rhs
       in counterexample (show lhs') $ counterexample (show bccnf) $ conjoin
          [ counterexample (show m) $
            counterexample (show (map (map (SAT.evalAtLeast m . BCCNF.toAtLeast)) bccnf)) $
              eval m bccnf === SAT.evalPBLinAtLeast m constr
          | m <- allAssignments nv
          ]
  where
    eval m = and . map (or . map (SAT.evalAtLeast m . BCCNF.toAtLeast))

prop_BCCNF_encode :: Property
prop_BCCNF_encode =
  forAll (choose (1, 6)) $ \nv ->
    forAll (arbitraryPBLinSumForBCCNF nv) $ \constr ->
      let bccnf = BCCNF.encode constr
       in counterexample (show bccnf) $ conjoin
          [ counterexample (show m) $
            counterexample (show (map (map (SAT.evalAtLeast m)) bccnf)) $
              eval m bccnf === SAT.evalPBLinAtLeast m constr
          | m <- allAssignments nv
          ]
  where
    eval m = and . map (or . map (SAT.evalAtLeast m))

-- ------------------------------------------------------------------------

satEncoderTestGroup :: TestTree
satEncoderTestGroup = $(testGroupGenerator)
