{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
module Test.Converter (converterTestGroup) where

import Control.Monad
import Data.Array.IArray
import qualified Data.Foldable as F
import Data.Maybe
import Data.Set (Set)
import qualified Data.Set as Set
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import qualified Data.Vector.Generic as VG

import Test.Tasty
import Test.Tasty.QuickCheck hiding ((.&&.), (.||.))
import Test.Tasty.TH
import qualified Test.QuickCheck as QC
import qualified Test.QuickCheck.Monadic as QM

import ToySolver.Converter
import qualified ToySolver.FileFormat.CNF as CNF
import qualified ToySolver.MaxCut as MaxCut
import qualified ToySolver.SAT as SAT
import qualified ToySolver.SAT.Types as SAT

import qualified Data.PseudoBoolean as PBFile

import Test.SAT.Utils


prop_sat2naesat_forward :: Property
prop_sat2naesat_forward = forAll arbitraryCNF $ \cnf ->
  let ret@(nae,info) = sat2naesat cnf
   in counterexample (show ret) $ 
        forAllAssignments (CNF.cnfNumVars cnf) $ \m ->
          evalCNF m cnf === evalNAESAT (transformForward info m) nae

prop_sat2naesat_backward :: Property
prop_sat2naesat_backward = forAll arbitraryCNF $ \cnf ->
  let ret@(nae,info) = sat2naesat cnf
   in counterexample (show ret) $ 
        forAllAssignments (fst nae) $ \m ->
          evalCNF (transformBackward info m) cnf === evalNAESAT m nae

prop_naesat2sat_forward :: Property
prop_naesat2sat_forward = forAll arbitraryNAESAT $ \nae ->
  let ret@(cnf,info) = naesat2sat nae
   in counterexample (show ret) $ 
        forAllAssignments (fst nae) $ \m ->
          evalNAESAT m nae === evalCNF (transformForward info m) cnf

prop_naesat2sat_backward :: Property
prop_naesat2sat_backward = forAll arbitraryNAESAT $ \nae ->
  let ret@(cnf,info) = naesat2sat nae
   in counterexample (show ret) $
        forAllAssignments (CNF.cnfNumVars cnf) $ \m ->
          evalNAESAT (transformBackward info m) nae === evalCNF m cnf

prop_naesat2naeksat_forward :: Property
prop_naesat2naeksat_forward =
  forAll arbitraryNAESAT $ \nae ->
  forAll (choose (3,10)) $ \k ->
    let ret@(nae',info) = naesat2naeksat k nae
     in counterexample (show ret) $
          property (all (\c -> VG.length c <= k) (snd nae'))
          QC..&&.
          (forAllAssignments (fst nae) $ \m ->
             evalNAESAT m nae === evalNAESAT (transformForward info m) nae')

prop_naesat2naeksat_backward :: Property
prop_naesat2naeksat_backward =
  forAll arbitraryNAESAT $ \nae ->
  forAll (choose (3,10)) $ \k ->
    let ret@(nae',info) = naesat2naeksat k nae
     in counterexample (show ret) $
          forAll (arbitraryAssignment (fst nae')) $ \m ->
            evalNAESAT (transformBackward info m) nae || not (evalNAESAT m nae')

prop_naesat2maxcut_forward :: Property
prop_naesat2maxcut_forward =
  forAll arbitraryNAESAT $ \nae ->
    let ret@((maxcut, threshold), info) = naesat2maxcut nae
     in counterexample (show ret) $
          forAllAssignments (fst nae) $ \m ->
            evalNAESAT m nae === (MaxCut.eval (transformForward info m) maxcut >= threshold)

prop_naesat2max2sat_forward :: Property
prop_naesat2max2sat_forward =
  forAll arbitraryNAESAT $ \nae ->
    let ret@((wcnf, threshold), info) = naesat2max2sat nae
     in counterexample (show ret) $
          forAllAssignments (fst nae) $ \m ->
            case evalWCNF (transformForward info m) wcnf of
              Nothing -> property False
              Just v -> evalNAESAT m nae === (v <= threshold)

------------------------------------------------------------------------

prop_satToMaxSAT2_forward :: Property
prop_satToMaxSAT2_forward =
  forAll arbitraryCNF $ \cnf ->
    let ((wcnf, threshold), info) = satToMaxSAT2 cnf
    in and
       [ evalCNF m cnf == b2
       | m <- allAssignments (CNF.cnfNumVars cnf)
       , let m2 = transformForward info m
             b2 = case evalWCNF m2 wcnf of
                    Nothing -> False
                    Just v -> v <= threshold
       ]

prop_simplifyMaxSAT2_forward :: Property
prop_simplifyMaxSAT2_forward =
  forAll arbitraryMaxSAT2 $ \(wcnf, th1) ->
    let r@((_n,cs,th2), info) = simplifyMaxSAT2 (wcnf, th1)
    in counterexample (show r) $ and
       [ b1 == b2
       | m1 <- allAssignments (CNF.wcnfNumVars wcnf)
       , let o1 = fromJust $ evalWCNF m1 wcnf
             b1 = o1 <= th1
             m2 = transformForward info m1
             o2 = fromIntegral $ length [()| (l1,l2) <- Set.toList cs, not (SAT.evalLit m2 l1), not (SAT.evalLit m2 l2)]
             b2 = o2 <= th2
       ]

prop_maxSAT2ToSimpleMaxCut_forward :: Property
prop_maxSAT2ToSimpleMaxCut_forward =
  forAll arbitraryMaxSAT2 $ \(wcnf, th1) ->
    let r@((maxcut, th2), info) = maxSAT2ToSimpleMaxCut (wcnf, th1)
    in counterexample (show r) $ and
       [ b1 == b2
       | m <- allAssignments (CNF.wcnfNumVars wcnf)
       , let o1 = fromJust $ evalWCNF m wcnf
             b1 = o1 <= th1
             sol2 = transformForward info m
             o2 = MaxCut.eval sol2 maxcut
             b2 = o2 >= th2
       ]

------------------------------------------------------------------------

prop_pb2sat :: Property
prop_pb2sat = QM.monadicIO $ do
  pb@(nv,cs) <- QM.pick arbitraryPB
  let f (PBRelGE,lhs,rhs) = ([(c,[l]) | (c,l) <- lhs], PBFile.Ge, rhs)
      f (PBRelLE,lhs,rhs) = ([(-c,[l]) | (c,l) <- lhs], PBFile.Ge, -rhs)
      f (PBRelEQ,lhs,rhs) = ([(c,[l]) | (c,l) <- lhs], PBFile.Eq, rhs)
  let opb = PBFile.Formula
            { PBFile.pbObjectiveFunction = Nothing
            , PBFile.pbNumVars = nv
            , PBFile.pbNumConstraints = length cs
            , PBFile.pbConstraints = map f cs
            }
  let (cnf, info) = pb2sat opb

  solver1 <- arbitrarySolver
  solver2 <- arbitrarySolver
  ret1 <- QM.run $ solvePB solver1 pb
  ret2 <- QM.run $ solveCNF solver2 cnf
  QM.assert $ isJust ret1 == isJust ret2
  case ret1 of
    Nothing -> return ()
    Just m1 -> do
      let m2 = transformForward info m1
      QM.assert $ bounds m2 == (1, CNF.cnfNumVars cnf)
      QM.assert $ evalCNF m2 cnf
  case ret2 of
    Nothing -> return ()
    Just m2 -> do
      let m1 = transformBackward info m2
      QM.assert $ bounds m1 == (1, nv)
      QM.assert $ evalPB m1 pb

prop_wbo2maxsat :: Property
prop_wbo2maxsat = QM.monadicIO $ do
  wbo1@(nv,cs,top) <- QM.pick arbitraryWBO
  let f (w,(PBRelGE,lhs,rhs)) = (w,([(c,[l]) | (c,l) <- lhs], PBFile.Ge, rhs))
      f (w,(PBRelLE,lhs,rhs)) = (w,([(-c,[l]) | (c,l) <- lhs], PBFile.Ge, -rhs))
      f (w,(PBRelEQ,lhs,rhs)) = (w,([(c,[l]) | (c,l) <- lhs], PBFile.Eq, rhs))
  let wbo1' = PBFile.SoftFormula
            { PBFile.wboNumVars = nv
            , PBFile.wboNumConstraints = length cs
            , PBFile.wboConstraints = map f cs
            , PBFile.wboTopCost = top
            }
  let (wcnf, info) = wbo2maxsat wbo1'
      wbo2 = ( CNF.wcnfNumVars wcnf
             , [ ( if w == CNF.wcnfTopCost wcnf then Nothing else Just w
                 , (PBRelGE, [(1,l) | l <- SAT.unpackClause clause], 1)
                 )
               | (w,clause) <- CNF.wcnfClauses wcnf
               ]
             , Nothing
             )

  solver1 <- arbitrarySolver
  solver2 <- arbitrarySolver
  method <- QM.pick arbitrary
  ret1 <- QM.run $ optimizeWBO solver1 method wbo1
  ret2 <- QM.run $ optimizeWBO solver2 method wbo2
  QM.assert $ isJust ret1 == isJust ret2
  case ret1 of
    Nothing -> return ()
    Just (m1,val) -> do
      let m2 = transformForward info m1
      QM.assert $ bounds m2 == (1, CNF.wcnfNumVars wcnf)
      QM.assert $ evalWBO m2 wbo2 == Just val
  case ret2 of
    Nothing -> return ()
    Just (m2,val) -> do
      let m1 = transformBackward info m2
      QM.assert $ bounds m1 == (1, nv)
      QM.assert $ evalWBO m1 wbo1 == Just val

prop_wbo2pb :: Property
prop_wbo2pb = QM.monadicIO $ do
  wbo@(nv,cs,top) <- QM.pick arbitraryWBO
  let f (w,(PBRelGE,lhs,rhs)) = (w,([(c,[l]) | (c,l) <- lhs], PBFile.Ge, rhs))
      f (w,(PBRelLE,lhs,rhs)) = (w,([(-c,[l]) | (c,l) <- lhs], PBFile.Ge, -rhs))
      f (w,(PBRelEQ,lhs,rhs)) = (w,([(c,[l]) | (c,l) <- lhs], PBFile.Eq, rhs))
  let wbo' = PBFile.SoftFormula
            { PBFile.wboNumVars = nv
            , PBFile.wboNumConstraints = length cs
            , PBFile.wboConstraints = map f cs
            , PBFile.wboTopCost = top
            }
  let (opb, info) = wbo2pb wbo'
      obj = fromMaybe [] $ PBFile.pbObjectiveFunction opb
      f (lhs, PBFile.Ge, rhs) = (PBRelGE, lhs, rhs)
      f (lhs, PBFile.Eq, rhs) = (PBRelEQ, lhs, rhs)
      cs2 = map f (PBFile.pbConstraints opb)
      pb = (PBFile.pbNumVars opb, obj, cs2)

  solver1 <- arbitrarySolver
  solver2 <- arbitrarySolver
  method <- QM.pick arbitrary
  ret1 <- QM.run $ optimizeWBO solver1 method wbo
  ret2 <- QM.run $ optimizePBNLC solver2 method pb
  QM.assert $ isJust ret1 == isJust ret2
  case ret1 of
    Nothing -> return ()
    Just (m1,val1) -> do
      let m2 = transformForward info m1
      QM.assert $ bounds m2 == (1, PBFile.pbNumVars opb)
      QM.assert $ evalPBNLC m2 (PBFile.pbNumVars opb, cs2)
      QM.assert $ SAT.evalPBSum m2 obj == val1
  case ret2 of
    Nothing -> return ()
    Just (m2,val2) -> do
      let m1 = transformBackward info m2
      QM.assert $ bounds m1 == (1,nv)
      QM.assert $ evalWBO m1 wbo == Just val2

prop_sat2ksat :: Property
prop_sat2ksat = QM.monadicIO $ do
  k <- QM.pick $ choose (3,10)

  cnf1 <- QM.pick arbitraryCNF
  let (cnf2, info) = sat2ksat k cnf1

  solver1 <- arbitrarySolver
  solver2 <- arbitrarySolver
  ret1 <- QM.run $ solveCNF solver1 cnf1
  ret2 <- QM.run $ solveCNF solver2 cnf2
  QM.assert $ isJust ret1 == isJust ret2
  case ret1 of
    Nothing -> return ()
    Just m1 -> do
      let m2 = transformForward info m1
      QM.assert $ bounds m2 == (1, CNF.cnfNumVars cnf2)
      QM.assert $ evalCNF m2 cnf2
  case ret2 of
    Nothing -> return ()
    Just m2 -> do
      let m1 = transformBackward info m2
      QM.assert $ bounds m1 == (1, CNF.cnfNumVars cnf1)
      QM.assert $ evalCNF m1 cnf1

prop_quadratizePB :: Property
prop_quadratizePB =
  forAll arbitraryPBFormula $ \pb ->
    let ((pb2,th), info) = quadratizePB pb
     in counterexample (show (pb2,th)) $
          conjoin
          [ property $ F.all (\t -> IntSet.size t <= 2) $ collectTerms pb2
          , property $ PBFile.pbNumConstraints pb === PBFile.pbNumConstraints pb2
          , forAll (arbitraryAssignment (PBFile.pbNumVars pb)) $ \m ->
              SAT.evalPBFormula m pb === eval2 (transformForward info m) (pb2,th)
          , forAll (arbitraryAssignment (PBFile.pbNumVars pb2)) $ \m ->
              case eval2 m (pb2,th) of
                Just o -> SAT.evalPBFormula (transformBackward info m) pb === Just o
                Nothing -> property True
          ]
  where        
    collectTerms :: PBFile.Formula -> Set IntSet
    collectTerms formula = Set.fromList [t' | t <- terms, let t' = IntSet.fromList t, IntSet.size t' >= 3]
      where
        sums = maybeToList (PBFile.pbObjectiveFunction formula) ++
               [lhs | (lhs,_,_) <- PBFile.pbConstraints formula]
        terms = [t | s <- sums, (_,t) <- s]

    eval2 :: SAT.IModel m => m -> (PBFile.Formula, Integer) -> Maybe Integer
    eval2 m (pb,th) = do
      o <- SAT.evalPBFormula m pb
      guard $ o <= th
      return o

prop_inequalitiesToEqualitiesPB :: Property
prop_inequalitiesToEqualitiesPB = QM.monadicIO $ do
  pb@(nv,cs) <- QM.pick arbitraryPBNLC
  let f (PBRelGE,lhs,rhs) = ([(c,ls) | (c,ls) <- lhs], PBFile.Ge, rhs)
      f (PBRelLE,lhs,rhs) = ([(-c,ls) | (c,ls) <- lhs], PBFile.Ge, -rhs)
      f (PBRelEQ,lhs,rhs) = ([(c,ls) | (c,ls) <- lhs], PBFile.Eq, rhs)
  let opb = PBFile.Formula
            { PBFile.pbObjectiveFunction = Nothing
            , PBFile.pbNumVars = nv
            , PBFile.pbNumConstraints = length cs
            , PBFile.pbConstraints = map f cs
            }
  QM.monitor $ counterexample (show opb)
  let (opb2, info) = inequalitiesToEqualitiesPB opb
      pb2 = (PBFile.pbNumVars opb2, [(g op, lhs, rhs) | (lhs,op,rhs) <- PBFile.pbConstraints opb2])
      g PBFile.Ge = PBRelGE
      g PBFile.Eq = PBRelEQ
  QM.monitor $ counterexample (show opb2)

  solver1 <- arbitrarySolver
  solver2 <- arbitrarySolver
  ret1 <- QM.run $ solvePBNLC solver1 pb
  ret2 <- QM.run $ solvePBNLC solver2 pb2
  QM.assert $ isJust ret1 == isJust ret2
  case ret1 of
    Nothing -> return ()
    Just m1 -> do
      let m2 = transformForward info m1
      QM.assert $ bounds m2 == (1, PBFile.pbNumVars opb2)
      QM.assert $ evalPBNLC m2 pb2
  case ret2 of
    Nothing -> return ()
    Just m2 -> do
      let m1 = transformBackward info m2
      QM.assert $ bounds m1 == (1, nv)
      QM.assert $ evalPBNLC m1 pb


converterTestGroup :: TestTree
converterTestGroup = $(testGroupGenerator)
