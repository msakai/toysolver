{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
module Test.Converter (converterTestGroup) where

import Control.Monad
import qualified Data.Aeson as J
import Data.Array.IArray
import qualified Data.Foldable as F
import Data.Map.Lazy (Map)
import qualified Data.Map.Lazy as Map
import Data.Maybe
import Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.IntMap.Strict as IntMap
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import Data.String
import qualified Data.Vector.Generic as VG
import qualified Numeric.Optimization.MIP as MIP

import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.QuickCheck hiding ((.&&.), (.||.))
import Test.Tasty.TH
import qualified Test.QuickCheck as QC
import qualified Test.QuickCheck.Monadic as QM

import ToySolver.Converter
import qualified ToySolver.FileFormat.CNF as CNF
import ToySolver.Graph.Base
import qualified ToySolver.Graph.MaxCut as MaxCut
import qualified ToySolver.SAT as SAT
import qualified ToySolver.SAT.Types as SAT

import qualified Data.PseudoBoolean as PBFile

import Test.SAT.Utils

------------------------------------------------------------------------

case_identity_transformer_json :: Assertion
case_identity_transformer_json = do
  let info :: IdentityTransformer SAT.Model
      info = IdentityTransformer
      json = J.encode info
  J.eitherDecode json @?= Right info

case_reversed_transformer_json :: Assertion
case_reversed_transformer_json = do
  let info :: ReversedTransformer (IdentityTransformer SAT.Model)
      info = ReversedTransformer IdentityTransformer
      json = J.encode info
  J.eitherDecode json @?= Right info

------------------------------------------------------------------------

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

prop_sat2naesat_json :: Property
prop_sat2naesat_json = forAll arbitraryCNF $ \cnf ->
  let ret@(_,info) = sat2naesat cnf
      json = J.encode info
   in counterexample (show ret) $ counterexample (show json) $
        J.eitherDecode json === Right info

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

prop_naesat2sat_json :: Property
prop_naesat2sat_json = forAll arbitraryNAESAT $ \nae ->
  let ret@(_,info) = naesat2sat nae
      json = J.encode info
   in counterexample (show ret) $ counterexample (show json) $
        J.eitherDecode json === Right info

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

prop_naesat2naeksat_json :: Property
prop_naesat2naeksat_json =
  forAll arbitraryNAESAT $ \nae ->
  forAll (choose (3,10)) $ \k ->
    let ret@(_,info) = naesat2naeksat k nae
        json = J.encode info
     in counterexample (show ret) $ counterexample (show json) $
          J.eitherDecode json === Right info

prop_naesat2maxcut_forward :: Property
prop_naesat2maxcut_forward =
  forAll arbitraryNAESAT $ \nae ->
    let ret@((maxcut, threshold), info) = naesat2maxcut nae
     in counterexample (show ret) $
          forAllAssignments (fst nae) $ \m ->
            evalNAESAT m nae === (MaxCut.eval (transformForward info m) maxcut >= threshold)

prop_naesat2maxcut_backward :: Property
prop_naesat2maxcut_backward = forAll arbitraryNAESAT $ \nae ->
  let ret@((g, threshold),info) = naesat2maxcut nae
   in counterexample (show ret) $
        forAll (arbitraryCut g) $ \cut ->
          if MaxCut.eval cut g >= threshold then
            evalNAESAT (transformBackward info cut) nae
          else
            True

prop_naesat2maxcut_json :: Property
prop_naesat2maxcut_json =
  forAll arbitraryNAESAT $ \nae ->
    let ret@(_, info) = naesat2maxcut nae
        json = J.encode info
     in counterexample (show ret) $ counterexample (show json) $
          J.eitherDecode json === Right info

prop_naesat2max2sat_forward :: Property
prop_naesat2max2sat_forward =
  forAll arbitraryNAESAT $ \nae ->
    let ret@((wcnf, threshold), info) = naesat2max2sat nae
     in counterexample (show ret) $
          forAllAssignments (fst nae) $ \m ->
            case evalWCNF (transformForward info m) wcnf of
              Nothing -> property False
              Just v -> evalNAESAT m nae === (v <= threshold)

prop_naesat2max2sat_backward :: Property
prop_naesat2max2sat_backward =
  forAll arbitraryNAESAT $ \nae ->
    let ret@((wcnf, threshold), info) = naesat2max2sat nae
     in counterexample (show ret) $
          forAll (arbitraryAssignment (CNF.wcnfNumVars wcnf)) $ \m ->
            case evalWCNF m wcnf of
              Just v | v <= threshold -> evalNAESAT (transformBackward info m) nae
              _ -> True

prop_naesat2max2sat_json :: Property
prop_naesat2max2sat_json =
  forAll arbitraryNAESAT $ \nae ->
    let ret@(_, info) = naesat2max2sat nae
        json = J.encode info
     in counterexample (show ret) $ counterexample (show json) $
          J.eitherDecode json === Right info

prop_sat2maxcut_forward :: Property
prop_sat2maxcut_forward =
  forAll arbitraryCNF $ \cnf ->
    let ret@((g, threshold), info) = sat2maxcut cnf
     in counterexample (show ret) $
          forAllAssignments (CNF.cnfNumVars cnf) $ \m ->
            evalCNF m cnf === (MaxCut.eval (transformForward info m) g >= threshold)

prop_sat2maxcut_backward :: Property
prop_sat2maxcut_backward = forAll arbitraryCNF $ \cnf ->
  let ret@((g, threshold),info) = sat2maxcut cnf
   in counterexample (show ret) $
        forAll (arbitraryCut g) $ \cut ->
          if MaxCut.eval cut g >= threshold then
            -- TODO: maybe it's difficult to come here
            evalCNF (transformBackward info cut) cnf
          else
            True

prop_sat2maxcut_json :: Property
prop_sat2maxcut_json =
  forAll arbitraryCNF $ \cnf ->
    let ret@(_, info) = sat2maxcut cnf
        json = J.encode info
     in counterexample (show ret) $ counterexample (show json) $
          J.eitherDecode json === Right info

arbitraryCut :: MaxCut.Problem a -> Gen MaxCut.Solution
arbitraryCut g = do
  let b = bounds g
  xs <- replicateM (rangeSize b) arbitrary
  return $ array b (zip (range b) xs)

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

prop_satToMaxSAT2_json :: Property
prop_satToMaxSAT2_json =
  forAll arbitraryCNF $ \cnf ->
    let ret@(_, info) = satToMaxSAT2 cnf
        json = J.encode info
     in counterexample (show ret) $ counterexample (show json) $
          J.eitherDecode json === Right info

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

prop_simplifyMaxSAT2_json :: Property
prop_simplifyMaxSAT2_json =
  forAll arbitraryMaxSAT2 $ \(wcnf, th1) ->
    let ret@(_, info) = simplifyMaxSAT2 (wcnf, th1)
        json = J.encode info
     in counterexample (show ret) $ counterexample (show json) $
          J.eitherDecode json === Right info

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

prop_maxSAT2ToSimpleMaxCut_backward :: Property
prop_maxSAT2ToSimpleMaxCut_backward =
  forAll arbitraryMaxSAT2 $ \(wcnf, th1) ->
    let r@((g, th2), info) = maxSAT2ToSimpleMaxCut (wcnf, th1)
    in counterexample (show r) $
        forAll (arbitraryCut g) $ \cut ->
          if MaxCut.eval cut g >= th2 then
            case evalWCNF (transformBackward info cut) wcnf of
              Nothing -> False
              Just v -> v <= th1
          else
            True

prop_maxSAT2ToSimpleMaxCut_json :: Property
prop_maxSAT2ToSimpleMaxCut_json =
  forAll arbitraryMaxSAT2 $ \(wcnf, th1) ->
    let ret@(_, info) = maxSAT2ToSimpleMaxCut (wcnf, th1)
        json = J.encode info
     in counterexample (show ret) $ counterexample (show json) $
          J.eitherDecode json === Right info

-- -- Too Slow
-- prop_satToSimpleMaxCut_forward :: Property
-- prop_satToSimpleMaxCut_forward =
--   forAll arbitraryCNF $ \cnf ->
--     let ret@((g, threshold), info) = satToSimpleMaxCut cnf
--      in counterexample (show ret) $
--           forAllAssignments (CNF.cnfNumVars cnf) $ \m ->
--             evalCNF m cnf === (MaxCut.eval (transformForward info m) g >= threshold)

-- -- Too Slow
-- prop_satToSimpleMaxCut_backward :: Property
-- prop_satToSimpleMaxCut_backward = forAll arbitraryCNF $ \cnf ->
--   let ret@((g, threshold),info) = satToSimpleMaxCut cnf
--    in counterexample (show ret) $
--         forAll (arbitraryCut g) $ \cut ->
--           if MaxCut.eval cut g >= threshold then
--             evalCNF (transformBackward info cut) cnf
--           else
--             True

prop_satToSimpleMaxCut_json :: Property
prop_satToSimpleMaxCut_json =
  forAll arbitraryCNF $ \cnf ->
    let ret@(_, info) = satToSimpleMaxCut cnf
        json = J.encode info
     in counterexample (show ret) $ counterexample (show json) $
          J.eitherDecode json === Right info

------------------------------------------------------------------------

prop_satToIS_forward :: Property
prop_satToIS_forward =
  forAll arbitraryCNF $ \cnf -> do
    let r@((g,k), info) = satToIS cnf
     in counterexample (show r) $ conjoin
        [ counterexample (show m) $ counterexample (show set) $
            not (evalCNF m cnf) || (set `isIndependentSetOf` g  && IntSet.size set >= k)
        | m <- allAssignments (CNF.cnfNumVars cnf)
        , let set = transformForward info m
        ]

prop_satToIS_backward :: Property
prop_satToIS_backward =
  forAll arbitraryCNF $ \cnf -> do
    let r@((g,k), info) = satToIS cnf
     in counterexample (show r) $
          forAll (oneof [arbitraryIndependentSet g, arbitraryIndependentSet' g k]) $ \set -> do
            let m = transformBackward info set
             in counterexample (show m) $
                  not (IntSet.size set >= k) || evalCNF m cnf

prop_satToIS_json :: Property
prop_satToIS_json =
  forAll arbitraryCNF $ \cnf -> do
    let r@(_, info) = satToIS cnf
        json = J.encode info
     in counterexample (show r) $ counterexample (show json) $
          J.eitherDecode json === Right info

prop_mis2MaxSAT_forward :: Property
prop_mis2MaxSAT_forward =
  forAll arbitraryGraph $ \g -> do
    let r@(wcnf, info) = mis2MaxSAT g
     in counterexample (show r) $ conjoin
        [ counterexample (show set) $ counterexample (show m) $ o1 === o2
        | set <- map IntSet.fromList $ allSubsets $ range $ bounds g
        , let m = transformForward info set
              o1 = if set `isIndependentSetOf` g
                   then Just (transformObjValueForward info (IntSet.size set))
                   else Nothing
              o2 = evalWCNF m wcnf
        ]
  where
    allSubsets :: [a] -> [[a]]
    allSubsets = filterM (const [False, True])

prop_mis2MaxSAT_backward :: Property
prop_mis2MaxSAT_backward =
  forAll arbitraryGraph $ \g -> do
    let r@(wcnf, info) = mis2MaxSAT g
     in counterexample (show r) $ conjoin
        [ counterexample (show m) $ counterexample (show set) $ o1 === o2
        | m <- allAssignments (CNF.wcnfNumVars wcnf)
        , let set = transformBackward info m
              o1 = if set `isIndependentSetOf` g
                   then Just (IntSet.size set)
                   else Nothing
              o2 = fmap (transformObjValueBackward info) $ evalWCNF m wcnf
        ]

prop_mis2MaxSAT_json :: Property
prop_mis2MaxSAT_json =
  forAll arbitraryGraph $ \g -> do
    let r@(_, info) = mis2MaxSAT g
        json = J.encode info
     in counterexample (show r) $ counterexample (show json) $
          J.eitherDecode json === Right info

prop_is2pb_forward :: Property
prop_is2pb_forward =
  forAll arbitraryGraph $ \g ->
  forAll arbitrary $ \(Positive k) ->
    let ret@(opb,info) = is2pb (g, k)
     in counterexample (show ret) $ conjoin
        [ counterexample (show set) $ counterexample (show m) $ o1 === o2
        | set <- map IntSet.fromList $ allSubsets $ range $ bounds g
        , let m = transformForward info set
              o1 = set `isIndependentSetOf` g && IntSet.size set >= k
              o2 = isJust $ SAT.evalPBFormula m opb
        ]
  where
    allSubsets :: [a] -> [[a]]
    allSubsets = filterM (const [False, True])

prop_is2pb_backward :: Property
prop_is2pb_backward =
  forAll arbitraryGraph $ \g ->
  forAll arbitrary $ \(Positive k) ->
    let ret@(opb,info) = is2pb (g, k)
     in counterexample (show ret) $ conjoin
        [ counterexample (show m) $ counterexample (show set) $ o1 === o2
        | m <- allAssignments (PBFile.pbNumVars opb)
        , let set = transformBackward info m
              o1 = set `isIndependentSetOf` g && IntSet.size set >= k
              o2 = isJust $ SAT.evalPBFormula m opb
        ]

prop_is2pb_json :: Property
prop_is2pb_json =
  forAll arbitraryGraph $ \g ->
  forAll arbitrary $ \(Positive k) ->
    let ret@(_,info) = is2pb (g, k)
        json = J.encode info
     in counterexample (show ret) $ counterexample (show json) $
          J.eitherDecode json === Right info

arbitraryGraph :: Gen Graph
arbitraryGraph = do
  n <- choose (0, 8) -- inclusive range
  es <- liftM concat $ forM [0..n-1] $ \v1 -> do
    vs <- sublistOf [0..n-1]
    return [(v1, v2, ()) | v2 <- vs]
  return $ graphFromUnorderedEdges n es

arbitraryIndependentSet :: Graph -> Gen IntSet
arbitraryIndependentSet g = do
  s <- arbitraryMaximalIndependentSet g
  liftM IntSet.fromList $ sublistOf $ IntSet.toList s

arbitraryIndependentSet' :: Graph -> Int -> Gen IntSet
arbitraryIndependentSet' g k = go IntSet.empty (IntSet.fromList (range (bounds g)))
  where
    go s c
      | IntSet.size s >= k = return s
      | IntSet.null c = return s
      | otherwise = do
          a <- elements (IntSet.toList c)
          go (IntSet.insert a s) (IntSet.delete a c IntSet.\\ (IntMap.keysSet (g ! a)))

arbitraryMaximalIndependentSet :: Graph -> Gen IntSet
arbitraryMaximalIndependentSet g = go IntSet.empty (IntSet.fromList (range (bounds g)))
  where
    go s c
      | IntSet.null c = return s
      | otherwise = do
          a <- elements (IntSet.toList c)
          go (IntSet.insert a s) (IntSet.delete a c IntSet.\\ (IntMap.keysSet (g ! a)))

------------------------------------------------------------------------

prop_sat2pb_forward :: Property
prop_sat2pb_forward = forAll arbitraryCNF $ \cnf ->
  let ret@(opb,info) = sat2pb cnf
   in counterexample (show ret) $
        forAllAssignments (CNF.cnfNumVars cnf) $ \m ->
          evalCNF m cnf === isJust (SAT.evalPBFormula (transformForward info m) opb)

prop_sat2pb_backward :: Property
prop_sat2pb_backward = forAll arbitraryCNF $ \cnf ->
  let ret@(opb,info) = sat2pb cnf
   in counterexample (show ret) $
        forAllAssignments (PBFile.pbNumVars opb) $ \m ->
          evalCNF (transformBackward info m) cnf === isJust (SAT.evalPBFormula m opb)

prop_sat2pb_json :: Property
prop_sat2pb_json = forAll arbitraryCNF $ \cnf ->
  let ret@(_,info) = sat2pb cnf
      json = J.encode info
   in counterexample (show ret) $ counterexample (show json) $
        J.eitherDecode json === Right info

prop_maxsat2wbo_forward :: Property
prop_maxsat2wbo_forward = forAll arbitraryWCNF $ \cnf ->
  let ret@(wbo,info) = maxsat2wbo cnf
   in counterexample (show ret) $
        forAllAssignments (CNF.wcnfNumVars cnf) $ \m ->
          fmap (transformObjValueForward info) (evalWCNF m cnf) === SAT.evalPBSoftFormula (transformForward info m) wbo

prop_maxsat2wbo_backward :: Property
prop_maxsat2wbo_backward = forAll arbitraryWCNF $ \cnf ->
  let ret@(wbo,info) = maxsat2wbo cnf
   in counterexample (show ret) $
        forAllAssignments (PBFile.wboNumVars wbo) $ \m ->
          evalWCNF (transformBackward info m) cnf === fmap (transformObjValueBackward info) (SAT.evalPBSoftFormula m wbo)

prop_maxsat2wbo_json :: Property
prop_maxsat2wbo_json = forAll arbitraryWCNF $ \cnf ->
  let ret@(_,info) = maxsat2wbo cnf
      json = J.encode info
   in counterexample (show ret) $ counterexample (show json) $
        J.eitherDecode json === Right info

prop_pb2sat :: Property
prop_pb2sat = QM.monadicIO $ do
  opb <- QM.pick arbitraryPBFormula

  strategy <- QM.pick arbitrary
  let (cnf, info) = pb2satWith strategy opb

  solver1 <- arbitrarySolver
  solver2 <- arbitrarySolver
  ret1 <- QM.run $ solvePBFormula solver1 opb
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
      QM.assert $ bounds m1 == (1, PBFile.pbNumVars opb)
      QM.assert $ isJust $ SAT.evalPBFormula m1 opb

prop_pb2sat_json :: Property
prop_pb2sat_json =
  forAll arbitraryPBFormula $ \opb ->
  forAll arbitrary $ \strategy ->
    let ret@(_, info) = pb2satWith strategy opb
        json = J.encode info
     in counterexample (show ret) $ counterexample (show json) $
        J.eitherDecode json === Right info

prop_wbo2maxsat :: Property
prop_wbo2maxsat = QM.monadicIO $ do
  wbo <- QM.pick arbitraryPBSoftFormula
  let (wcnf, info) = wbo2maxsat wbo

  solver1 <- arbitrarySolver
  solver2 <- arbitrarySolver
  method <- QM.pick arbitrary
  ret1 <- QM.run $ optimizePBSoftFormula solver1 method wbo
  ret2 <- QM.run $ optimizeWCNF solver2 method wcnf
  QM.assert $ isJust ret1 == isJust ret2
  case ret1 of
    Nothing -> return ()
    Just (m1,val) -> do
      let m2 = transformForward info m1
      QM.assert $ bounds m2 == (1, CNF.wcnfNumVars wcnf)
      QM.assert $ evalWCNF m2 wcnf == Just (transformObjValueForward info val)
  case ret2 of
    Nothing -> return ()
    Just (m2,val) -> do
      let m1 = transformBackward info m2
      QM.assert $ bounds m1 == (1, PBFile.wboNumVars wbo)
      QM.assert $ SAT.evalPBSoftFormula m1 wbo == Just (transformObjValueBackward info val)

prop_wbo2maxsat_json :: Property
prop_wbo2maxsat_json =
  forAll arbitraryPBSoftFormula $ \wbo ->
    let ret@(_, info) = wbo2maxsat wbo
        json = J.encode info
     in counterexample (show ret) $ counterexample (show json) $
        J.eitherDecode json === Right info

prop_pb2wbo :: Property
prop_pb2wbo = QM.monadicIO $ do
  opb <- QM.pick arbitraryPBFormula
  let (wbo, info) = pb2wbo opb
  QM.monitor $ counterexample (show wbo)

  solver1 <- arbitrarySolver
  solver2 <- arbitrarySolver
  method <- QM.pick arbitrary
  ret1 <- QM.run $ optimizePBFormula solver2 method opb
  ret2 <- QM.run $ optimizePBSoftFormula solver1 method wbo
  QM.monitor $ counterexample (show ret1)
  QM.monitor $ counterexample (show ret2)
  QM.assert $ isJust ret1 == isJust ret2
  case ret1 of
    Nothing -> return ()
    Just (m1,val1) -> do
      let m2 = transformForward info m1
      QM.assert $ bounds m2 == (1, PBFile.wboNumVars wbo)
      QM.assert $ SAT.evalPBSoftFormula m2 wbo == Just (transformObjValueForward info val1)
  case ret2 of
    Nothing -> return ()
    Just (m2,val2) -> do
      let m1 = transformBackward info m2
      QM.assert $ bounds m1 == (1, PBFile.wboNumVars wbo)
      QM.assert $ SAT.evalPBFormula m1 opb == Just (transformObjValueBackward info val2)

prop_pb2wbo_json :: Property
prop_pb2wbo_json =
  forAll arbitraryPBFormula $ \opb ->
    let ret@(_, info) = pb2wbo opb
        json = J.encode info
     in counterexample (show ret) $ counterexample (show json) $
        J.eitherDecode json === Right info

prop_wbo2pb :: Property
prop_wbo2pb = QM.monadicIO $ do
  wbo <- QM.pick arbitraryPBSoftFormula
  let (opb, info) = wbo2pb wbo
  QM.monitor $ counterexample (show opb)

  solver1 <- arbitrarySolver
  solver2 <- arbitrarySolver
  method <- QM.pick arbitrary
  ret1 <- QM.run $ optimizePBSoftFormula solver1 method wbo
  ret2 <- QM.run $ optimizePBFormula solver2 method opb
  QM.monitor $ counterexample (show ret1)
  QM.monitor $ counterexample (show ret2)
  QM.assert $ isJust ret1 == isJust ret2
  case ret1 of
    Nothing -> return ()
    Just (m1,val1) -> do
      let m2 = transformForward info m1
      QM.assert $ bounds m2 == (1, PBFile.pbNumVars opb)
      QM.assert $ SAT.evalPBFormula m2 opb == Just (transformObjValueForward info val1)
  case ret2 of
    Nothing -> return ()
    Just (m2,val2) -> do
      let m1 = transformBackward info m2
      QM.assert $ bounds m1 == (1, PBFile.wboNumVars wbo)
      QM.assert $ SAT.evalPBSoftFormula m1 wbo == Just (transformObjValueBackward info val2)

prop_wbo2pb_json :: Property
prop_wbo2pb_json =
  forAll arbitraryPBSoftFormula $ \wbo ->
    let ret@(_, info) = wbo2pb wbo
        json = J.encode info
     in counterexample (show ret) $ counterexample (show json) $
        J.eitherDecode json === Right info

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

prop_sat2ksat_json :: Property
prop_sat2ksat_json =
  forAll (choose (3,10)) $ \k ->
  forAll arbitraryCNF $ \cnf1 ->
    let ret@(_, info) = sat2ksat k cnf1
        json = J.encode info
     in counterexample (show ret) $ counterexample (show json) $
        J.eitherDecode json === Right info

prop_linearizePB_forward :: Property
prop_linearizePB_forward =
  forAll arbitraryPBFormula $ \pb ->
  forAll arbitrary $ \b ->
    let ret@(pb2, info) = linearizePB pb b
     in counterexample (show ret) $
        forAllAssignments (PBFile.pbNumVars pb) $ \m ->
          fmap (transformObjValueForward info) (SAT.evalPBFormula m pb) === SAT.evalPBFormula (transformForward info m) pb2

prop_linearizePB_backward :: Property
prop_linearizePB_backward =
  forAll arbitraryPBFormula $ \pb ->
  forAll arbitrary $ \b ->
    let ret@(pb2, info) = linearizePB pb b
     in counterexample (show ret) $
        forAll (arbitraryAssignment (PBFile.pbNumVars pb2)) $ \m2 ->
          case (SAT.evalPBFormula (transformBackward info m2) pb, SAT.evalPBFormula m2 pb2) of
            pair@(Just val1, Just val2) -> counterexample (show pair) $ val1 <= transformObjValueBackward info val2
            pair@(Nothing, Just _) -> counterexample (show pair) $ False
            (_, Nothing) -> property True

prop_linearizePB_json :: Property
prop_linearizePB_json =
  forAll arbitraryPBFormula $ \pb ->
  forAll arbitrary $ \b ->
    let ret@(_, info) = linearizePB pb b
        json = J.encode info
     in counterexample (show ret) $ counterexample (show json) $
        J.eitherDecode json === Right info

prop_linearizeWBO_forward :: Property
prop_linearizeWBO_forward =
  forAll arbitraryPBSoftFormula $ \wbo ->
  forAll arbitrary $ \b ->
    let ret@(wbo2, info) = linearizeWBO wbo b
     in counterexample (show ret) $
        forAllAssignments (PBFile.wboNumVars wbo) $ \m ->
          fmap (transformObjValueForward info) (SAT.evalPBSoftFormula m wbo) === SAT.evalPBSoftFormula (transformForward info m) wbo2

prop_linearizeWBO_backward :: Property
prop_linearizeWBO_backward =
  forAll arbitraryPBSoftFormula $ \wbo ->
  forAll arbitrary $ \b ->
    let ret@(wbo2, info) = linearizeWBO wbo b
     in counterexample (show ret) $
        forAll (arbitraryAssignment (PBFile.wboNumVars wbo2)) $ \m2 ->
          case (SAT.evalPBSoftFormula (transformBackward info m2) wbo, SAT.evalPBSoftFormula m2 wbo2) of
            pair@(Just val1, Just val2) -> counterexample (show pair) $ val1 <= transformObjValueBackward info val2
            pair@(Nothing, Just _) -> counterexample (show pair) $ False
            (_, Nothing) -> property True

prop_linearizeWBO_json :: Property
prop_linearizeWBO_json =
  forAll arbitraryPBSoftFormula $ \wbo ->
  forAll arbitrary $ \b ->
    let ret@(_, info) = linearizeWBO wbo b
        json = J.encode info
     in counterexample (show ret) $ counterexample (show json) $
        J.eitherDecode json === Right info

prop_quadratizePB :: Property
prop_quadratizePB =
  forAll arbitraryPBFormula $ \pb ->
    let ((pb2,th), info) = quadratizePB pb
     in counterexample (show (pb2,th)) $
          conjoin
          [ property $ F.all (\t -> IntSet.size t <= 2) $ collectTerms pb2
          , property $ PBFile.pbNumConstraints pb === PBFile.pbNumConstraints pb2
          , forAll (arbitraryAssignment (PBFile.pbNumVars pb)) $ \m ->
              fmap (transformObjValueForward info) (SAT.evalPBFormula m pb) === eval2 (transformForward info m) (pb2,th)
          , forAll (arbitraryAssignment (PBFile.pbNumVars pb2)) $ \m ->
              case eval2 m (pb2,th) of
                Just o -> SAT.evalPBFormula (transformBackward info m) pb === Just (transformObjValueBackward info o)
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

prop_quadratizePB_json :: Property
prop_quadratizePB_json =
  forAll arbitraryPBFormula $ \pb ->
    let ret@(_, info) = quadratizePB pb
        json = J.encode info
     in counterexample (show ret) $ counterexample (show json) $
          J.eitherDecode json === Right info

prop_inequalitiesToEqualitiesPB :: Property
prop_inequalitiesToEqualitiesPB = QM.monadicIO $ do
  opb <- QM.pick arbitraryPBFormula
  let (opb2, info) = inequalitiesToEqualitiesPB opb

  solver1 <- arbitrarySolver
  solver2 <- arbitrarySolver
  ret1 <- QM.run $ solvePBFormula solver1 opb
  ret2 <- QM.run $ solvePBFormula solver2 opb2
  QM.assert $ isJust ret1 == isJust ret2
  case ret1 of
    Nothing -> return ()
    Just m1 -> do
      let m2 = transformForward info m1
      QM.assert $ bounds m2 == (1, PBFile.pbNumVars opb2)
      QM.assert $ isJust $ SAT.evalPBFormula m2 opb2
  case ret2 of
    Nothing -> return ()
    Just m2 -> do
      let m1 = transformBackward info m2
      QM.assert $ bounds m1 == (1, PBFile.pbNumVars opb)
      QM.assert $ isJust $ SAT.evalPBFormula m1 opb

case_inequalitiesToEqualitiesPB_taut :: Assertion
case_inequalitiesToEqualitiesPB_taut = PBFile.pbNumConstraints opb2 @?= 0
  where
    opb =
      PBFile.Formula
      { PBFile.pbObjectiveFunction = Nothing
      , PBFile.pbConstraints = [([(1,[1]), (1,[])], PBFile.Ge, 0)] -- x1 + 1 >= 0
      , PBFile.pbNumVars = 1
      , PBFile.pbNumConstraints = 1
      }
    (opb2, _info) = inequalitiesToEqualitiesPB opb

case_inequalitiesToEqualitiesPB_num_surplus_vars :: Assertion
case_inequalitiesToEqualitiesPB_num_surplus_vars = (PBFile.pbNumVars opb2 @?= 3+2)
  where
    opb =
      PBFile.Formula
      { PBFile.pbObjectiveFunction = Nothing
      , PBFile.pbConstraints = [([(4,[1]), (4,[2]), (6,[3])], PBFile.Ge, 8)] -- 4 x1 + 4 x2 + 6 x3 >= 8
      , PBFile.pbNumVars = 3
      , PBFile.pbNumConstraints = 1
      }
    (opb2, _info) = inequalitiesToEqualitiesPB opb

prop_inequalitiesToEqualitiesPB_json :: Property
prop_inequalitiesToEqualitiesPB_json = forAll arbitraryPBFormula $ \opb ->
  let ret@(_, info) = inequalitiesToEqualitiesPB opb
      json = J.encode info
   in counterexample (show ret) $ counterexample (show json) $
      J.eitherDecode json == Right info

prop_normalizePB :: Property
prop_normalizePB = QM.monadicIO $ do
  opb <- QM.pick arbitraryPBFormula
  let (opb2, info) = normalizePB opb
  QM.monitor $ counterexample (show opb2)

  QM.assert $
    PBFile.pbNumVars opb2 == PBFile.pbNumVars opb ||
    PBFile.pbNumVars opb2 == PBFile.pbNumVars opb + 1
  QM.assert $ and
    [ case t of
        (_, []) -> False
        (_, [l]) -> l > 0
        _ -> True
    | s <- maybeToList (PBFile.pbObjectiveFunction opb2) ++ [lhs | (lhs,_,_) <- PBFile.pbConstraints opb2]
    , t <- s
    ]

  solver1 <- arbitrarySolver
  solver2 <- arbitrarySolver
  ret1 <- QM.run $ solvePBFormula solver1 opb
  ret2 <- QM.run $ solvePBFormula solver2 opb2
  QM.assert $ isJust ret1 == isJust ret2
  case ret1 of
    Nothing -> return ()
    Just m1 -> do
      let m2 = transformForward info m1
      QM.assert $ bounds m2 == (1, PBFile.pbNumVars opb2)
      QM.assert $ isJust $ SAT.evalPBFormula m2 opb2
  case ret2 of
    Nothing -> return ()
    Just m2 -> do
      let m1 = transformBackward info m2
      QM.assert $ bounds m1 == (1, PBFile.pbNumVars opb)
      QM.assert $ isJust $ SAT.evalPBFormula m1 opb    

case_normalizePB_1 :: Assertion
case_normalizePB_1 = fst (normalizePB opb) @?= expected
  where
    opb =
      PBFile.Formula
      { PBFile.pbNumVars = 2
      , PBFile.pbNumConstraints = 1
      , PBFile.pbObjectiveFunction = Just [(1, [1,2]), (1, [-1]), (1, [])]
      , PBFile.pbConstraints =
          [ ([(1, [1,2]), (1, [-1]), (1, [])], PBFile.Ge, 2)
          ]
      }
    expected =
      PBFile.Formula
      { PBFile.pbNumVars = 3
      , PBFile.pbNumConstraints = 1
      , PBFile.pbObjectiveFunction = Just [(1, [1,2]), (-1, [1]), (2, [3])]
      , PBFile.pbConstraints =
          [ ([(1, [1,2]), (-1, [1])], PBFile.Ge, 0)
          , ([(1, [3])], PBFile.Ge, 1)
          ]
      }

case_normalizePB_2 :: Assertion
case_normalizePB_2 = fst (normalizePB opb) @?= expected
  where
    opb =
      PBFile.Formula
      { PBFile.pbNumVars = 2
      , PBFile.pbNumConstraints = 1
      , PBFile.pbObjectiveFunction = Just [(1, [1,2]), (1, [-1]), (1, [])]
      , PBFile.pbConstraints =
          [ ([(1, [1,2]), (1, [-1]), (1, [])], PBFile.Ge, 2)
          , ([(3, [2])], PBFile.Ge, 2)
          ]
      }
    expected =
      PBFile.Formula
      { PBFile.pbNumVars = 2
      , PBFile.pbNumConstraints = 1
      , PBFile.pbObjectiveFunction = Just [(1, [1,2]), (-1, [1]), (2, [2])]
      , PBFile.pbConstraints =
          [ ([(1, [1,2]), (-1, [1])], PBFile.Ge, 0)
          , ([(3, [2])], PBFile.Ge, 2)
          ]
      }

case_normalizePB_3 :: Assertion
case_normalizePB_3 = fst (normalizePB opb) @?= expected
  where
    opb =
      PBFile.Formula
      { PBFile.pbNumVars = 2
      , PBFile.pbNumConstraints = 1
      , PBFile.pbObjectiveFunction = Just [(1, [1,2]), (1, [-1]), (1, [])]
      , PBFile.pbConstraints =
          [ ([(1, [1,2]), (1, [-1]), (1, [])], PBFile.Ge, 2)
          , ([(-2, [-2])], PBFile.Ge, -1)
          ]
      }
    expected =
      PBFile.Formula
      { PBFile.pbNumVars = 2
      , PBFile.pbNumConstraints = 1
      , PBFile.pbObjectiveFunction = Just [(1, [1,2]), (-1, [1]), (2, [2])]
      , PBFile.pbConstraints =
          [ ([(1, [1,2]), (-1, [1])], PBFile.Ge, 0)
          , ([(2, [2])], PBFile.Ge, 1)
          ]
      }

------------------------------------------------------------------------

prop_pb2ip_forward :: Property
prop_pb2ip_forward =
  forAll arbitraryPBFormula $ \pb ->
    let ret@(mip, info) = pb2ip pb
     in counterexample (show ret) $
        forAll (arbitraryAssignment (PBFile.pbNumVars pb)) $ \m ->
          fmap (transformObjValueForward info) (SAT.evalPBFormula m pb)
          ===
          evalMIP (transformForward info m) (fmap fromIntegral mip)

prop_pb2ip_backward :: Property
prop_pb2ip_backward =
  forAll arbitraryPBFormula $ \pb ->
    let ret@(mip, info) = pb2ip pb
     in counterexample (show ret) $
        forAll (arbitraryAssignmentBinaryIP mip) $ \sol ->
          SAT.evalPBFormula (transformBackward info sol) pb
          ===
          fmap (transformObjValueBackward info) (evalMIP sol (fmap fromIntegral mip))

prop_pb2ip_json :: Property
prop_pb2ip_json =
  forAll arbitraryPBFormula $ \pb ->
    let ret@(_, info) = pb2ip pb
        json = J.encode info
     in counterexample (show ret) $ counterexample (show json) $
          J.eitherDecode json === Right info

prop_wbo2ip_forward :: Property
prop_wbo2ip_forward =
  forAll arbitraryPBSoftFormula $ \wbo ->
  forAll arbitrary $ \b ->
    let ret@(mip, info) = wbo2ip b wbo
     in counterexample (show ret) $
        forAll (arbitraryAssignment (PBFile.wboNumVars wbo)) $ \m ->
          fmap (transformObjValueForward info) (SAT.evalPBSoftFormula m wbo)
          ===
          evalMIP (transformForward info m) (fmap fromIntegral mip)

prop_wbo2ip_backward :: Property
prop_wbo2ip_backward =
  forAll arbitraryPBSoftFormula $ \wbo ->
  forAll arbitrary $ \b ->
    let ret@(mip, info) = wbo2ip b wbo
     in counterexample (show ret) $
        forAll (arbitraryAssignmentBinaryIP mip) $ \sol ->
          case evalMIP sol (fmap fromIntegral mip) of
            Nothing -> True
            Just val2 ->
              case SAT.evalPBSoftFormula (transformBackward info sol) wbo of
                Nothing -> False
                Just val1 -> val1 <= transformObjValueBackward info val2

prop_wbo2ip_json :: Property
prop_wbo2ip_json =
  forAll arbitraryPBSoftFormula $ \wbo ->
  forAll arbitrary $ \b ->
    let ret@(_, info) = wbo2ip b wbo
        json = J.encode info
     in counterexample (show ret) $ counterexample (show json) $
          J.eitherDecode json === Right info

prop_ip2pb_forward :: Property
prop_ip2pb_forward =
  forAll arbitraryBoundedIP $ \ip ->
    case ip2pb ip of
      Left err -> counterexample err $ property False
      Right ret@(pb, info) ->
        counterexample (show ret) $
          forAll (arbitraryAssignmentBoundedIP ip) $ \sol ->
            fmap (transformObjValueForward info) (evalMIP sol ip)
            ===
            SAT.evalPBFormula (transformForward info sol) pb

prop_ip2pb_backward :: Property
prop_ip2pb_backward =
  forAll arbitraryBoundedIP $ \ip ->
    case ip2pb ip of
      Left err -> counterexample err $ property False
      Right ret@(pb, info) ->
        counterexample (show ret) $
          forAll (arbitraryAssignment (PBFile.pbNumVars pb)) $ \m ->
            case SAT.evalPBFormula m pb of
              Nothing -> property True
              Just val -> evalMIP (transformBackward info m) ip === Just (transformObjValueBackward info val)

prop_ip2pb_backward' :: Property
prop_ip2pb_backward' =
  forAll arbitraryBoundedIP $ \ip ->
    case ip2pb ip of
      Left err -> counterexample err $ property False
      Right ret@(pb, info) ->
        counterexample (show ret) $
          QM.monadicIO $ do
            solver <- arbitrarySolver
            -- Using optimizePBFormula is too slow for using in QuickCheck
            ret2 <- QM.run $ solvePBFormula solver pb
            case ret2 of
              Nothing -> return ()
              Just m -> QM.assert $ isJust $ evalMIP (transformBackward info m) ip

prop_ip2pb_json :: Property
prop_ip2pb_json =
  forAll arbitraryBoundedIP $ \ip ->
    case ip2pb ip of
      Left err -> counterexample err $ property False
      Right ret@(_, info) ->
        let json = J.encode info
         in counterexample (show ret) $ counterexample (show json) $
              J.eitherDecode json === Right info

case_ip2pb_continuous_error :: Assertion
case_ip2pb_continuous_error =
  case ip2pb prob of
    Left _ -> return ()
    Right _ -> assertFailure "should be error"
  where
    prob :: MIP.Problem Rational
    prob =
      MIP.def
      { MIP.constraints =
          [ MIP.def
            { MIP.constrExpr = MIP.varExpr "x"
            , MIP.constrLB = 1/2
            }
          ]
      , MIP.varDomains = Map.fromList [("x", (MIP.ContinuousVariable, (0, 1)))]
      }

case_ip2pb_semi_continuous_error :: Assertion
case_ip2pb_semi_continuous_error =
  case ip2pb prob of
    Left _ -> return ()
    Right _ -> assertFailure "should be error"
  where
    prob :: MIP.Problem Rational
    prob =
      MIP.def
      { MIP.constraints =
          [ MIP.def
            { MIP.constrExpr = MIP.varExpr "x"
            , MIP.constrUB = 50
            }
          ]
      , MIP.varDomains = Map.fromList [("x", (MIP.SemiContinuousVariable, (10, 100)))]
      }

case_ip2pb_unbounded_error_1 :: Assertion
case_ip2pb_unbounded_error_1 =
  case ip2pb prob of
    Left _ -> return ()
    Right _ -> assertFailure "should be error"
  where
    prob :: MIP.Problem Rational
    prob =
      MIP.def
      { MIP.constraints =
          [ MIP.def
            { MIP.constrExpr = MIP.varExpr "x"
            , MIP.constrUB = 50
            }
          ]
      , MIP.varDomains = Map.fromList [("x", (MIP.IntegerVariable, (0, MIP.PosInf)))]
      }

case_ip2pb_unbounded_error_2 :: Assertion
case_ip2pb_unbounded_error_2 =
  case ip2pb prob of
    Left _ -> return ()
    Right _ -> assertFailure "should be error"
  where
    prob :: MIP.Problem Rational
    prob =
      MIP.def
      { MIP.constraints =
          [ MIP.def
            { MIP.constrExpr = MIP.varExpr "x"
            , MIP.constrUB = -50
            }
          ]
      , MIP.varDomains = Map.fromList [("x", (MIP.IntegerVariable, (MIP.NegInf, 0)))]
      }

prop_normalizeMIPObjective :: Property
prop_normalizeMIPObjective =
  forAll arbitraryBoundedIP $ \prob ->
    let ret@(prob', _) = normalizeMIPObjective prob
     in counterexample (show ret) $
          all (\(MIP.Term _ vs) -> not (null vs)) (MIP.terms (MIP.objExpr (MIP.objectiveFunction prob')))

prop_normalizeMIPObjective_round_trip :: Property
prop_normalizeMIPObjective_round_trip =
  forAll arbitraryBoundedIP $ \prob ->
    let ret@(prob', info) = normalizeMIPObjective prob
     in counterexample (show ret) $
          forAll (arbitraryAssignmentBoundedIP prob) $ \sol ->
            let result1 = evalMIP sol prob
                result2 = evalMIP (transformForward info sol) prob'
                result3 = fmap (transformObjValueForward info) result1
                result4 = fmap (transformObjValueBackward info . transformObjValueForward info) result1
             in conjoin
                [ sol === transformBackward info (transformForward info sol)
                , result1 === result2
                , result1 === result3
                , result1 === result4
                ]

prop_normalizeMIPObjective_json :: Property
prop_normalizeMIPObjective_json =
  forAll arbitraryBoundedIP $ \prob ->
    let ret@(_, info) = normalizeMIPObjective prob
        json = J.encode info
     in counterexample (show ret) $ counterexample (show json) $
          J.eitherDecode json === Right info

arbitraryBoundedIP :: Gen (MIP.Problem Rational)
arbitraryBoundedIP = do
  nv <- choose (0,10)
  bs <- liftM Map.fromList $ forM [0..nv-1] $ \(i :: Int) -> do
    let v = fromString ("z" ++ show i)
    b <- arbitrary
    if b then
      pure (v, (MIP.IntegerVariable, (MIP.Finite 0, MIP.Finite 1)))
    else do
      lb <- arbitrary
      NonNegative w <- arbitrary
      let ub = fromInteger (ceiling lb) + w
      b2 <- arbitrary
      return (v, (if b2 then MIP.IntegerVariable else MIP.SemiIntegerVariable, (MIP.Finite lb, MIP.Finite ub)))

  let vs = Map.keys bs
      vs_bin = [v | (v, (MIP.IntegerVariable, (MIP.Finite 0, MIP.Finite 1))) <- Map.toList bs]

  dir <- elements [MIP.OptMin, MIP.OptMax]
  obj <- arbitraryMIPExpr vs

  nc <- choose (0,3)
  cs <- replicateM nc $ do
    ind <-
      if null vs_bin then
        pure Nothing
      else do
        b <- arbitrary
        if b then
          pure Nothing
        else do
          v <- elements vs_bin
          rhs <- elements [0, 1]
          pure $ Just (v, rhs)
    e <- arbitraryMIPExpr vs
    lb <- oneof [pure MIP.NegInf, MIP.Finite <$> arbitrary, pure MIP.PosInf]
    ub <- oneof $ [pure MIP.NegInf, MIP.Finite <$> arbitrary, pure MIP.PosInf] ++ [pure lb | case lb of{ MIP.Finite _ -> True; _ -> False }]
    isLazy <- arbitrary
    return $ MIP.def
      { MIP.constrIndicator = ind
      , MIP.constrExpr = e
      , MIP.constrLB = lb
      , MIP.constrUB = ub
      , MIP.constrIsLazy = isLazy
      }

  sos <-
    if length vs == 0 then
      pure []
    else do
      n <- choose (0, 1)
      replicateM n $ do
        t <- elements [MIP.S1, MIP.S2]
        m <- choose (0, length vs `div` 2)
        xs <- liftM (take m) $ shuffle vs
        ns <- shuffle (map fromIntegral [0 .. length xs - 1])
        pure (MIP.SOSConstraint{ MIP.sosLabel = Nothing, MIP.sosType = t, MIP.sosBody = zip xs ns })

  return $ MIP.def
    { MIP.objectiveFunction = MIP.def{ MIP.objDir = dir, MIP.objExpr = obj }
    , MIP.varDomains = bs
    , MIP.constraints = cs
    , MIP.sosConstraints = sos
    }

arbitraryMIPExpr :: [MIP.Var] -> Gen (MIP.Expr Rational)
arbitraryMIPExpr vs = do
  let nv = length vs
  nt <- choose (0,3)
  liftM MIP.Expr $ replicateM nt $ do
    ls <-
      if nv==0
      then return []
      else do
        m <- choose (0,2)
        replicateM m (elements vs)
    c <- arbitrary
    return $ MIP.Term c ls

arbitraryAssignmentBinaryIP :: MIP.Problem a -> Gen (Map MIP.Var Rational)
arbitraryAssignmentBinaryIP mip = liftM Map.fromList $ do
  forM (Map.keys (MIP.varTypes mip)) $ \v -> do
    val <- choose (0, 1)
    pure (v, fromInteger val)

arbitraryAssignmentBoundedIP :: RealFrac a => MIP.Problem a -> Gen (Map MIP.Var Rational)
arbitraryAssignmentBoundedIP mip = liftM Map.fromList $ do
  forM (Map.toList (MIP.varBounds mip)) $ \case
    (v, (MIP.Finite lb, MIP.Finite ub))  -> do
      val <- choose (ceiling lb, floor ub)
      pure (v, fromInteger val)
    _ -> error "should not happen"

evalMIP :: Map MIP.Var Rational -> MIP.Problem Rational -> Maybe Rational
evalMIP = MIP.eval MIP.zeroTol

------------------------------------------------------------------------

converterTestGroup :: TestTree
converterTestGroup = $(testGroupGenerator)
