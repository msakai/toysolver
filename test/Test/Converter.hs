{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
module Test.Converter (converterTestGroup) where

import Control.Monad
import qualified Data.Aeson as J
import Data.Array.IArray
import qualified Data.Foldable as F
import Data.List (sortBy)
import Data.Map.Lazy (Map)
import qualified Data.Map.Lazy as Map
import Data.Maybe
import Data.Ord (comparing)
import Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.IntMap.Strict as IntMap
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
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
          evalWCNF m cnf === SAT.evalPBSoftFormula (transformForward info m) wbo

prop_maxsat2wbo_backward :: Property
prop_maxsat2wbo_backward = forAll arbitraryWCNF $ \cnf ->
  let ret@(wbo,info) = maxsat2wbo cnf
   in counterexample (show ret) $
        forAllAssignments (PBFile.wboNumVars wbo) $ \m ->
          evalWCNF (transformBackward info m) cnf === SAT.evalPBSoftFormula m wbo

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
  wbo1 <- QM.pick arbitraryPBSoftFormula

  let (wcnf, info) = wbo2maxsat wbo1
      wbo2 = PBFile.SoftFormula
        { PBFile.wboNumVars = CNF.wcnfNumVars wcnf
        , PBFile.wboNumConstraints = CNF.wcnfNumClauses wcnf
        , PBFile.wboConstraints =
            [ ( if w == CNF.wcnfTopCost wcnf then Nothing else Just w
              , ([(1, [l]) | l <- SAT.unpackClause clause], PBFile.Ge, 1)
              )
            | (w,clause) <- CNF.wcnfClauses wcnf
            ]
        , PBFile.wboTopCost = Nothing
        }

  solver1 <- arbitrarySolver
  solver2 <- arbitrarySolver
  method <- QM.pick arbitrary
  ret1 <- QM.run $ optimizePBSoftFormula solver1 method wbo1
  ret2 <- QM.run $ optimizePBSoftFormula solver2 method wbo2
  QM.assert $ isJust ret1 == isJust ret2
  case ret1 of
    Nothing -> return ()
    Just (m1,val) -> do
      let m2 = transformForward info m1
      QM.assert $ bounds m2 == (1, CNF.wcnfNumVars wcnf)
      QM.assert $ SAT.evalPBSoftFormula m2 wbo2 == Just val
  case ret2 of
    Nothing -> return ()
    Just (m2,val) -> do
      let m1 = transformBackward info m2
      QM.assert $ bounds m1 == (1, PBFile.wboNumVars wbo1)
      QM.assert $ SAT.evalPBSoftFormula m1 wbo1 == Just val

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

  -- no constant terms in objective function
  QM.assert $ all (\(_,ls) -> length ls > 0) $ fromMaybe [] (PBFile.pbObjectiveFunction opb)

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
          SAT.evalPBFormula m pb === SAT.evalPBFormula (transformForward info m) pb2

prop_linearizePB_backward :: Property
prop_linearizePB_backward =
  forAll arbitraryPBFormula $ \pb ->
  forAll arbitrary $ \b ->
    let ret@(pb2, info) = linearizePB pb b
     in counterexample (show ret) $
        forAll (arbitraryAssignment (PBFile.pbNumVars pb2)) $ \m2 ->
          if isJust (SAT.evalPBFormula m2 pb2) then
            isJust (SAT.evalPBFormula (transformBackward info m2) pb)
          else
            True

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
          SAT.evalPBSoftFormula m wbo === SAT.evalPBSoftFormula (transformForward info m) wbo2

prop_linearizeWBO_backward :: Property
prop_linearizeWBO_backward =
  forAll arbitraryPBSoftFormula $ \wbo ->
  forAll arbitrary $ \b ->
    let ret@(wbo2, info) = linearizeWBO wbo b
     in counterexample (show ret) $
        forAll (arbitraryAssignment (PBFile.wboNumVars wbo2)) $ \m2 ->
          if isJust (SAT.evalPBSoftFormula m2 wbo2) then
            isJust (SAT.evalPBSoftFormula (transformBackward info m2) wbo)
          else
            True

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

prop_inequalitiesToEqualitiesPB_json :: Property
prop_inequalitiesToEqualitiesPB_json = forAll arbitraryPBFormula $ \opb ->
  let ret@(_, info) = inequalitiesToEqualitiesPB opb
      json = J.encode info
   in counterexample (show ret) $ counterexample (show json) $
      J.eitherDecode json == Right info

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
        forAll (arbitraryAssignments mip) $ \sol ->
          SAT.evalPBFormula (transformBackward info sol) pb
          ===
          fmap (transformObjValueBackward info) (evalMIP sol (fmap fromIntegral mip))
  where
    arbitraryAssignments mip = liftM Map.fromList $ do
      forM (Map.keys (MIP.varType mip)) $ \v -> do
        val <- choose (0, 1)
        pure (v, fromInteger val)

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
        forAll (arbitraryAssignments mip) $ \sol ->
          case evalMIP sol (fmap fromIntegral mip) of
            Nothing -> True
            Just val2 ->
              case SAT.evalPBSoftFormula (transformBackward info sol) wbo of
                Nothing -> False
                Just val1 -> val1 <= transformObjValueBackward info val2
  where
    arbitraryAssignments mip = liftM Map.fromList $ do
      forM (Map.keys (MIP.varType mip)) $ \v -> do
        val <- choose (0, 1)
        pure (v, fromInteger val)

prop_wbo2ip_json :: Property
prop_wbo2ip_json =
  forAll arbitraryPBSoftFormula $ \wbo ->
  forAll arbitrary $ \b ->
    let ret@(_, info) = wbo2ip b wbo
        json = J.encode info
     in counterexample (show ret) $ counterexample (show json) $
          J.eitherDecode json === Right info

evalMIP :: Map MIP.Var Rational -> MIP.Problem Rational -> Maybe Rational
evalMIP sol prob = do
  forM_ (MIP.constraints prob) $ \constr -> do
    guard $ evalConstraint constr
  forM_ (MIP.sosConstraints prob) $ \constr -> do
    guard $ evalSOSConstraint constr
  forM_ (Map.toList (MIP.varBounds prob)) $ \(v, (lb, ub)) -> do
    let val = sol Map.! v
    case MIP.varType prob Map.! v of
      MIP.ContinuousVariable -> do
        guard $ lb <= MIP.Finite val && MIP.Finite val <= ub
      MIP.IntegerVariable -> do
        guard $ lb <= MIP.Finite val && MIP.Finite val <= ub
        guard $ fromIntegral (round val :: Integer) == val
      MIP.SemiContinuousVariable -> do
        guard $ val == 0 || lb <= MIP.Finite val && MIP.Finite val <= ub
      MIP.SemiIntegerVariable -> do
        guard $ val == 0 || lb <= MIP.Finite val && MIP.Finite val <= ub
        guard $ fromIntegral (round val :: Integer) == val
  return $ evalExpr $ MIP.objExpr $ MIP.objectiveFunction prob
  where
    evalExpr :: MIP.Expr Rational -> Rational
    evalExpr expr = sum [product (c : [sol Map.! v | v <- vs]) | MIP.Term c vs <- MIP.terms expr]

    evalIndicator :: Maybe (MIP.Var, Rational) -> Bool
    evalIndicator Nothing = True
    evalIndicator (Just (v, val)) = (sol Map.! v) == val

    evalConstraint :: MIP.Constraint Rational -> Bool
    evalConstraint constr =
      not (evalIndicator (MIP.constrIndicator constr)) ||
      MIP.constrLB constr <= val && val <= MIP.constrUB constr
      where
        val = MIP.Finite $ evalExpr (MIP.constrExpr constr)

    evalSOSConstraint :: MIP.SOSConstraint Rational -> Bool
    evalSOSConstraint sos =
      case MIP.sosType sos of
        MIP.S1 -> length [() | val <- body, val > 0] <= 1
        MIP.S2 -> f body
      where
        body = map ((sol Map.!) . fst) $ sortBy (comparing snd) $ (MIP.sosBody sos)
        f [] = True
        f [_] = True
        f (x1 : x2 : xs)
          | x1 > 0 = all (0==) xs
          | otherwise = f (x2 : xs)

------------------------------------------------------------------------

converterTestGroup :: TestTree
converterTestGroup = $(testGroupGenerator)
