{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
module Test.CNF (cnfTestGroup) where

import Control.Applicative
import Control.Monad
import Data.ByteString.Builder
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import Data.Maybe
import Test.Tasty
import Test.Tasty.QuickCheck
import Test.Tasty.TH
import qualified ToySolver.SAT.Types as SAT
import qualified ToySolver.Text.CNF as CNF

------------------------------------------------------------------------

arbitraryCNF :: Gen CNF.CNF
arbitraryCNF = do
  nv <- choose (0,10)
  nc <- choose (0,50)
  cs <- replicateM nc $ do
    if nv == 0 then
      return $ SAT.packClause []
    else do
      len <- choose (0,10)
      SAT.packClause <$> (replicateM len $ choose (-nv, nv) `suchThat` (/= 0))
  return $
    CNF.CNF
    { CNF.cnfNumVars = nv
    , CNF.cnfNumClauses = nc
    , CNF.cnfClauses = cs
    }

arbitraryGCNF :: Gen CNF.GCNF
arbitraryGCNF = do
  nv <- choose (0,10)
  nc <- choose (0,50)
  ng <- choose (0,10)
  cs <- replicateM nc $ do
    g <- choose (0,ng) -- inclusive range
    c <-
      if nv == 0 then do
        return $ SAT.packClause []
      else do
        len <- choose (0,10)
        SAT.packClause <$> (replicateM len $ choose (-nv, nv) `suchThat` (/= 0))
    return (g,c)
  return $
    CNF.GCNF
    { CNF.gcnfNumVars = nv
    , CNF.gcnfNumClauses = nc
    , CNF.gcnfLastGroupIndex = ng
    , CNF.gcnfClauses = cs
    }

arbitraryWCNF :: Gen CNF.WCNF
arbitraryWCNF = do
  nv <- choose (0,10)
  nc <- choose (0,50)
  cs <- replicateM nc $ do
    w <- arbitrary
    c <- do
      if nv == 0 then do
        return $ SAT.packClause []
      else do
        len <- choose (0,10)
        SAT.packClause <$> (replicateM len $ choose (-nv, nv) `suchThat` (/= 0))
    return (fmap getPositive w, c)
  let topCost = sum [w | (Just w, _) <- cs] + 1
  return $
    CNF.WCNF
    { CNF.wcnfNumVars = nv
    , CNF.wcnfNumClauses = nc
    , CNF.wcnfTopCost = topCost
    , CNF.wcnfClauses = [(fromMaybe topCost w, c) | (w,c) <- cs]
    }

arbitraryQDimacs :: Gen CNF.QDimacs
arbitraryQDimacs = do
  nv <- choose (0,10)
  nc <- choose (0,50)
  prefix <- arbitraryPrefix $ IntSet.fromList [1..nv]

  cs <- replicateM nc $ do
    if nv == 0 then
      return $ SAT.packClause []
    else do
      len <- choose (0,10)
      SAT.packClause <$> (replicateM len $ choose (-nv, nv) `suchThat` (/= 0))
  return $
    CNF.QDimacs
    { CNF.qdimacsNumVars = nv
    , CNF.qdimacsNumClauses = nc
    , CNF.qdimacsPrefix = prefix
    , CNF.qdimacsMatrix = cs
    }

arbitraryPrefix :: IntSet -> Gen [CNF.QuantSet]
arbitraryPrefix xs = do
  if IntSet.null xs then
    return []
  else do
    b <- arbitrary
    if b then
      return []
    else do
      xs1 <- subsetof xs `suchThat` (not . IntSet.null)
      let xs2 = xs IntSet.\\ xs1
      q <- elements [CNF.E, CNF.A]
      ((q, IntSet.toList xs1) :) <$> arbitraryPrefix xs2

subsetof :: IntSet -> Gen IntSet
subsetof xs = (IntSet.fromList . catMaybes) <$> sequence [elements [Just x, Nothing] | x <- IntSet.toList xs]

------------------------------------------------------------------------

prop_CNF_ReadWrite_Invariance :: Property
prop_CNF_ReadWrite_Invariance = forAll arbitraryCNF $ \cnf ->
  CNF.parse (toLazyByteString (CNF.render cnf)) == Right cnf

prop_GCNF_ReadWrite_Invariance :: Property
prop_GCNF_ReadWrite_Invariance = forAll arbitraryGCNF $ \gcnf ->
  CNF.parse (toLazyByteString (CNF.render gcnf)) == Right gcnf

prop_WCNF_ReadWrite_Invariance :: Property
prop_WCNF_ReadWrite_Invariance = forAll arbitraryWCNF $ \wcnf ->
  CNF.parse (toLazyByteString (CNF.render wcnf)) == Right wcnf

prop_QDimacs_ReadWrite_Invariance :: Property
prop_QDimacs_ReadWrite_Invariance = forAll arbitraryQDimacs $ \qdimacs ->
  CNF.parse (toLazyByteString (CNF.render qdimacs)) == Right qdimacs

prop_GCNF_from_CNF :: Property
prop_GCNF_from_CNF = forAll arbitraryCNF $ \cnf ->
  case CNF.parse (toLazyByteString (CNF.render cnf)) of
    Left _ -> False
    Right gcnf -> and
      [ CNF.gcnfNumVars gcnf == CNF.cnfNumVars cnf
      , CNF.gcnfNumClauses gcnf == CNF.cnfNumClauses cnf
      , CNF.gcnfLastGroupIndex gcnf == CNF.cnfNumClauses cnf
      , CNF.gcnfClauses gcnf == zip [1..] (CNF.cnfClauses cnf)
      ]

prop_WCNF_from_CNF :: Property
prop_WCNF_from_CNF = forAll arbitraryCNF $ \cnf ->
  case CNF.parse (toLazyByteString (CNF.render cnf)) of
    Left _ -> False
    Right wcnf -> and
      [ CNF.wcnfNumVars wcnf == CNF.cnfNumVars cnf
      , CNF.wcnfNumClauses wcnf == CNF.cnfNumClauses cnf
      , CNF.wcnfTopCost wcnf > fromIntegral (CNF.cnfNumClauses cnf)
      , CNF.wcnfClauses wcnf == map (\c -> (1,c)) (CNF.cnfClauses cnf)
      ]

prop_QDimacs_from_CNF :: Property
prop_QDimacs_from_CNF = forAll arbitraryCNF $ \cnf ->
  case CNF.parse (toLazyByteString (CNF.render cnf)) of
    Left _ -> False
    Right qdimacs -> and
      [ CNF.qdimacsNumVars qdimacs == CNF.cnfNumVars cnf
      , CNF.qdimacsNumClauses qdimacs == CNF.cnfNumClauses cnf
      , CNF.qdimacsPrefix qdimacs == []
      , CNF.qdimacsMatrix qdimacs == CNF.cnfClauses cnf
      ]

------------------------------------------------------------------------
-- Test harness

cnfTestGroup :: TestTree
cnfTestGroup = $(testGroupGenerator)
