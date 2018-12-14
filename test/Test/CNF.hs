{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
module Test.CNF (cnfTestGroup) where

import Control.Applicative
import Control.Monad
import Data.ByteString.Builder
import Data.Maybe
import Test.Tasty
import Test.Tasty.QuickCheck
import Test.Tasty.TH
import qualified ToySolver.FileFormat.CNF as CNF
import qualified ToySolver.SAT.Types as SAT

import Test.SAT.Utils

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
