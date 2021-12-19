{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
module Test.CNF (cnfTestGroup) where

import Data.ByteString.Builder
import qualified Data.ByteString.Lazy.Char8 as BL
import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.QuickCheck
import Test.Tasty.TH
import ToySolver.FileFormat
import qualified ToySolver.FileFormat.CNF as CNF

import Test.SAT.Utils

------------------------------------------------------------------------

prop_CNF_ReadWrite_Invariance :: Property
prop_CNF_ReadWrite_Invariance = forAll arbitraryCNF $ \cnf ->
  CNF.parse (toLazyByteString (CNF.render cnf)) === Right cnf

prop_GCNF_ReadWrite_Invariance :: Property
prop_GCNF_ReadWrite_Invariance = forAll arbitraryGCNF $ \gcnf ->
  CNF.parse (toLazyByteString (CNF.render gcnf)) === Right gcnf

prop_WCNF_ReadWrite_Invariance :: Property
prop_WCNF_ReadWrite_Invariance = forAll arbitraryWCNF $ \wcnf ->
  CNF.parse (toLazyByteString (CNF.render wcnf)) === Right wcnf

prop_NewWCNF_ReadWrite_Invariance :: Property
prop_NewWCNF_ReadWrite_Invariance = forAll arbitraryNewWCNF $ \wcnf ->
  CNF.parse (toLazyByteString (CNF.render wcnf)) === Right wcnf

prop_QDimacs_ReadWrite_Invariance :: Property
prop_QDimacs_ReadWrite_Invariance = forAll arbitraryQDimacs $ \qdimacs ->
  CNF.parse (toLazyByteString (CNF.render qdimacs)) === Right qdimacs

prop_GCNF_from_CNF :: Property
prop_GCNF_from_CNF = forAll arbitraryCNF $ \cnf ->
  case CNF.parse (toLazyByteString (CNF.render cnf)) of
    Left _ -> property False
    Right gcnf -> conjoin
      [ CNF.gcnfNumVars gcnf === CNF.cnfNumVars cnf
      , CNF.gcnfNumClauses gcnf === CNF.cnfNumClauses cnf
      , CNF.gcnfLastGroupIndex gcnf === CNF.cnfNumClauses cnf
      , CNF.gcnfClauses gcnf === zip [1..] (CNF.cnfClauses cnf)
      ]

prop_WCNF_from_CNF :: Property
prop_WCNF_from_CNF = forAll arbitraryCNF $ \cnf ->
  case CNF.parse (toLazyByteString (CNF.render cnf)) of
    Left _ -> property False
    Right wcnf -> conjoin
      [ CNF.wcnfNumVars wcnf === CNF.cnfNumVars cnf
      , CNF.wcnfNumClauses wcnf === CNF.cnfNumClauses cnf
      , property $ CNF.wcnfTopCost wcnf > fromIntegral (CNF.cnfNumClauses cnf)
      , CNF.wcnfClauses wcnf === map (\c -> (1,c)) (CNF.cnfClauses cnf)
      ]

prop_QDimacs_from_CNF :: Property
prop_QDimacs_from_CNF = forAll arbitraryCNF $ \cnf ->
  case CNF.parse (toLazyByteString (CNF.render cnf)) of
    Left _ -> property False
    Right qdimacs -> conjoin
      [ CNF.qdimacsNumVars qdimacs === CNF.cnfNumVars cnf
      , CNF.qdimacsNumClauses qdimacs === CNF.cnfNumClauses cnf
      , CNF.qdimacsPrefix qdimacs === []
      , CNF.qdimacsMatrix qdimacs === CNF.cnfClauses cnf
      ]

-- example from https://maxsat-evaluations.github.io/2021/format.html
case_parse_new_WCNF_as_old :: IO ()
case_parse_new_WCNF_as_old = parse s @?= Right expected
  where
    s = BL.pack $ unlines
        [ "c This is a comment"
        , "c Example 1...another comment"
        , "h 1 2 3 4 0"
        , "1 -3 -5 6 7 0"
        , "6 -1 -2 0"
        , "4 1 6 -7 0"
        ]
    h = 12
    expected =
      CNF.WCNF
      { CNF.wcnfNumVars = 7
      , CNF.wcnfNumClauses = 4
      , CNF.wcnfTopCost = h
      , CNF.wcnfClauses =
          [ (h, CNF.packClause [1,2,3,4])
          , (1, CNF.packClause [-3,-5,6,7])
          , (6, CNF.packClause [-1,-2])
          , (4, CNF.packClause [1,6,-7])
          ]
      }

-- example from https://maxsat-evaluations.github.io/2021/format.html
case_parse_old_WCNF_as_new :: IO ()
case_parse_old_WCNF_as_new = parse s @?= Right expected
  where
    s = BL.pack $ unlines
        [ "c This is a comment"
        , "c Example 1...another comment"
        , "p wcnf 7 4 12 "
        , "12 1 2 3 4 0"
        , "1 -3 -5 6 7 0"
        , "6 -1 -2 0"
        , "4 1 6 -7 0"
        ]
    expected =
      CNF.NewWCNF
        [ (Nothing, CNF.packClause [1,2,3,4])
        , (Just 1, CNF.packClause [-3,-5,6,7])
        , (Just 6, CNF.packClause [-1,-2])
        , (Just 4, CNF.packClause [1,6,-7])
        ]

------------------------------------------------------------------------
-- Test harness

cnfTestGroup :: TestTree
cnfTestGroup = $(testGroupGenerator)
