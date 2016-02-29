{-# LANGUAGE FlexibleContexts, OverloadedStrings #-}
{-# OPTIONS_GHC -Wall #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.Text.CNF
-- Copyright   :  (c) Masahiro Sakai 2016
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  non-portable (FlexibleContexts, OverloadedStrings)
--
-----------------------------------------------------------------------------
module ToySolver.Text.CNF
  (
  -- * Generating .cnf files
    writeFile
  ) where

import Prelude hiding (writeFile)
import Data.Array.IArray
import Data.ByteString.Builder
import Data.Monoid
import System.IO hiding (writeFile)

import qualified Language.CNF.Parse.ParseDIMACS as DIMACS

writeFile :: FilePath -> DIMACS.CNF -> IO ()
writeFile filepath cnf = do
  withBinaryFile filepath WriteMode $ \h -> do
    hSetBuffering h (BlockBuffering Nothing)
    hPutBuilder h (cnfBuilder cnf)

cnfBuilder :: DIMACS.CNF -> Builder
cnfBuilder cnf = header <> mconcat (map f (DIMACS.clauses cnf))
  where
    header = mconcat
      [ byteString "p cnf "
      , intDec (DIMACS.numVars cnf), char7 ' '
      , intDec (DIMACS.numClauses cnf), char7 '\n'
      ]
    f c = mconcat [intDec lit <> char7 ' '| lit <- elems c] <> byteString "0\n"
