{-# LANGUAGE BangPatterns #-}
{-# OPTIONS_GHC -Wall #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.Text.PBFile
-- Copyright   :  (c) Masahiro Sakai 2011-2015
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Portability :  non-portable (BangPatterns)
--
-- A parser library for .opb file and .wbo files used by PB Competition.
-- 
-- References:
--
-- * Input/Output Format and Solver Requirements for the Competitions of
--   Pseudo-Boolean Solvers
--   <http://www.cril.univ-artois.fr/PB11/format.pdf>
--
-----------------------------------------------------------------------------

module ToySolver.Text.PBFile
  (
  -- * Abstract Syntax
    Formula (..)
  , Constraint
  , Op (..)
  , SoftFormula (..)
  , SoftConstraint
  , Sum
  , WeightedTerm
  , Term
  , Lit
  , Var

  -- * Parsing .opb files
  , parseOPBString
  , parseOPBByteString
  , parseOPBFile

  -- * Parsing .wbo files
  , parseWBOString
  , parseWBOByteString
  , parseWBOFile

  -- * Show .opb files
  , renderOPB
  , renderOPBByteString
  , writeOPBFile
  , hPutOPB

  -- * Show .wbo files
  , renderWBO
  , renderWBOByteString
  , writeWBOFile
  , hPutWBO
  ) where

import Prelude hiding (sum)
import qualified Data.ByteString.Lazy as BS
import qualified Data.ByteString.Builder as Builder
import qualified Data.DList as DList
import Data.Monoid hiding (Sum (..))
import Data.String
import System.IO
import Text.Printf
import ToySolver.Text.PBFile.Parsec
import ToySolver.Text.PBFile.Attoparsec hiding (parseOPBFile, parseWBOFile)
import ToySolver.Text.PBFile.Types

renderOPB :: Formula -> String
renderOPB opb = DList.apply (showOPB opb) ""

renderWBO :: SoftFormula -> String
renderWBO wbo = DList.apply (showWBO wbo) ""

renderOPBByteString :: Formula -> BS.ByteString
renderOPBByteString opb = Builder.toLazyByteString (showOPB opb)

renderWBOByteString :: SoftFormula -> BS.ByteString
renderWBOByteString wbo = Builder.toLazyByteString (showWBO wbo)

showOPB :: (Monoid a, IsString a) => Formula -> a
showOPB opb = (size <> part1 <> part2)
  where
    nv = pbNumVars opb
    nc = pbNumConstraints opb
    size = fromString (printf "* #variable= %d #constraint= %d\n" nv nc)
    part1 = 
      case pbObjectiveFunction opb of
        Nothing -> mempty
        Just o -> fromString "min: " <> showSum o <> fromString ";\n"
    part2 = mconcat $ map showConstraint (pbConstraints opb)

showWBO :: (Monoid a, IsString a) => SoftFormula -> a
showWBO wbo = size <> part1 <> part2
  where
    nv = wboNumVars wbo
    nc = wboNumConstraints wbo
    size = fromString (printf "* #variable= %d #constraint= %d\n" nv nc)
    part1 = 
      case wboTopCost wbo of
        Nothing -> fromString "soft: ;\n"
        Just t -> fromString "soft: " <> fromString (show t) <> fromString ";\n"
    part2 = mconcat $ map showSoftConstraint (wboConstraints wbo)

showSum :: (Monoid a, IsString a) => Sum -> a
showSum = mconcat . map showWeightedTerm

showWeightedTerm :: (Monoid a, IsString a) => WeightedTerm -> a
showWeightedTerm (c, lits) = foldr (\f g -> f <> fromString " " <> g) mempty (x:xs)
  where
    x = if c >= 0 then fromString "+" <> fromString (show c) else fromString (show c)
    xs = map showLit lits

showLit :: (Monoid a, IsString a) => Lit -> a
showLit lit = if lit > 0 then v else fromString "~" <> v
  where
    v = fromString "x" <> fromString (show (abs lit))

showConstraint :: (Monoid a, IsString a) => Constraint -> a
showConstraint (lhs, op, rhs) =
  showSum lhs <> f op <>  fromString " " <> fromString (show rhs) <> fromString ";\n"
  where
    f Eq = fromString "="
    f Ge = fromString ">="

showSoftConstraint :: (Monoid a, IsString a) => SoftConstraint -> a
showSoftConstraint (cost, constr) =
  case cost of
    Nothing -> showConstraint constr
    Just c -> fromString "[" <> fromString (show c) <> fromString "] " <> showConstraint constr

writeOPBFile :: FilePath -> Formula -> IO ()
writeOPBFile filepath opb = withBinaryFile filepath WriteMode $ \h -> do
  hSetBuffering h (BlockBuffering Nothing)
  hPutOPB h opb

writeWBOFile :: FilePath -> SoftFormula -> IO ()
writeWBOFile filepath wbo = withBinaryFile filepath WriteMode $ \h -> do
  hSetBuffering h (BlockBuffering Nothing)
  hPutWBO h wbo

-- It is recommended that the 'Handle' is set to binary and
-- 'BlockBuffering' mode. See 'hSetBinaryMode' and 'hSetBuffering'.
hPutOPB :: Handle -> Formula -> IO ()
hPutOPB h opb = Builder.hPutBuilder h (showOPB opb)

-- It is recommended that the 'Handle' is set to binary and
-- 'BlockBuffering' mode. See 'hSetBinaryMode' and 'hSetBuffering'.
hPutWBO :: Handle -> SoftFormula -> IO ()
hPutWBO h wbo = Builder.hPutBuilder h (showWBO wbo)

