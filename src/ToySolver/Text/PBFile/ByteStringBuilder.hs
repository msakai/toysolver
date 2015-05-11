{-# OPTIONS_GHC -Wall #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.Text.PBFile.ByteStringBuilder
-- Copyright   :  (c) Masahiro Sakai 2011-2015
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Portability :  portable
--
-----------------------------------------------------------------------------

module ToySolver.Text.PBFile.ByteStringBuilder
  ( opbBuilder
  , wboBuilder
  ) where

import Prelude hiding (sum)
import Data.Monoid hiding (Sum (..))
import Data.ByteString.Builder (Builder, intDec, integerDec, char7, string7)
import ToySolver.Text.PBFile.Types

opbBuilder :: Formula -> Builder
opbBuilder opb = (size <> part1 <> part2)
  where
    nv = pbNumVars opb
    nc = pbNumConstraints opb
    size = string7 "* #variable= " <> intDec nv <> string7 " #constraint= " <> intDec nc <> char7 '\n'
    part1 = 
      case pbObjectiveFunction opb of
        Nothing -> mempty
        Just o -> string7 "min: " <> showSum o <> string7 ";\n"
    part2 = mconcat $ map showConstraint (pbConstraints opb)

wboBuilder :: SoftFormula -> Builder
wboBuilder wbo = size <> part1 <> part2
  where
    nv = wboNumVars wbo
    nc = wboNumConstraints wbo
    size = string7 "* #variable= " <> intDec nv <> string7 " #constraint= " <> intDec nc <> char7 '\n'
    part1 = 
      case wboTopCost wbo of
        Nothing -> string7 "soft: ;\n"
        Just t -> string7 "soft: " <> integerDec t <> string7 ";\n"
    part2 = mconcat $ map showSoftConstraint (wboConstraints wbo)

showSum :: Sum -> Builder
showSum = mconcat . map showWeightedTerm

showWeightedTerm :: WeightedTerm -> Builder
showWeightedTerm (c, lits) = foldr (\f g -> f <> char7 ' ' <> g) mempty (x:xs)
  where
    x = if c >= 0 then char7 '+' <> integerDec c else integerDec c
    xs = map showLit lits

showLit :: Lit -> Builder
showLit lit = if lit > 0 then v else char7 '~' <> v
  where
    v = char7 'x' <> intDec (abs lit)

showConstraint :: Constraint -> Builder
showConstraint (lhs, op, rhs) =
  showSum lhs <> f op <>  char7 ' ' <> integerDec rhs <> string7 ";\n"
  where
    f Eq = char7 '='
    f Ge = string7 ">="

showSoftConstraint :: SoftConstraint -> Builder
showSoftConstraint (cost, constr) =
  case cost of
    Nothing -> showConstraint constr
    Just c -> char7 '[' <> integerDec c <> string7 "] " <> showConstraint constr
