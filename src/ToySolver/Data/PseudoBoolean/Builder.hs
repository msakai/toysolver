{-# OPTIONS_GHC -Wall #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.Data.PseudoBoolean.Builder
-- Copyright   :  (c) Masahiro Sakai 2011-2015
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Portability :  portable
--
-----------------------------------------------------------------------------

module ToySolver.Data.PseudoBoolean.Builder
  (
  -- * Builder for String-like Monoid
    opbBuilder
  , wboBuilder

  -- * String generation
  , toOPBString
  , toWBOString
  ) where

import Prelude hiding (sum)
import qualified Data.DList as DList
import Data.Monoid hiding (Sum (..))
import Data.String
import Text.Printf
import ToySolver.Data.PseudoBoolean.Types

-- | A builder which renders a OPB format in any String-like 'Monoid'.
opbBuilder :: (Monoid a, IsString a) => Formula -> a
opbBuilder opb = (size <> part1 <> part2)
  where
    nv = pbNumVars opb
    nc = pbNumConstraints opb
    size = fromString (printf "* #variable= %d #constraint= %d\n" nv nc)
    part1 = 
      case pbObjectiveFunction opb of
        Nothing -> mempty
        Just o -> fromString "min: " <> showSum o <> fromString ";\n"
    part2 = mconcat $ map showConstraint (pbConstraints opb)

-- | A builder which renders a WBO format in any String-like 'Monoid'.
wboBuilder :: (Monoid a, IsString a) => SoftFormula -> a
wboBuilder wbo = size <> part1 <> part2
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


-- | Generate a OPB format string containing pseudo boolean problem.
toOPBString :: Formula -> String
toOPBString opb = DList.apply (opbBuilder opb) ""

-- | Generate a WBO format string containing weighted boolean optimization problem.
toWBOString :: SoftFormula -> String
toWBOString wbo = DList.apply (wboBuilder wbo) ""
