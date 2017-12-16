{-# OPTIONS_GHC -Wall #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.Converter.PBNormalization
-- Copyright   :  (c) Masahiro Sakai 2017
-- License     :  BSD-style
--
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  experimental
-- Portability :  portable
--
-- Remove negations from linear terms.
--
-----------------------------------------------------------------------------
module ToySolver.Converter.PBNormalization
  ( normalizeOPB
  , normalizeWBO
  ) where

import Data.List
import qualified Data.PseudoBoolean as PBFile

-- XXX: we do not normalize objective function, because normalization might
-- introduce constrant terms, but OPB file format does not allow constant terms.
--
-- Options:
-- (1) not normalize objective function (current implementation),
-- (2) normalize and simply delete constant terms (in pseudo-boolean package?),
-- (3) normalize and introduce dummy variable to make constant terms
--     into non-constant terms (in pseudo-boolean package?).
normalizeOPB :: PBFile.Formula -> PBFile.Formula
normalizeOPB formula =
  formula
  { PBFile.pbConstraints =
      map normalizePBConstraint (PBFile.pbConstraints formula)
  }

normalizeWBO :: PBFile.SoftFormula -> PBFile.SoftFormula
normalizeWBO formula =
  formula
  { PBFile.wboConstraints =
      map (\(w,constr) -> (w, normalizePBConstraint constr)) (PBFile.wboConstraints formula)
  }

normalizePBConstraint :: PBFile.Constraint -> PBFile.Constraint
normalizePBConstraint (lhs,op,rhs) =
  case mapAccumL h 0 lhs of
    (offset, lhs') -> (lhs', op, rhs - offset)
  where
    h s (w,[x]) | x < 0 = (s+w, (-w,[-x]))
    h s t = (s,t)
