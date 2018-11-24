
{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE TypeFamilies #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.Converter.Tseitin
-- Copyright   :  (c) Masahiro Sakai 2018
-- License     :  BSD-style
--
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  experimental
-- Portability :  non-portable
--
-----------------------------------------------------------------------------
module ToySolver.Converter.Tseitin
  ( TseitinInfo (..)
  ) where

import Data.Array.IArray
import ToySolver.Converter.Base
import qualified ToySolver.SAT.Types as SAT
import qualified ToySolver.SAT.Encoder.Tseitin as Tseitin

data TseitinInfo = TseitinInfo !Int !Int [(SAT.Var, Tseitin.Formula)]
  deriving (Eq, Show)

instance Transformer TseitinInfo where
  type Source TseitinInfo = SAT.Model
  type Target TseitinInfo = SAT.Model

instance ForwardTransformer TseitinInfo where
  transformForward (TseitinInfo _nv1 nv2 defs) m = array (1, nv2) (assocs a)
    where
      -- Use BOXED array to tie the knot
      a :: Array SAT.Var Bool
      a = array (1, nv2) $
            assocs m ++ [(v, Tseitin.evalFormula a phi) | (v, phi) <- defs]

instance BackwardTransformer TseitinInfo where
  transformBackward (TseitinInfo nv1 _nv2 _defs) = SAT.restrictModel nv1

-- -----------------------------------------------------------------------------
