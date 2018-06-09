{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE TypeFamilies #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.Converter.GCNF2MaxSAT
-- Copyright   :  (c) Masahiro Sakai 2016
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  experimental
-- Portability :  non-portable
--
-----------------------------------------------------------------------------
module ToySolver.Converter.GCNF2MaxSAT
  ( convert
  , GCNF2WCNFInfo (..)
  ) where

import qualified Data.Vector.Generic as VG
import ToySolver.Converter.Base
import qualified ToySolver.SAT.Types as SAT
import qualified ToySolver.Text.CNF as CNF

data GCNF2WCNFInfo = GCNF2WCNFInfo !Int

instance Transformer GCNF2WCNFInfo where
  type Source GCNF2WCNFInfo = SAT.Model
  type Target GCNF2WCNFInfo = SAT.Model

instance BackwardTransformer GCNF2WCNFInfo where
  transformBackward (GCNF2WCNFInfo nv1) = SAT.restrictModel nv1

convert :: CNF.GCNF -> (CNF.WCNF, GCNF2WCNFInfo)
convert
  CNF.GCNF
  { CNF.gcnfNumVars        = nv
  , CNF.gcnfNumClauses     = nc
  , CNF.gcnfLastGroupIndex = lastg
  , CNF.gcnfClauses        = cs
  }
  =
  ( CNF.WCNF
    { CNF.wcnfTopCost = top
    , CNF.wcnfClauses = [(top, if g==0 then c else VG.cons (-(nv+g)) c) | (g,c) <- cs] ++ [(1, SAT.packClause [v]) | v <- [nv+1..nv+lastg]]
    , CNF.wcnfNumVars = nv + lastg
    , CNF.wcnfNumClauses = nc + lastg
    }
  , GCNF2WCNFInfo nv
  )
  where
    top :: CNF.Weight
    top = fromIntegral (lastg + 1)
