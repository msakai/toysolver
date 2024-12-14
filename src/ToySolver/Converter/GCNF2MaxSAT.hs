{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_HADDOCK show-extensions #-}
{-# LANGUAGE OverloadedStrings #-}
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
  ( gcnf2maxsat
  , GCNF2MaxSATInfo (..)
  ) where

import qualified Data.Aeson as J
import Data.Aeson ((.=), (.:))
import qualified Data.Vector.Generic as VG
import ToySolver.Converter.Base
import qualified ToySolver.FileFormat.CNF as CNF
import ToySolver.Internal.JSON
import qualified ToySolver.SAT.Types as SAT

newtype GCNF2MaxSATInfo = GCNF2MaxSATInfo Int
  deriving (Eq, Show, Read)

instance Transformer GCNF2MaxSATInfo where
  type Source GCNF2MaxSATInfo = SAT.Model
  type Target GCNF2MaxSATInfo = SAT.Model

instance BackwardTransformer GCNF2MaxSATInfo where
  transformBackward (GCNF2MaxSATInfo nv1) = SAT.restrictModel nv1

instance J.ToJSON GCNF2MaxSATInfo where
  toJSON (GCNF2MaxSATInfo nv) =
    J.object
    [ "type" .= ("GCNF2MaxSATInfo" :: J.Value)
    , "num_original_variables" .= nv
    ]

instance J.FromJSON GCNF2MaxSATInfo where
  parseJSON = withTypedObject "GCNF2MaxSATInfo" $ \obj ->
    GCNF2MaxSATInfo <$> obj .: "num_original_variables"

gcnf2maxsat :: CNF.GCNF -> (CNF.WCNF, GCNF2MaxSATInfo)
gcnf2maxsat
  CNF.GCNF
  { CNF.gcnfNumVars        = nv
  , CNF.gcnfNumClauses     = nc
  , CNF.gcnfLastGroupIndex = lastg
  , CNF.gcnfClauses        = cs
  }
  =
  ( CNF.WCNF
    { CNF.wcnfTopCost = top
    , CNF.wcnfClauses =
        [(top, if g==0 then c else VG.cons (- SAT.packLit (nv+g)) c) | (g,c) <- cs] ++
        [(1, SAT.packClause [v]) | v <- [nv+1..nv+lastg]]
    , CNF.wcnfNumVars = nv + lastg
    , CNF.wcnfNumClauses = nc + lastg
    }
  , GCNF2MaxSATInfo nv
  )
  where
    top :: CNF.Weight
    top = fromIntegral (lastg + 1)
