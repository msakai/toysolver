{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_HADDOCK show-extensions #-}
{-# LANGUAGE OverloadedStrings #-}
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

import qualified Data.Aeson as J
import qualified Data.Aeson.Types as J
import Data.Aeson ((.=), (.:))
import Data.Array.IArray
import qualified Data.IntMap.Strict as IntMap
import qualified Data.Map.Lazy as Map
import Data.String
import qualified Data.Text as T
import ToySolver.Converter.Base
import ToySolver.Internal.JSON
import qualified ToySolver.SAT.Formula as SAT
import ToySolver.SAT.Internal.JSON
import qualified ToySolver.SAT.Types as SAT
import qualified ToySolver.SAT.Encoder.Tseitin as Tseitin

data TseitinInfo = TseitinInfo !Int !Int (SAT.VarMap Tseitin.Formula)
  deriving (Show, Read, Eq)

instance Transformer TseitinInfo where
  type Source TseitinInfo = SAT.Model
  type Target TseitinInfo = SAT.Model

instance ForwardTransformer TseitinInfo where
  transformForward (TseitinInfo _nv1 nv2 defs) m = array (1, nv2) (assocs a)
    where
      -- Use BOXED array to tie the knot
      a :: Array SAT.Var Bool
      a = array (1, nv2) $
            assocs m ++ [(v, Tseitin.evalFormula a phi) | (v, phi) <- IntMap.toList defs]

instance BackwardTransformer TseitinInfo where
  transformBackward (TseitinInfo nv1 _nv2 _defs) = SAT.restrictModel nv1

instance J.ToJSON TseitinInfo where
  toJSON (TseitinInfo nv1 nv2 defs) =
    J.object
    [ "type" .= J.String "TseitinInfo"
    , "num_original_variables" .= nv1
    , "num_transformed_variables" .= nv2
    , "definitions" .= J.object
        [ fromString ("x" ++ show v) .= formula
        | (v, formula) <- IntMap.toList defs
        ]
    ]

instance J.FromJSON TseitinInfo where
  parseJSON = withTypedObject "TseitinInfo" $ \obj -> do
    defs <- obj .: "definitions"
    TseitinInfo
      <$> obj .: "num_original_variables"
      <*> obj .: "num_transformed_variables"
      <*> (IntMap.fromList <$> mapM f (Map.toList defs))
    where
      f :: (T.Text, SAT.Formula) -> J.Parser (SAT.Var, SAT.Formula)
      f (name, formula) = do
        x <- parseVarNameText name
        pure (x, formula)

-- -----------------------------------------------------------------------------
