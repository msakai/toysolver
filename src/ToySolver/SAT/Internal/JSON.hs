{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_HADDOCK show-extensions #-}
{-# LANGUAGE OverloadedStrings #-}
module ToySolver.SAT.Internal.JSON where

import qualified Data.Aeson as J
import Data.Aeson ((.=))
import Data.String
import qualified Data.Vector as V

import qualified Data.PseudoBoolean as PBFile
import qualified ToySolver.SAT.Types as SAT

jVar :: SAT.Var -> J.Value
jVar v = J.object
  [ "type" .= J.String "variable"
  , "name" .= (fromString ("x" <> show v) :: J.Value)
  ]

jNot :: J.Value -> J.Value
jNot x = J.object
  [ "type" .= J.String "operator"
  , "name" .= J.String "not"
  , "operands" .= J.Array (V.singleton x)
  ]

jLit :: SAT.Lit -> J.Value
jLit l
  | l > 0 = jVar l
  | otherwise = jNot $ jVar (- l)

jConst :: J.ToJSON a => a -> J.Value
jConst x = J.object ["type" .= J.String "constant", "value" .= x]

jPBSum :: SAT.PBSum -> J.Value
jPBSum s = J.object
  [ "type" .= J.String "operator"
  , "name" .= J.String "+"
  , "operands" .=
      [ J.object
          [ "type" .= J.String "operator"
          , "name" .= J.String "*"
          , "operands" .= (jConst c : [jLit lit | lit <- lits])
          ]
      | (c, lits) <- s
      ]
  ]

jPBConstraint :: PBFile.Constraint -> J.Value
jPBConstraint (lhs, op, rhs) =
  J.object
  [ "type" .= J.String "operator"
  , "name" .= J.String (case op of{ PBFile.Ge -> ">="; PBFile.Eq -> "=" })
  , "operands" .= [jPBSum lhs, jConst rhs]
  ]
