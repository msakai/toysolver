{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_HADDOCK show-extensions #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.Converter.Base
-- Copyright   :  (c) Masahiro Sakai 2018
-- License     :  BSD-style
--
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  experimental
-- Portability :  non-portable
--
-----------------------------------------------------------------------------
module ToySolver.Converter.Base
  ( Transformer (..)
  , ForwardTransformer (..)
  , BackwardTransformer (..)
  , ObjValueTransformer (..)
  , ObjValueForwardTransformer (..)
  , ObjValueBackwardTransformer (..)
  , ComposedTransformer (..)
  , IdentityTransformer (..)
  , ReversedTransformer (..)
  ) where

import qualified Data.Aeson as J
import Data.Aeson ((.=), (.:))
import ToySolver.Internal.JSON (withTypedObject)

class (Eq a, Show a) => Transformer a where
  type Source a
  type Target a

class Transformer a => ForwardTransformer a where
  transformForward :: a -> Source a -> Target a

class Transformer a => BackwardTransformer a where
  transformBackward :: a -> Target a -> Source a


class ObjValueTransformer a where
  type SourceObjValue a
  type TargetObjValue a

class ObjValueTransformer a => ObjValueForwardTransformer a where
  transformObjValueForward :: a -> SourceObjValue a -> TargetObjValue a

class ObjValueTransformer a => ObjValueBackwardTransformer a where
  transformObjValueBackward :: a -> TargetObjValue a -> SourceObjValue a


data ComposedTransformer a b = ComposedTransformer a b
  deriving (Eq, Show, Read)

instance (Transformer a, Transformer b, Target a ~ Source b) => Transformer (ComposedTransformer a b) where
  type Source (ComposedTransformer a b) = Source a
  type Target (ComposedTransformer a b) = Target b

instance (ForwardTransformer a, ForwardTransformer b, Target a ~ Source b)
  => ForwardTransformer (ComposedTransformer a b) where
  transformForward (ComposedTransformer a b) = transformForward b . transformForward a

instance (BackwardTransformer a, BackwardTransformer b, Target a ~ Source b)
  => BackwardTransformer (ComposedTransformer a b) where
  transformBackward (ComposedTransformer a b) = transformBackward a . transformBackward b


instance (ObjValueTransformer a, ObjValueTransformer b, TargetObjValue a ~ SourceObjValue b)
  => ObjValueTransformer (ComposedTransformer a b) where
  type SourceObjValue (ComposedTransformer a b) = SourceObjValue a
  type TargetObjValue (ComposedTransformer a b) = TargetObjValue b

instance (ObjValueForwardTransformer a, ObjValueForwardTransformer b, TargetObjValue a ~ SourceObjValue b)
  => ObjValueForwardTransformer (ComposedTransformer a b) where
  transformObjValueForward (ComposedTransformer a b) = transformObjValueForward b . transformObjValueForward a

instance (ObjValueBackwardTransformer a, ObjValueBackwardTransformer b, TargetObjValue a ~ SourceObjValue b)
  => ObjValueBackwardTransformer (ComposedTransformer a b) where
  transformObjValueBackward (ComposedTransformer a b) = transformObjValueBackward a . transformObjValueBackward b

instance (J.ToJSON a, J.ToJSON b) => J.ToJSON (ComposedTransformer a b) where
  toJSON (ComposedTransformer a b) =
    J.object
    [ "type" .= J.String "ComposedTransformer"
    , "first" .= a
    , "second" .= b
    ]

instance (J.FromJSON a, J.FromJSON b) => J.FromJSON (ComposedTransformer a b) where
  parseJSON = withTypedObject "ComposedTransformer" $ \obj -> do
    ComposedTransformer
      <$> obj .: "first"
      <*> obj .: "second"


data IdentityTransformer a = IdentityTransformer
  deriving (Eq, Show, Read)

instance Transformer (IdentityTransformer a) where
  type Source (IdentityTransformer a) = a
  type Target (IdentityTransformer a) = a

instance ForwardTransformer (IdentityTransformer a) where
  transformForward IdentityTransformer = id

instance BackwardTransformer (IdentityTransformer a) where
  transformBackward IdentityTransformer = id

instance J.ToJSON (IdentityTransformer a) where
  toJSON IdentityTransformer =
    J.object
    [ "type" .= J.String "IdentityTransformer"
    ]

instance J.FromJSON (IdentityTransformer a) where
  parseJSON = withTypedObject "IdentityTransformer" $ \_ -> pure IdentityTransformer


newtype ReversedTransformer t = ReversedTransformer t
  deriving (Eq, Show, Read)

instance Transformer t => Transformer (ReversedTransformer t) where
  type Source (ReversedTransformer t) = Target t
  type Target (ReversedTransformer t) = Source t

instance BackwardTransformer t => ForwardTransformer (ReversedTransformer t) where
  transformForward (ReversedTransformer t) = transformBackward t

instance ForwardTransformer t => BackwardTransformer (ReversedTransformer t) where
  transformBackward (ReversedTransformer t) = transformForward t

instance ObjValueTransformer t => ObjValueTransformer (ReversedTransformer t) where
  type SourceObjValue (ReversedTransformer t) = TargetObjValue t
  type TargetObjValue (ReversedTransformer t) = SourceObjValue t

instance ObjValueBackwardTransformer t => ObjValueForwardTransformer (ReversedTransformer t) where
  transformObjValueForward (ReversedTransformer t) = transformObjValueBackward t

instance ObjValueForwardTransformer t => ObjValueBackwardTransformer (ReversedTransformer t) where
  transformObjValueBackward (ReversedTransformer t) = transformObjValueForward t

instance J.ToJSON t => J.ToJSON (ReversedTransformer t) where
  toJSON (ReversedTransformer t) =
    J.object
    [ "type" .= ("ReversedTransformer" :: J.Value)
    , "base" .= t
    ]

instance J.FromJSON t => J.FromJSON (ReversedTransformer t) where
  parseJSON = withTypedObject "ReversedTransformer" $ \v ->
    ReversedTransformer <$> v .: "base"
