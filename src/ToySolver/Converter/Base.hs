{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
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
  , ComposedTransformer (..)
  , IdentityTransformer (..)
  ) where


class Transformer a where
  type Source a
  type Target a

class Transformer a => ForwardTransformer a where
  transformForward :: a -> Source a -> Target a

class Transformer a => BackwardTransformer a where
  transformBackward :: a -> Target a -> Source a


data ComposedTransformer a b = ComposedTransformer a b

instance (Transformer a, Transformer b, Target a ~ Source b) => Transformer (ComposedTransformer a b) where
  type Source (ComposedTransformer a b) = Source a
  type Target (ComposedTransformer a b) = Target b

instance (ForwardTransformer a, ForwardTransformer b, Target a ~ Source b)
  => ForwardTransformer (ComposedTransformer a b) where
  transformForward (ComposedTransformer a b) = transformForward b . transformForward a

instance (BackwardTransformer a, BackwardTransformer b, Target a ~ Source b)
  => BackwardTransformer (ComposedTransformer a b) where
  transformBackward (ComposedTransformer a b) = transformBackward a . transformBackward b


data IdentityTransformer a = IdentityTransformer

instance Transformer (IdentityTransformer a) where
  type Source (IdentityTransformer a) = a
  type Target (IdentityTransformer a) = a

instance ForwardTransformer (IdentityTransformer a) where
  transformForward IdentityTransformer = id

instance BackwardTransformer (IdentityTransformer a) where
  transformBackward IdentityTransformer = id
