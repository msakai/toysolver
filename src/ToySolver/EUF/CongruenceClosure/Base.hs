{-# LANGUAGE FlexibleInstances #-}
{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_HADDOCK show-extensions #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.EUF.CongruenceClosure.Base
-- Copyright   :  (c) Masahiro Sakai 2012, 2015
-- License     :  BSD-style
--
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  non-portable
--
-----------------------------------------------------------------------------
module ToySolver.EUF.CongruenceClosure.Base
  ( FSym
  , Term (..)
  , VAFun (..)
  ) where

type FSym = Int

data Term = TApp FSym [Term]
  deriving (Ord, Eq, Show)

class VAFun a where
  withVArgs :: ([Term] -> Term) -> a

instance VAFun Term where
  withVArgs k = k []

instance VAFun a => VAFun (Term -> a) where
  withVArgs k x = withVArgs (\xs -> k (x : xs))
