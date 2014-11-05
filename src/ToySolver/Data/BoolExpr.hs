{-# LANGUAGE DeriveDataTypeable #-}
{-# OPTIONS_GHC -Wall #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.Data.BoolExpr
-- Copyright   :  (c) Masahiro Sakai 2014
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  portable
--
-- Boolean expression over a given type of atoms
-- 
-----------------------------------------------------------------------------
module ToySolver.Data.BoolExpr
  (
  -- * BoolExpr type
    BoolExpr (..)

  -- * Operations
  , fold
  ) where

import Control.Applicative
import Control.DeepSeq
import Control.Monad
import Data.Data
import Data.Foldable hiding (fold)
import Data.Hashable
import Data.Traversable
import ToySolver.Data.Boolean

-- | Boolean expression over a given type of atoms
data BoolExpr a
  = Atom a
  | And [BoolExpr a]
  | Or [BoolExpr a]
  | Not (BoolExpr a)
  | Imply (BoolExpr a) (BoolExpr a)
  | Equiv (BoolExpr a) (BoolExpr a)
  deriving (Eq, Ord, Show, Read, Typeable, Data)

instance Functor BoolExpr where
  fmap = fmapDefault

instance Applicative BoolExpr where
  pure = Atom
  (<*>) = ap

instance Monad BoolExpr where
  return = pure
  m >>= f = fold f m

instance Foldable BoolExpr where
  foldMap = foldMapDefault

instance Traversable BoolExpr where
  traverse f (Atom x) = Atom <$> f x
  traverse f (And xs) = And <$> sequenceA (fmap (traverse f) xs)
  traverse f (Or xs) = Or <$> sequenceA (fmap (traverse f) xs)
  traverse f (Not x) = Not <$> traverse f x
  traverse f (Imply x y) = Imply <$> traverse f x <*> traverse f y
  traverse f (Equiv x y) = Equiv <$> traverse f x <*> traverse f y

instance NFData a => NFData (BoolExpr a) where
  rnf (Atom a) = rnf a
  rnf (And xs) = rnf xs
  rnf (Or xs) = rnf xs
  rnf (Not x) = rnf x
  rnf (Imply x y) = rnf x `seq` rnf y
  rnf (Equiv x y) = rnf x `seq` rnf y

instance Hashable a => Hashable (BoolExpr a) where
  hashWithSalt s (Atom a) = s `hashWithSalt` (0::Int) `hashWithSalt` a
  hashWithSalt s (And xs) = s `hashWithSalt` (1::Int) `hashWithSalt` xs
  hashWithSalt s (Or xs)  = s `hashWithSalt` (2::Int) `hashWithSalt` xs
  hashWithSalt s (Not x)  = s `hashWithSalt` (3::Int) `hashWithSalt` x
  hashWithSalt s (Imply x y) = s `hashWithSalt` (4::Int) `hashWithSalt` x `hashWithSalt` y
  hashWithSalt s (Equiv x y) = s `hashWithSalt` (5::Int) `hashWithSalt` x `hashWithSalt` y

instance Complement (BoolExpr a) where
  notB = Not

instance MonotoneBoolean (BoolExpr a) where
  andB = And
  orB  = Or

instance Boolean (BoolExpr a) where
  (.=>.) = Imply
  (.<=>.) = Equiv

fold :: Boolean b => (atom -> b) -> BoolExpr atom -> b
fold f = g
  where
    g (Atom a) = f a
    g (Or xs) = orB (map g xs)
    g (And xs) = andB (map g xs)
    g (Not x) = notB (g x)
    g (Imply x y) = g x .=>. g y
    g (Equiv x y) = g x .<=>. g y

