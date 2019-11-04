{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# OPTIONS_GHC -Wall #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.Data.BoolExpr
-- Copyright   :  (c) Masahiro Sakai 2014-2015
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  non-portable (MultiParamTypeClasses, DeriveDataTypeable, FlexibleContexts, FlexibleInstances)
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
  , simplify
  ) where

import Control.DeepSeq
import Control.Monad
import Data.Data
import Data.Hashable
import Data.Traversable
import ToySolver.Data.Boolean
import ToySolver.Data.IntVar

-- | Boolean expression over a given type of atoms
data BoolExpr a
  = Atom a
  | And [BoolExpr a]
  | Or [BoolExpr a]
  | Not (BoolExpr a)
  | Imply (BoolExpr a) (BoolExpr a)
  | Equiv (BoolExpr a) (BoolExpr a)
  | ITE (BoolExpr a) (BoolExpr a) (BoolExpr a)
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
  traverse f (ITE c t e) = ITE <$> traverse f c <*> traverse f t <*> traverse f e

instance NFData a => NFData (BoolExpr a) where
  rnf (Atom a) = rnf a
  rnf (And xs) = rnf xs
  rnf (Or xs) = rnf xs
  rnf (Not x) = rnf x
  rnf (Imply x y) = rnf x `seq` rnf y
  rnf (Equiv x y) = rnf x `seq` rnf y
  rnf (ITE c t e) = rnf c `seq` rnf t `seq` rnf e

instance Hashable a => Hashable (BoolExpr a) where
  hashWithSalt s (Atom a) = s `hashWithSalt` (0::Int) `hashWithSalt` a
  hashWithSalt s (And xs) = s `hashWithSalt` (1::Int) `hashWithSalt` xs
  hashWithSalt s (Or xs)  = s `hashWithSalt` (2::Int) `hashWithSalt` xs
  hashWithSalt s (Not x)  = s `hashWithSalt` (3::Int) `hashWithSalt` x
  hashWithSalt s (Imply x y) = s `hashWithSalt` (4::Int) `hashWithSalt` x `hashWithSalt` y
  hashWithSalt s (Equiv x y) = s `hashWithSalt` (5::Int) `hashWithSalt` x `hashWithSalt` y
  hashWithSalt s (ITE c t e) = s `hashWithSalt` (6::Int) `hashWithSalt` c `hashWithSalt` t `hashWithSalt` e

instance Complement (BoolExpr a) where
  notB = Not

instance MonotoneBoolean (BoolExpr a) where
  andB = And
  orB  = Or

instance IfThenElse (BoolExpr a) (BoolExpr a) where
  ite = ITE

instance Boolean (BoolExpr a) where
  (.=>.) = Imply
  (.<=>.) = Equiv

instance Variables a => Variables (BoolExpr a) where
  vars = foldMap vars


fold :: Boolean b => (atom -> b) -> BoolExpr atom -> b
fold f = g
  where
    g (Atom a) = f a
    g (Or xs) = orB (map g xs)
    g (And xs) = andB (map g xs)
    g (Not x) = notB (g x)
    g (Imply x y) = g x .=>. g y
    g (Equiv x y) = g x .<=>. g y
    g (ITE c t e) = ite (g c) (g t) (g e)

{-# RULES
  "fold/fmap"    forall f g e.  fold f (fmap g e) = fold (f.g) e
 #-}

instance Eval m a Bool => Eval m (BoolExpr a) Bool where
  eval m = fold (eval m)

simplify :: BoolExpr a -> BoolExpr a
simplify = runSimplify . fold (Simplify . Atom)

newtype Simplify a = Simplify{ runSimplify :: BoolExpr a }

instance Complement (Simplify a) where
  notB (Simplify (Not x)) = Simplify x
  notB (Simplify x) = Simplify (Not x)

instance MonotoneBoolean (Simplify a) where
  orB xs
    | any isTrue ys = Simplify true
    | otherwise = Simplify $ Or ys
    where
      ys = concat [f x | Simplify x <- xs]
      f (Or zs) = zs
      f z = [z]
  andB xs 
    | any isFalse ys = Simplify false
    | otherwise = Simplify $ And ys
    where
      ys = concat [f x | Simplify x <- xs]
      f (And zs) = zs
      f z = [z]

instance IfThenElse (Simplify a) (Simplify a) where
  ite (Simplify c) (Simplify t) (Simplify e)
    | isTrue c  = Simplify t
    | isFalse c = Simplify e
    | otherwise = Simplify (ITE c t e)

instance Boolean (Simplify a) where
  Simplify x .=>. Simplify y
    | isFalse x = true
    | isTrue y  = true
    | isTrue x  = Simplify y
    | isFalse y = notB (Simplify x)
    | otherwise = Simplify (x .=>. y)

isTrue :: BoolExpr a -> Bool
isTrue (And []) = True
isTrue _ = False

isFalse :: BoolExpr a -> Bool
isFalse (Or []) = True
isFalse _ = False
