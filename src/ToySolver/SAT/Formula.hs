{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_HADDOCK show-extensions #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ViewPatterns #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.SAT.Formula
-- Copyright   :  (c) Masahiro Sakai 2012-2021
-- License     :  BSD-style
--
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  non-portable
--
-----------------------------------------------------------------------------
module ToySolver.SAT.Formula
  (
  -- * Boolean formula type
    Formula (Atom, And, Or, Not, Equiv, Imply, ITE)
  , fold
  , evalFormula
  , simplify
  ) where

import Control.Monad.ST
import Data.Hashable
import qualified Data.HashTable.Class as H
import qualified Data.HashTable.ST.Cuckoo as C
import Data.Interned
import GHC.Generics
import ToySolver.Data.Boolean
import qualified ToySolver.Data.BoolExpr as BoolExpr
import qualified ToySolver.SAT.Types as SAT

-- Should this module be merged into ToySolver.SAT.Types module?

-- ------------------------------------------------------------------------

-- | Arbitrary formula not restricted to CNF
data Formula = Formula {-# UNPACK #-} !Id UFormula

instance Eq Formula where
  Formula i _ == Formula j _ = i == j

instance Show Formula where
  showsPrec d x = showsPrec d (toBoolExpr x)

instance Read Formula where
  readsPrec d s = [(fromBoolExpr b, rest) | (b, rest) <- readsPrec d s]

instance Hashable Formula where
  hashWithSalt s (Formula i _) = hashWithSalt s i

data UFormula
  = UAtom SAT.Lit
  | UAnd [Formula]
  | UOr [Formula]
  | UNot Formula
  | UImply Formula Formula
  | UEquiv Formula Formula
  | UITE Formula Formula Formula

instance Interned Formula where
  type Uninterned Formula = UFormula
  data Description Formula
    = DAtom SAT.Lit
    | DAnd [Id]
    | DOr [Id]
    | DNot Id
    | DImply Id Id
    | DEquiv Id Id
    | DITE Id Id Id
    deriving (Eq, Generic)
  describe (UAtom a) = DAtom a
  describe (UAnd xs) = DAnd [i | Formula i _ <- xs]
  describe (UOr xs) = DOr [i | Formula i _ <- xs]
  describe (UNot (Formula i _)) = DNot i
  describe (UImply (Formula i _) (Formula j _)) = DImply i j
  describe (UEquiv (Formula i _) (Formula j _)) = DEquiv i j
  describe (UITE (Formula i _) (Formula j _) (Formula k _)) = DITE i j k
  identify = Formula
  cache = formulaCache

instance Hashable (Description Formula)

instance Uninternable Formula where
  unintern (Formula _ uformula) = uformula

formulaCache :: Cache Formula
formulaCache = mkCache
{-# NOINLINE formulaCache #-}

-- ------------------------------------------------------------------------

pattern Atom :: SAT.Lit -> Formula
pattern Atom l <- (unintern -> UAtom l) where
  Atom l = intern (UAtom l)

pattern Not :: Formula -> Formula
pattern Not p <- (unintern -> UNot p) where
  Not p = intern (UNot p)

pattern And :: [Formula] -> Formula
pattern And ps <- (unintern -> UAnd ps) where
  And ps = intern (UAnd ps)

pattern Or :: [Formula] -> Formula
pattern Or ps <- (unintern -> UOr ps) where
  Or ps = intern (UOr ps)

pattern Equiv :: Formula -> Formula -> Formula
pattern Equiv p q <- (unintern -> UEquiv p q) where
  Equiv p q = intern (UEquiv p q)

pattern Imply :: Formula -> Formula -> Formula
pattern Imply p q <- (unintern -> UImply p q) where
  Imply p q = intern (UImply p q)

pattern ITE :: Formula -> Formula -> Formula -> Formula
pattern ITE p q r <- (unintern -> UITE p q r) where
  ITE p q r = intern (UITE p q r)

{-# COMPLETE Atom, Not, And, Or, Equiv, Imply, ITE #-}

-- ------------------------------------------------------------------------

instance Complement Formula where
  notB = intern . UNot

instance MonotoneBoolean Formula where
  andB = intern . UAnd
  orB  = intern . UOr

instance IfThenElse Formula Formula where
  ite c t e = intern (UITE c t e)

instance Boolean Formula where
  (.=>.) p q = intern (UImply p q)
  (.<=>.) p q = intern (UEquiv p q)

-- ------------------------------------------------------------------------

fold :: Boolean b => (SAT.Lit -> b) -> Formula -> b
fold f formula = runST $ do
  h <- C.newSized 256
  let g x = do
        m <- H.lookup h x
        case m of
          Just y -> return y
          Nothing -> do
            y <-
              case x of
                Atom lit -> return (f lit)
                And ps -> andB <$> mapM g ps
                Or ps -> orB <$> mapM g ps
                Not p -> notB <$> g p
                Imply p q -> (.=>.) <$> g p <*> g q
                Equiv p q -> (.<=>.) <$> g p <*> g q
                ITE p q r -> ite <$> g p <*> g q <*> g r
            H.insert h x y
            return y
  g formula

evalFormula :: SAT.IModel m => m -> Formula -> Bool
evalFormula m = fold (SAT.evalLit m)

toBoolExpr :: Formula -> BoolExpr.BoolExpr SAT.Lit
toBoolExpr = fold BoolExpr.Atom

fromBoolExpr :: BoolExpr.BoolExpr SAT.Lit -> Formula
fromBoolExpr = BoolExpr.fold Atom

-- ------------------------------------------------------------------------

simplify :: Formula -> Formula
simplify = runSimplify . fold (Simplify . Atom)

newtype Simplify = Simplify{ runSimplify :: Formula }

instance Complement Simplify where
  notB (Simplify (Not x)) = Simplify x
  notB (Simplify x) = Simplify (Not x)

instance MonotoneBoolean (Simplify) where
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

instance IfThenElse Simplify Simplify where
  ite (Simplify c) (Simplify t) (Simplify e)
    | isTrue c  = Simplify t
    | isFalse c = Simplify e
    | otherwise = Simplify (ITE c t e)

instance Boolean Simplify where
  Simplify x .=>. Simplify y
    | isFalse x = true
    | isTrue y  = true
    | isTrue x  = Simplify y
    | isFalse y = notB (Simplify x)
    | otherwise = Simplify (x .=>. y)

isTrue :: Formula -> Bool
isTrue (And []) = True
isTrue _ = False

isFalse :: Formula -> Bool
isFalse (Or []) = True
isFalse _ = False

-- ------------------------------------------------------------------------
