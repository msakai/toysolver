{-# OPTIONS_GHC -Wall #-}
module Data.LA.FOL
  ( toFOLFormula
  , fromFOLExpr
  , toFOLExpr
  ) where

import Control.Monad

import Data.Expr
import Data.Formula
import Data.Linear

import qualified Data.LA as LA

-- ---------------------------------------------------------------------------

toFOLFormula :: LA.Atom Rational -> Formula (Atom Rational)
toFOLFormula r = Atom $ fmap toFOLExpr r

fromFOLExpr :: Expr Rational -> Maybe (LA.Expr Rational)
fromFOLExpr (Const c) = return (LA.constant c)
fromFOLExpr (Var v)   = return (LA.var v)
fromFOLExpr (a :+: b) = liftM2 (.+.) (fromFOLExpr a) (fromFOLExpr b)
fromFOLExpr (a :*: b) = do
  a' <- fromFOLExpr a
  b' <- fromFOLExpr b
  msum [ do{ c <- LA.asConst a'; return (c .*. b') }
       , do{ c <- LA.asConst b'; return (c .*. a') }
       ]
fromFOLExpr (a :/: b) = do
  a' <- fromFOLExpr a
  b' <- fromFOLExpr b
  c <- LA.asConst b'
  guard $ c /= 0
  return (a' ./. c)

toFOLExpr :: LA.Expr Rational -> Expr Rational
toFOLExpr e =
  case map f (LA.terms e) of
    []  -> Const 0
    [t] -> t
    ts  -> foldr1 (*) ts
  where
    f (c,x)
      | x == LA.unitVar = Const c
      | otherwise       = Const c * Var x

-- ---------------------------------------------------------------------------
