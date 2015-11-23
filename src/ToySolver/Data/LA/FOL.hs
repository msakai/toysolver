{-# OPTIONS_GHC -Wall #-}
module ToySolver.Data.LA.FOL
  ( fromFOLAtom
  , toFOLFormula
  , fromFOLExpr
  , toFOLExpr
  ) where

import Control.Monad
import Data.VectorSpace

import ToySolver.Data.OrdRel
import ToySolver.Data.FOL.Arith
import qualified ToySolver.Data.LA as LA

-- ---------------------------------------------------------------------------

fromFOLAtom :: (Real r, Fractional r) => Atom r -> Maybe (LA.Atom r)
fromFOLAtom (OrdRel a op b) = do
  a' <- fromFOLExpr a
  b' <- fromFOLExpr b
  return $ ordRel op a' b'

toFOLFormula :: (Real r, Fractional r) => LA.Atom r -> Formula (Atom r)
toFOLFormula r = Atom $ fmap toFOLExpr r

fromFOLExpr :: (Real r, Fractional r) => Expr r -> Maybe (LA.Expr r)
fromFOLExpr (Const c) = return (LA.constant c)
fromFOLExpr (Var v)   = return (LA.var v)
fromFOLExpr (a :+: b) = liftM2 (^+^) (fromFOLExpr a) (fromFOLExpr b)
fromFOLExpr (a :*: b) = do
  a' <- fromFOLExpr a
  b' <- fromFOLExpr b
  msum [ do{ c <- LA.asConst a'; return (c *^ b') }
       , do{ c <- LA.asConst b'; return (c *^ a') }
       ]
fromFOLExpr (a :/: b) = do
  a' <- fromFOLExpr a
  b' <- fromFOLExpr b
  c <- LA.asConst b'
  guard $ c /= 0
  return (a' ^/ c)

toFOLExpr :: (Real r, Fractional r) => LA.Expr r -> Expr r
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
