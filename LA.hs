-----------------------------------------------------------------------------
-- |
-- Module      :  LA
-- Copyright   :  (c) Masahiro Sakai 2011
-- License     :  BSD-style
-- 
-----------------------------------------------------------------------------
module LA
  ( module LC
  , Constraint (..)
  , Bounds
  , compileExpr
  , compileAtom
  ) where

import Control.Monad
import qualified Data.IntSet as IS
import Expr
import Formula
import LC
import Interval

data Constraint r = LARel (LC r) RelOp (LC r)
    deriving (Show, Eq, Ord)

instance Variables (Constraint r) where
  vars (LARel a _ b) = vars a `IS.union` vars b

type Bounds r = VarMap (Interval r)

compileExpr :: (Real r, Fractional r) => Expr r -> Maybe (LC r)
compileExpr (Const c) = return (constLC c)
compileExpr (Var c) = return (varLC c)
compileExpr (a :+: b) = liftM2 (.+.) (compileExpr a) (compileExpr b)
compileExpr (a :*: b) = do
  x <- compileExpr a
  y <- compileExpr b
  msum [ do{ c <- asConst x; return (c .*. y) }
       , do{ c <- asConst y; return (c .*. x) }
       ]
compileExpr (a :/: b) = do
  x <- compileExpr a
  c <- asConst =<< compileExpr b
  return $ (1/c) .*. x

compileAtom :: (Real r, Fractional r) => Atom r -> Maybe (Constraint r)
compileAtom (Rel a op b) = do
  a' <- compileExpr a
  b' <- compileExpr b
  return $ LARel a' op b'
