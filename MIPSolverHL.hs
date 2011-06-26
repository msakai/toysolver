{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wall #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  MIPSolverHL
-- Copyright   :  (c) Masahiro Sakai 2011
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  portable
--
-----------------------------------------------------------------------------

module MIPSolverHL
  ( module Expr
  , module Formula
  , minimize
  , maximize
  , optimize
--  , solve
  ) where

import Control.Monad.State
import Data.Maybe
import Data.List (maximumBy)
import Data.Function
import qualified Data.IntMap as IM
import qualified Data.IntSet as IS

import Expr
import Formula
import LA
import qualified Simplex
import Util (isInteger, fracPart)
import LPSolver

-- ---------------------------------------------------------------------------

maximize :: RealFrac r => Expr r -> [Atom r] -> VarSet -> OptResult r
maximize = optimize False

minimize :: RealFrac r => Expr r -> [Atom r] -> VarSet -> OptResult r
minimize = optimize True

optimize :: RealFrac r => Bool -> Expr r -> [Atom r] -> VarSet -> OptResult r
optimize isMinimize obj2 cs2 ivs = fromMaybe OptUnknown $ do
  obj <- compileExpr obj2  
  cs <- mapM compileAtom cs2
  return (optimize' isMinimize obj cs ivs)

{-
solve :: RealFrac r => [Atom r] -> VarSet -> SatResult r
solve cs2 ivs = fromMaybe Unknown $ do
  cs <- mapM compileAtom cs2
  return (solve' cs ivs)
-}

-- ---------------------------------------------------------------------------

optimize' :: RealFrac r => Bool -> LC r -> [Constraint r] -> VarSet -> OptResult r
optimize' isMinimize obj cs ivs =
  flip evalState (1 + maximum ((-1) : IS.toList vs), IM.empty, IS.empty, IM.empty) $ do
    tableau cs
    ret <- phaseI
    if not ret
      then return OptUnsat
      else do
        ret2 <- simplex isMinimize obj
        if not ret2
          then return Unbounded
               -- FIXME: original problem might not be unbounded 
               -- even if LP relaxiation is unbounded.
          else loop
  where
    vs = vars cs `IS.union` vars obj

    loop = do
      tbl <- getTableau
      let xs = [ (fracPart val, m)
               | v <- IS.toList ivs
               , Just (m, val) <- return (IM.lookup v tbl)
               , not (isInteger val)
               ]
      if null xs
        then do
          model <- getModel vs
          return $ Optimum (Simplex.currentObjValue tbl) model
        else do
          let (f0, m) = maximumBy (compare `on` fst) xs
          tbl <- getTableau
          s <- gensym
          putTableau $ IM.insert s (IM.map (negate . fracPart) m, negate f0) tbl
          ret <- dualSimplex isMinimize obj
          if ret
            then loop
            else return OptUnsat

-- ---------------------------------------------------------------------------

example1 = (isMinimize, obj, cs, ivs)
  where
    isMinimize = False
    x1 = varLC 1
    x2 = varLC 2
    x3 = varLC 3
    x4 = varLC 4
    obj = x1 .+. 2 .*. x2 .+. 3 .*. x3 .+. x4
    cs =
      [ LARel ((-1) .*. x1 .+. x2 .+. x3 .+. 10.*.x4) Le (constLC 20)
      , LARel (x1 .-. 3 .*. x2 .+. x3) Le (constLC 30)
      , LARel (x2 .-. 3.5 .*. x4) Eql (constLC 0)
      , LARel (constLC 0) Le x1
      , LARel x1 Le (constLC 40)
      , LARel (constLC 0) Le x2
      , LARel (constLC 0) Le x3
      , LARel (constLC 2) Le x4
      , LARel x4 Le (constLC 3)
      ]
    ivs = IS.singleton 4

test1 :: OptResult Rational
test1 = optimize' isMinimize obj cs ivs
  where
    (isMinimize, obj, cs, ivs) = example1

test2 :: OptResult Rational
test2 = optimize' (not isMinimize) (negateLC obj) cs ivs
  where
    (isMinimize, obj, cs, ivs) = example1

-- ---------------------------------------------------------------------------
