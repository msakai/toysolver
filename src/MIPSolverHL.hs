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
-- References:
-- 
-- Ralph E. Gomory.
-- An Algorithm for the Mixed Integer Problem, Technical Report
-- RM-2597, The Rand Corporation, Santa Monica, CA.
-- http://www.rand.org/pubs/research_memoranda/RM2597.html
--
-- Ralph E. Gomory.
-- Outline of an algorithm for integer solutions to linear programs.
-- Bull. Amer. Math. Soc., Vol. 64, No. 5. (1958), pp. 275-278.
-- http://projecteuclid.org/euclid.bams/1183522679
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
import qualified OmegaTest

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
    ivs2 <- tableau' cs ivs
    ret <- phaseI
    if not ret
      then return OptUnsat
      else do
        ret2 <- simplex isMinimize obj
        if ret2
          then loop (ivs `IS.union` ivs2)
          else
            if IS.null ivs
            then return Unbounded
            else
              {-
                 Fallback to Fourier-Motzkin + OmegaTest
                 * In general, original problem may have optimal
                   solution even though LP relaxiation is unbounded.
                 * But if restricted to rational numbers, the
                   original problem is unbounded or unsatisfiable
                   when LP relaxation is unbounded.
              -}
              case OmegaTest.solveQFLA (map conv cs) ivs of
                Nothing -> return OptUnsat
                Just _ -> return Unbounded
  where
    vs = vars cs `IS.union` vars obj

    loop ivs = do
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
          let g x = if x >= 0 then x else (f0 / (f0 - 1)) * x
          putTableau $ IM.insert s (IM.map (negate . g) m, negate f0) tbl
          ret <- dualSimplex isMinimize obj
          if ret
            then loop ivs
            else return OptUnsat

tableau' :: (RealFrac r) => [Constraint r] -> VarSet -> LP r VarSet
tableau' cs ivs = do
  let (nonnegVars, cs') = collectNonnegVars cs ivs
      fvs = vars cs `IS.difference` nonnegVars
  ivs2 <- liftM IS.unions $ forM (IS.toList fvs) $ \v -> do
    v1 <- gensym
    v2 <- gensym
    define v (varLC v1 .-. varLC v2)
    return $ if v `IS.member` ivs then IS.fromList [v1,v2] else IS.empty
  mapM_ addConstraint cs'
  return ivs2

conv :: RealFrac r => Constraint r -> Constraint Rational
conv (LARel a op b) = LARel (f a) op (f b)
  where
    f (LC t) = normalizeLC $ LC (fmap toRational t)

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
test2 = optimize' (not isMinimize) (lnegate obj) cs ivs
  where
    (isMinimize, obj, cs, ivs) = example1

-- ---------------------------------------------------------------------------
