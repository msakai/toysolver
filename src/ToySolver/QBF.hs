{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE BangPatterns #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.QBF
-- Copyright   :  (c) Masahiro Sakai 2016
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  non-portable (BangPatterns)
--
-- Reference:
--
-- * Mikoláš Janota, William Klieber, Joao Marques-Silva, Edmund Clarke.
--   Solving QBF with Counterexample Guided Refinement.
--   In Theory and Applications of Satisfiability Testing (SAT 2012), pp. 114-128.
--   <http://dx.doi.org/10.1007/978-3-642-31612-8_10>
--   <https://www.cs.cmu.edu/~wklieber/papers/qbf-cegar-sat-2012.pdf>
--
-----------------------------------------------------------------------------
module ToySolver.QBF
  ( Quantifier (..)
  , Prefix
  , normalizePrefix
  , quantifyFreeVariables 
  , Matrix
  , solveNaive
  ) where

import Control.Monad
import Control.Monad.Trans
import Control.Monad.Trans.Except
import qualified Data.IntSet as IntSet
import Data.Function (on)
import Data.List (groupBy)
import Data.Maybe

import ToySolver.Data.Boolean
import ToySolver.Data.BoolExpr (BoolExpr)
import qualified ToySolver.Data.BoolExpr as BoolExpr
import qualified ToySolver.SAT as SAT
import ToySolver.SAT.Types (LitSet, VarSet) 
import qualified ToySolver.SAT.TseitinEncoder as Tseitin

import ToySolver.Text.QDimacs (Quantifier (..))
import qualified ToySolver.Text.QDimacs as QDimacs

-- ----------------------------------------------------------------------------

type Prefix = [(Quantifier, VarSet)]

normalizePrefix :: Prefix -> Prefix
normalizePrefix = groupQuantifiers . removeEmptyQuantifiers

removeEmptyQuantifiers :: Prefix -> Prefix
removeEmptyQuantifiers = filter (\(_,xs) -> not (IntSet.null xs))

groupQuantifiers :: Prefix -> Prefix
groupQuantifiers = map f . groupBy ((==) `on` fst)
  where
    f qs = (fst (head qs), IntSet.unions [xs | (_,xs) <- qs])

quantifyFreeVariables :: Int -> Prefix -> Prefix
quantifyFreeVariables nv prefix
  | IntSet.null rest = prefix
  | otherwise = (E, rest) : prefix
  where
    rest = IntSet.fromList [1..nv] `IntSet.difference` IntSet.unions [vs | (_q, vs) <- prefix]

-- ----------------------------------------------------------------------------

type Matrix = BoolExpr SAT.Lit

reduct :: Matrix -> LitSet -> Matrix
reduct m ls = BoolExpr.simplify $ m >>= s
  where
    s l
      |   l  `IntSet.member` ls = true
      | (-l) `IntSet.member` ls = false
      | otherwise = BoolExpr.Atom l

-- ----------------------------------------------------------------------------

-- | Naive Algorithm for a Winning Move
solveNaive :: Int -> Prefix -> Matrix -> IO (Bool, Maybe LitSet)
solveNaive nv prefix matrix =
  case prefix' of
    [] -> if BoolExpr.fold undefined matrix
          then return (True, Just IntSet.empty)
          else return (False, Nothing)
    (E,_) : _ -> do
      m <- f prefix' matrix
      return (isJust m, m)
    (A,_) : _ -> do
      m <- f prefix' matrix
      return (isNothing m, m)
  where
    prefix' = normalizePrefix prefix

    {- Naive Algorithm for a Winning Move
    Function Solve (QX. Φ)
    begin
      if Φ has no quant then
        return (Q = ∃) ? SAT(φ) : SAT(¬φ)
      Λ ← {true, false}^X  // consider all assignments
      while true do
        if Λ = ∅ then      // all assignments used up
          return NULL
        τ ← pick(Λ)        // pick a candidate solution
        μ ← Solve(Φ[τ])    // find a countermove
        if μ = NULL then   // winning move
          return τ
        Λ ← Λ \ {τ}        // remove bad candidate
      end
    end
    -}
    f :: Prefix -> Matrix -> IO (Maybe LitSet)
    f [] _matrix = error "should not happen"
    f [(q,xs)] matrix = do
      solver <- SAT.newSolver
      SAT.newVars_ solver nv
      enc <- Tseitin.newEncoder solver
      case q of
        E -> Tseitin.addFormula enc matrix
        A -> Tseitin.addFormula enc (notB matrix)
      ret <- SAT.solve solver
      if ret then do
        m <- SAT.getModel solver
        return $ Just $ IntSet.fromList [if SAT.evalLit m x then x else -x | x <- IntSet.toList xs]
      else
        return Nothing
    f ((_q,xs) : prefix') matrix = do
      ret <- runExceptT $ do
        let moves :: [LitSet]
            moves = map IntSet.fromList $ sequence [[x, -x] | x <- IntSet.toList xs]
        forM_ moves $ \tau -> do
          ret <- lift $ f prefix' (reduct matrix tau)
          case ret of
            Nothing  -> throwE tau
            Just _nu -> return ()
      case ret of
        Left tau -> return (Just tau)
        Right () -> return Nothing

-- ----------------------------------------------------------------------------

-- ∀y ∃x. x ∧ (y ∨ ¬x)
test = solveNaive 2 [(A, IntSet.singleton 2), (E, IntSet.singleton 1)] (x .&&. (y .||. notB x))
  where
    x  = BoolExpr.Atom 1
    y  = BoolExpr.Atom 2
