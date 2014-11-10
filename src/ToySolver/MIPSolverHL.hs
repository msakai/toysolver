{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wall #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.MIPSolverHL
-- Copyright   :  (c) Masahiro Sakai 2011
-- License     :  BSD-style
--
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  non-portable (ScopedTypeVariables)
--
-- References:
-- 
-- * [Gomory1960]
--   Ralph E. Gomory.
--   An Algorithm for the Mixed Integer Problem, Technical Report
--   RM-2597, 1960, The Rand Corporation, Santa Monica, CA.
--   <http://www.rand.org/pubs/research_memoranda/RM2597.html>
--
-- * [Gomory1958]
--   Ralph E. Gomory.
--   Outline of an algorithm for integer solutions to linear programs.
--   Bull. Amer. Math. Soc., Vol. 64, No. 5. (1958), pp. 275-278.
--   <http://projecteuclid.org/euclid.bams/1183522679>
-----------------------------------------------------------------------------

module ToySolver.MIPSolverHL
  ( module Data.OptDir
  , OptResult (..)
  , minimize
  , maximize
  , optimize
  ) where

import Control.Exception
import Control.Monad.State
import Data.Default.Class
import Data.Ord
import Data.Maybe
import Data.List (maximumBy)
import qualified Data.IntMap as IM
import qualified Data.IntSet as IS
import Data.OptDir
import Data.VectorSpace

import ToySolver.Data.ArithRel
import ToySolver.Data.Var
import qualified ToySolver.Data.LA as LA
import qualified ToySolver.Simplex as Simplex
import qualified ToySolver.LPSolver as LPSolver
import ToySolver.LPSolver hiding (OptResult (..))
import ToySolver.LPSolverHL (OptResult (..))
import qualified ToySolver.OmegaTest as OmegaTest
import ToySolver.Internal.Util (isInteger, fracPart)

-- ---------------------------------------------------------------------------

data Node r
  = Node
  { ndSolver :: LPSolver.Solver r
  , ndDepth  :: {-# UNPACK #-} !Int
--  , ndCutSlackVariables :: VarSet
  }

ndTableau :: Node r  -> Simplex.Tableau r
ndTableau node = evalState getTableau (ndSolver node)

ndLowerBound :: (Num r, Eq r) => Node r -> r
ndLowerBound node = evalState (liftM Simplex.currentObjValue getTableau) (ndSolver node)

data Err = ErrUnbounded | ErrUnsat deriving (Ord, Eq, Show, Enum, Bounded)

maximize :: RealFrac r => LA.Expr r -> [LA.Atom r] -> VarSet -> OptResult r
maximize = optimize OptMax

minimize :: RealFrac r => LA.Expr r -> [LA.Atom r] -> VarSet -> OptResult r
minimize = optimize OptMin

optimize :: RealFrac r => OptDir -> LA.Expr r -> [LA.Atom r] -> VarSet -> OptResult r
optimize optdir obj cs ivs = 
  case mkInitialNode optdir obj cs ivs of
    Left err ->
      case err of
        ErrUnsat -> OptUnsat
        ErrUnbounded ->
          if IS.null ivs
          then Unbounded
          else
            {-
               Fallback to Fourier-Motzkin + OmegaTest
               * In general, original problem may have optimal
                 solution even though LP relaxiation is unbounded.
               * But if restricted to rational numbers, the
                 original problem is unbounded or unsatisfiable
                 when LP relaxation is unbounded.
            -}
            case OmegaTest.solveQFLA def (vars cs `IS.union` ivs) (map conv cs) ivs of
              Nothing -> OptUnsat
              Just _ -> Unbounded        
    Right (node0, ivs2) -> 
      case traverse optdir obj ivs2 node0 of
        Left ErrUnbounded -> error "shoud not happen"
        Left ErrUnsat -> OptUnsat
        Right node -> flip evalState (ndSolver node) $ do
          tbl <- getTableau
          model <- getModel vs
          return $ Optimum (Simplex.currentObjValue tbl) model
  where
    vs = vars cs `IS.union` vars obj

tableau' :: (RealFrac r) => [LA.Atom r] -> VarSet -> LP r VarSet
tableau' cs ivs = do
  let (nonnegVars, cs') = collectNonnegVars cs ivs
      fvs = vars cs `IS.difference` nonnegVars
  ivs2 <- liftM IS.unions $ forM (IS.toList fvs) $ \v -> do
    v1 <- newVar
    v2 <- newVar
    define v (LA.var v1 ^-^ LA.var v2)
    return $ if v `IS.member` ivs then IS.fromList [v1,v2] else IS.empty
  mapM_ addConstraint cs'
  return ivs2

conv :: RealFrac r => LA.Atom r -> LA.Atom Rational
conv = fmap (LA.mapCoeff toRational)

mkInitialNode :: RealFrac r => OptDir -> LA.Expr r -> [LA.Atom r] -> VarSet -> Either Err (Node r, VarSet)
mkInitialNode optdir obj cs ivs =
  flip evalState (emptySolver vs) $ do
    ivs2 <- tableau' cs ivs
    ret <- LPSolver.twoPhaseSimplex optdir obj
    case ret of
      LPSolver.Unsat -> return (Left ErrUnsat)
      LPSolver.Unbounded -> return (Left ErrUnbounded)
      LPSolver.Optimum -> do
        solver <- get
        return $ Right $
          ( Node{ ndSolver = solver
                , ndDepth = 0
--                , ndCutSlackVariables = IS.empty
                }
          , ivs `IS.union` ivs2
          )
  where
    vs = vars cs `IS.union` vars obj

isStrictlyBetter :: RealFrac r => OptDir -> r -> r -> Bool
isStrictlyBetter optdir = if optdir==OptMin then (<) else (>)

traverse :: forall r. RealFrac r => OptDir -> LA.Expr r -> VarSet -> Node r -> Either Err (Node r)
traverse optdir obj ivs node0 = loop [node0] Nothing
  where
    loop :: [Node r] -> Maybe (Node r) -> Either Err (Node r)
    loop [] (Just best) = Right best
    loop [] Nothing = Left ErrUnsat
    loop (n:ns) Nothing =
      case children n of
        Nothing -> loop ns (Just n)
        Just cs -> loop (cs++ns) Nothing
    loop (n:ns) (Just best)
      | isStrictlyBetter optdir (ndLowerBound n) (ndLowerBound best) =
          case children n of
            Nothing -> loop ns (Just n)
            Just cs -> loop (cs++ns) (Just best)
      | otherwise = loop ns (Just best)

    reopt :: Solver r -> Maybe (Solver r)
    reopt s = flip evalState s $ do
      ret <- dualSimplex optdir obj
      if ret
        then liftM Just get
        else return Nothing

    children :: Node r -> Maybe [Node r]
    children node
      | null xs = Nothing -- no violation
      | ndDepth node `mod` 100 == 0 = -- cut
          let
            (f0, m0) = maximumBy (comparing fst) [(fracPart val, m) | (_,m,val) <- xs]
            sv = flip execState (ndSolver node) $ do
                   s <- newVar
                   let g j x = assert (a >= 0) a
                         where
                           a | j `IS.member` ivs =
                                if fracPart x <= f0
                                then fracPart x
                                else (f0 / (f0 - 1)) * (fracPart x - 1)
                                     -- [Gomory1960] では (f0 / (1 - f0)) * (fracPart x - 1) としているが、
                                     -- これは誤り
                             | otherwise =
                                if x >= 0
                                then x
                                else (f0 / (f0 - 1)) * x
                   putTableau $ IM.insert s (IM.mapWithKey (\j x -> negate (g j x)) m0, negate f0) tbl
          in Just $ [node{ ndSolver = sv2, ndDepth = ndDepth node + 1 } | sv2 <- maybeToList (reopt sv)]
      | otherwise = -- branch
          let (v0, val0) = snd $ maximumBy (comparing fst) [(fracPart val, (v, val)) | (v,_,val) <- xs]
              cs = [ LA.var v0 .>=. LA.constant (fromIntegral (ceiling val0 :: Integer))
                   , LA.var v0 .<=. LA.constant (fromIntegral (floor val0 :: Integer))
                   ]
              svs = [execState (addConstraint c) (ndSolver node) | c <- cs]
          in Just $ [node{ ndSolver = sv, ndDepth = ndDepth node + 1 } | Just sv <- map reopt svs]
        
      where
        tbl :: Simplex.Tableau r
        tbl = ndTableau node

        xs :: [(Var, VarMap r, r)]
        xs = [ (v, m, val)
             | v <- IS.toList ivs
             , Just (m, val) <- return (IM.lookup v tbl)
             , not (isInteger val)
             ]

-- ---------------------------------------------------------------------------

example1 :: (Fractional r, Eq r) => (OptDir, LA.Expr r, [LA.Atom r], VarSet)
example1 = (optdir, obj, cs, ivs)
  where
    optdir = OptMax
    x1 = LA.var 1
    x2 = LA.var 2
    x3 = LA.var 3
    x4 = LA.var 4
    obj = x1 ^+^ 2 *^ x2 ^+^ 3 *^ x3 ^+^ x4
    cs =
      [ (-1) *^ x1 ^+^ x2 ^+^ x3 ^+^ 10*^x4 .<=. LA.constant 20
      , x1 ^-^ 3 *^ x2 ^+^ x3 .<=. LA.constant 30
      , x2 ^-^ 3.5 *^ x4 .==. LA.constant 0
      , LA.constant 0 .<=. x1
      , x1 .<=. LA.constant 40
      , LA.constant 0 .<=. x2
      , LA.constant 0 .<=. x3
      , LA.constant 2 .<=. x4
      , x4 .<=. LA.constant 3
      ]
    ivs = IS.singleton 4

test1 :: Bool
test1 = result==expected
  where
    (optdir, obj, cs, ivs) = example1
    result, expected :: OptResult Rational
    result = optimize optdir obj cs ivs
    expected = Optimum (245/2) (IM.fromList [(1,40),(2,21/2),(3,39/2),(4,3)])

test1' :: Bool
test1' = result==expected
  where
    (optdir, obj, cs, ivs) = example1
    f OptMin = OptMax
    f OptMax = OptMin
    result, expected :: OptResult Rational
    result = optimize (f optdir) (negateV obj) cs ivs
    expected = Optimum (-245/2) (IM.fromList [(1,40),(2,21/2),(3,39/2),(4,3)])

-- 『数理計画法の基礎』(坂和 正敏) p.109 例 3.8
example2 :: (Fractional r, Eq r) => (OptDir, LA.Expr r, [LA.Atom r], VarSet)
example2 = (optdir, obj, cs, ivs)
  where
    optdir = OptMin
    [x1,x2,x3] = map LA.var [1..3]
    obj = (-1) *^ x1 ^-^ 3 *^ x2 ^-^ 5 *^ x3
    cs =
      [ 3 *^ x1 ^+^ 4 *^ x2 .<=. LA.constant 10
      , 2 *^ x1 ^+^ x2 ^+^ x3 .<=. LA.constant 7
      , 3*^x1 ^+^ x2 ^+^ 4 *^ x3 .==. LA.constant 12
      , LA.constant 0 .<=. x1
      , LA.constant 0 .<=. x2
      , LA.constant 0 .<=. x3
      ]
    ivs = IS.fromList [1,2]

test2 :: Bool
test2 = result == expected
  where
    result, expected :: OptResult Rational
    result = optimize optdir obj cs ivs
    expected = Optimum (-37/2) (IM.fromList [(1,0),(2,2),(3,5/2)])
    (optdir, obj, cs, ivs) = example2

-- ---------------------------------------------------------------------------
