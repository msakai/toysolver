{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wall #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  MIPSolverHL
-- Copyright   :  (c) Masahiro Sakai 2011
-- License     :  BSD-style
-- Maintainer  :  masahiro.sakai@gmail.com
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

data Node r
  = Node
  { ndSolver :: LPSolver.Solver r
  , ndDepth  :: {-# UNPACK #-} !Int
--  , ndCutSlackVariables :: VarSet
  }

ndTableau :: Node r -> Simplex.Tableau r
ndTableau node = evalState getTableau (ndSolver node)

ndLowerBound :: Num r => Node r -> r
ndLowerBound node = evalState (liftM Simplex.currentObjValue getTableau) (ndSolver node)

data Err = ErrUnbounded | ErrUnsat deriving (Ord, Eq, Show, Enum, Bounded)

optimize' :: RealFrac r => Bool -> LC r -> [Constraint r] -> VarSet -> OptResult r
optimize' isMinimize obj cs ivs = 
  case mkInitialNode isMinimize obj cs ivs of
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
            case OmegaTest.solveQFLA (map conv cs) ivs of
              Nothing -> OptUnsat
              Just _ -> Unbounded        
    Right (node0, ivs2) -> 
      case traverse isMinimize obj ivs2 node0 of
        Left ErrUnbounded -> error "shoud not happen"
        Left ErrUnsat -> OptUnsat
        Right node -> flip evalState (ndSolver node) $ do
          tbl <- getTableau
          model <- getModel vs
          return $ Optimum (Simplex.currentObjValue tbl) model
  where
    vs = vars cs `IS.union` vars obj

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

mkInitialNode :: RealFrac r => Bool -> LC r -> [Constraint r] -> VarSet -> Either Err (Node r, VarSet)
mkInitialNode isMinimize obj cs ivs =
  flip evalState (emptySolver vs) $ do
    ivs2 <- tableau' cs ivs
    ret <- phaseI
    if not ret
      then return (Left ErrUnsat)
      else do
        ret2 <- simplex isMinimize obj
        if ret2
          then do
            solver <- get
            return $ Right $
              ( Node{ ndSolver = solver
                    , ndDepth = 0
--                    , ndCutSlackVariables = IS.empty
                    }
              , ivs `IS.union` ivs2
              )
          else return (Left ErrUnbounded)
  where
    vs = vars cs `IS.union` vars obj

isStrictlyBetter :: RealFrac r => Bool -> r -> r -> Bool
isStrictlyBetter isMinimize = if isMinimize then (<) else (>)

traverse :: forall r. RealFrac r => Bool -> LC r -> VarSet -> Node r -> Either Err (Node r)
traverse isMinimize obj ivs node0 = loop [node0] Nothing
  where
    loop :: [Node r] -> Maybe (Node r) -> Either Err (Node r)
    loop [] (Just best) = Right best
    loop [] Nothing = Left ErrUnsat
    loop (n:ns) Nothing =
      case children n of
        Nothing -> loop ns (Just n)
        Just cs -> loop (cs++ns) Nothing
    loop (n:ns) (Just best)
      | isStrictlyBetter isMinimize (ndLowerBound n) (ndLowerBound best) =
          case children n of
            Nothing -> loop ns (Just n)
            Just cs -> loop (cs++ns) (Just best)
      | otherwise = loop ns (Just best)

    reopt :: Solver r -> Maybe (Solver r)
    reopt s = flip evalState s $ do
      ret <- dualSimplex isMinimize obj
      if ret
        then liftM Just get
        else return Nothing

    children :: Node r -> Maybe [Node r]
    children node
      | null xs = Nothing -- no violation
      | ndDepth node `mod` 100 == 0 = -- cut
          let
            (f0, m0) = maximumBy (compare `on` fst) [(fracPart val, m) | (_,m,val) <- xs]
            sv = flip execState (ndSolver node) $ do
                   s <- gensym
                   let g j x =
                        if j `IS.member` ivs
                        then
                          if fracPart x <= f0
                          then fracPart x
                          else (f0 / (f0 - 1)) * (fracPart x - 1)
                        else
                          if x >= 0
                          then x
                          else (f0 / (f0 - 1)) * x
                   putTableau $ IM.insert s (IM.mapWithKey (\j x -> negate (g j x)) m0, negate f0) tbl
          in Just $ [node{ ndSolver = sv2, ndDepth = ndDepth node + 1 } | sv2 <- maybeToList (reopt sv)]
      | otherwise = -- branch
          let (v0, val0) = snd $ maximumBy (compare `on` fst) [(fracPart val, (v, val)) | (v,_,val) <- xs]
              cs = [ LARel (varLC v0) Ge (constLC (fromIntegral (ceiling val0 :: Integer)))
                   , LARel (varLC v0) Le (constLC (fromIntegral (floor val0 :: Integer)))
                   ]
              svs = [execState (addConstraint2 c) (ndSolver node) | c <- cs]
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
