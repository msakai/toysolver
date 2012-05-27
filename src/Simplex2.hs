{-# LANGUAGE DoAndIfThenElse, TypeSynonymInstances, FlexibleContexts, FlexibleInstances #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Simplex2
-- Copyright   :  (c) Masahiro Sakai 2012
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  non-portable (DoAndIfThenElse, TypeSynonymInstances, FlexibleContexts, FlexibleInstances)
--
-- Naïve implementation of Simplex method
-- 
-- Reference:
--
-- * <http://www.math.cuhk.edu.hk/~wei/lpch3.pdf>
-- 
-- * Bruno Dutertre and Leonardo de Moura.
--   A Fast Linear-Arithmetic Solver for DPLL(T).
--   Computer Aided Verification In Computer Aided Verification, Vol. 4144 (2006), pp. 81-94.
--   <http://yices.csl.sri.com/cav06.pdf>
--
-- * Bruno Dutertre and Leonardo de Moura.
--   Integrating Simplex with DPLL(T).
--   CSL Technical Report SRI-CSL-06-01. 2006.
--   <http://yices.csl.sri.com/sri-csl-06-01.pdf>
--
-----------------------------------------------------------------------------
module Simplex2
  (
  -- * The @Solver@ type
    Solver
  , GenericSolver
  , SolverValue (..)
  , newSolver
  , cloneSolver

  -- * Problem specification
  , Var
  , newVar
  , RelOp (..)
  , (.<=.), (.>=.), (.==.), (.<.), (.>.)
  , Atom (..)
  , assertAtom
  , assertAtomEx
  , assertLower
  , assertUpper
  , setObj
  , OptDir (..)
  , setOptDir
  , getOptDir

  -- * Solving
  , check
  , Options (..)
  , defaultOptions
  , OptResult (..)
  , optimize
  , dualSimplex

  -- * Extract results
  , Model
  , model
  , RawModel
  , rawModel
  , getValue
  , getObjValue

  -- * Reading status
  , getTableau
  , getRow
  , getCol
  , getCoeff
  , nVars
  , isBasicVariable
  , isNonBasicVariable
  , isFeasible
  , isOptimal
  , getLB
  , getUB

  -- * Configulation
  , setLogger
  , clearLogger
  , PivotStrategy (..)
  , setPivotStrategy

  -- * Debug
  , dump
  ) where

import Prelude hiding (log)
import Control.Exception
import Control.Monad
import Data.Ord
import Data.IORef
import Data.List
import Data.Maybe
import Data.Ratio
import qualified Data.Map as Map
import qualified Data.IntMap as IM
import Text.Printf
import Data.OptDir
import System.CPUTime

import qualified LA as LA
import LA (Atom (..))
import qualified Formula as F
import Formula (RelOp (..), (.<=.), (.>=.), (.==.), (.<.), (.>.))
import Linear
import Delta
import Util (showRational)

{--------------------------------------------------------------------
  The @Solver@ type
--------------------------------------------------------------------}

type Var = Int

data GenericSolver v
  = GenericSolver
  { svTableau :: !(IORef (IM.IntMap (LA.Expr Rational)))
  , svLB      :: !(IORef (IM.IntMap v))
  , svUB      :: !(IORef (IM.IntMap v))
  , svModel   :: !(IORef (IM.IntMap v))
  , svVCnt    :: !(IORef Int)
  , svOk      :: !(IORef Bool)
  , svOptDir  :: !(IORef OptDir)

  , svDefDB  :: !(IORef (Map.Map (LA.Expr Rational) Var))

  , svLogger :: !(IORef (Maybe (String -> IO ())))
  , svPivotStrategy :: !(IORef PivotStrategy)
  , svNPivot  :: !(IORef Int)
  }

type Solver = GenericSolver Rational

-- special basic variable
objVar :: Int
objVar = -1

newSolver :: SolverValue v => IO (GenericSolver v)
newSolver = do
  t <- newIORef (IM.singleton objVar lzero)
  l <- newIORef IM.empty
  u <- newIORef IM.empty
  m <- newIORef (IM.singleton objVar lzero)
  v <- newIORef 0
  ok <- newIORef True
  dir <- newIORef OptMin
  defs <- newIORef Map.empty
  logger <- newIORef Nothing
  pivot <- newIORef PivotStrategyBlandRule
  npivot <- newIORef 0
  return $
    GenericSolver
    { svTableau = t
    , svLB      = l
    , svUB      = u
    , svModel   = m
    , svVCnt    = v
    , svOk      = ok
    , svOptDir  = dir
    , svDefDB   = defs
    , svLogger  = logger
    , svNPivot  = npivot
    , svPivotStrategy = pivot
    }

cloneSolver :: GenericSolver v -> IO (GenericSolver v)
cloneSolver solver = do
  t      <- newIORef =<< readIORef (svTableau solver)
  l      <- newIORef =<< readIORef (svLB solver)
  u      <- newIORef =<< readIORef (svUB solver)
  m      <- newIORef =<< readIORef (svModel solver)
  v      <- newIORef =<< readIORef (svVCnt solver)
  ok     <- newIORef =<< readIORef (svOk solver)
  dir    <- newIORef =<< readIORef (svOptDir solver)
  defs   <- newIORef =<< readIORef (svDefDB solver)
  logger <- newIORef =<< readIORef (svLogger solver)
  pivot  <- newIORef =<< readIORef (svPivotStrategy solver)
  npivot <- newIORef =<< readIORef (svNPivot solver)
  return $
    GenericSolver
    { svTableau = t
    , svLB      = l
    , svUB      = u
    , svModel   = m
    , svVCnt    = v
    , svOk      = ok
    , svOptDir  = dir
    , svDefDB   = defs
    , svLogger  = logger
    , svNPivot  = npivot
    , svPivotStrategy = pivot
    }  

class (Linear Rational v, Ord v) => SolverValue v where
  toValue :: Rational -> v
  showValue :: Bool -> v -> String
  model :: GenericSolver v -> IO Model

instance SolverValue Rational where
  toValue = id
  showValue = showRational
  model = rawModel

instance SolverValue (Delta Rational) where
  toValue = fromReal
  showValue = showDelta
  model solver = do
    xs <- variables solver
    ys <- liftM concat $ forM xs $ \x -> do
      Delta p q  <- getValue solver x
      lb <- getLB solver x
      ub <- getUB solver x
      return $
        [(p - c) / (k - q) | Just (Delta c k) <- return lb, c < p, k > q] ++
        [(d - p) / (q - h) | Just (Delta d h) <- return ub, p < d, q > h]
    let delta0 :: Rational
        delta0 = if null ys then 0.1 else minimum ys
        f :: Delta Rational -> Rational
        f (Delta r k) = r + k * delta0
    liftM (IM.map f) $ readIORef (svModel solver)

{-
Largest coefficient rule: original rule suggested by G. Dantzig.
Largest increase rule: computationally more expensive in comparison with Largest coefficient, but locally maximizes the progress.
Steepest edge rule: best pivot rule in practice, an efficient approximate implementation is "Devex".
Bland’s rule: avoids cycling but one of the slowest rules.
Random edge rule: Randomized have lead to the current best provable bounds for the number of pivot steps of the simplex method.
Lexicographic rule: used for avoiding cyclying.
-}
data PivotStrategy
  = PivotStrategyBlandRule
  | PivotStrategyLargestCoefficient
--  | PivotStrategySteepestEdge
  deriving (Eq, Ord, Enum, Show, Read)

setPivotStrategy :: GenericSolver v -> PivotStrategy -> IO ()
setPivotStrategy solver ps = writeIORef (svPivotStrategy solver) ps

{--------------------------------------------------------------------
  problem description
--------------------------------------------------------------------}

newVar :: SolverValue v => GenericSolver v -> IO Var
newVar solver = do
  v <- readIORef (svVCnt solver)
  writeIORef (svVCnt solver) $! v+1
  modifyIORef (svModel solver) (IM.insert v lzero)
  return v

assertAtom :: Solver -> LA.Atom Rational -> IO ()
assertAtom solver atom = do
  (v,op,rhs') <- simplifyAtom solver atom
  case op of
    F.Le  -> assertUpper solver v (toValue rhs')
    F.Ge  -> assertLower solver v (toValue rhs')
    F.Eql -> do
      assertLower solver v (toValue rhs')
      assertUpper solver v (toValue rhs')
    _ -> error "unsupported"
  return ()

assertAtomEx :: GenericSolver (Delta Rational) -> LA.Atom Rational -> IO ()
assertAtomEx solver atom = do
  (v,op,rhs') <- simplifyAtom solver atom
  case op of
    F.Le  -> assertUpper solver v (toValue rhs')
    F.Ge  -> assertLower solver v (toValue rhs')
    F.Lt  -> assertUpper solver v (toValue rhs' .-. delta)
    F.Gt  -> assertLower solver v (toValue rhs' .+. delta)
    F.Eql -> do
      assertLower solver v (toValue rhs')
      assertUpper solver v (toValue rhs')
  return ()

simplifyAtom :: SolverValue v => GenericSolver v -> LA.Atom Rational -> IO (Var, F.RelOp, Rational)
simplifyAtom solver (LA.Atom lhs op rhs) = do
  let (lhs',rhs') =
        case LA.extract LA.unitVar (lhs .-. rhs) of
          (n,e) -> (e, -n)
  case LA.terms lhs' of
    [(1,v)] -> return (v, op, rhs')
    [(-1,v)] -> return (v, F.flipOp op, -rhs')
    _ -> do
      defs <- readIORef (svDefDB solver)
      let (c,lhs'') = scale lhs' -- lhs' = lhs'' / c = rhs'
          rhs'' = c .*. rhs'
          op''  = if c < 0 then F.flipOp op else op
      case Map.lookup lhs'' defs of
        Just v -> do
          return (v,op'',rhs'')
        Nothing -> do
          v <- newVar solver
          setRow solver v lhs''
          modifyIORef (svDefDB solver) $ Map.insert lhs'' v
          return (v,op'',rhs'')
  where
    scale :: LA.Expr Rational -> (Rational, LA.Expr Rational)
    scale e = (c, c .*. e)
      where
        c = c1 * c2
        c1 = fromIntegral $ foldl' lcm 1 [denominator c | (c, _) <- LA.terms e]
        c2 = signum $ head ([c | (c,x) <- LA.terms e] ++ [1])

assertLower :: SolverValue v => GenericSolver v -> Var -> v -> IO ()
assertLower solver x l = do
  l0 <- getLB solver x
  u0 <- getUB solver x
  case (l0,u0) of 
    (Just l0', _) | l <= l0' -> return ()
    (_, Just u0') | u0' < l -> markBad solver
    _ -> do
      modifyIORef (svLB solver) (IM.insert x l)
      b <- isNonBasicVariable solver x
      v <- getValue solver x
      when (b && not (l <= v)) $ update solver x l
      checkNBFeasibility solver

assertUpper :: SolverValue v => GenericSolver v -> Var -> v -> IO ()
assertUpper solver x u = do
  l0 <- getLB solver x
  u0 <- getUB solver x
  case (l0,u0) of 
    (_, Just u0') | u0' <= u -> return ()
    (Just l0', _) | u < l0' -> markBad solver
    _ -> do
      modifyIORef (svUB solver) (IM.insert x u)
      b <- isNonBasicVariable solver x
      v <- getValue solver x
      when (b && not (v <= u)) $ update solver x u
      checkNBFeasibility solver

-- FIXME: 式に定数項が含まれる可能性を考えるとこれじゃまずい?
setObj :: SolverValue v => GenericSolver v -> LA.Expr Rational -> IO ()
setObj solver e = setRow solver objVar e

setRow :: SolverValue v => GenericSolver v -> Var -> LA.Expr Rational -> IO ()
setRow solver v e = do
  modifyIORef (svTableau solver) $ \t ->
    IM.insert v (LA.applySubst t e) t
  modifyIORef (svModel solver) $ \m -> 
    IM.insert v (LA.evalLinear m (toValue 1) e) m  

setOptDir :: GenericSolver v -> OptDir -> IO ()
setOptDir solver dir = writeIORef (svOptDir solver) dir

getOptDir :: GenericSolver v -> IO OptDir
getOptDir solver = readIORef (svOptDir solver)

{--------------------------------------------------------------------
  Status
--------------------------------------------------------------------}

nVars :: GenericSolver v -> IO Int
nVars solver = readIORef (svVCnt solver)

isBasicVariable :: GenericSolver v -> Var -> IO Bool
isBasicVariable solver v = do
  t <- readIORef (svTableau solver)
  return $ v `IM.member` t

isNonBasicVariable  :: GenericSolver v -> Var -> IO Bool
isNonBasicVariable solver x = liftM not (isBasicVariable solver x)

isFeasible :: SolverValue v => GenericSolver v -> IO Bool
isFeasible solver = do
  xs <- variables solver
  liftM and $ forM xs $ \x -> do
    v <- getValue solver x
    l <- getLB solver x
    u <- getUB solver x
    return (testLB l v && testUB u v)

isOptimal :: SolverValue v => GenericSolver v -> IO Bool
isOptimal solver = do
  obj <- getRow solver objVar
  ret <- selectEnteringVariable solver
  return $! isNothing ret

{--------------------------------------------------------------------
  Satisfiability solving
--------------------------------------------------------------------}

check :: SolverValue v => GenericSolver v -> IO Bool
check solver = do
  let
    loop :: IO Bool
    loop = do
      -- select the smallest basic variable xi such that β(xi) < li or β(xi) > ui
      m <- selectViolatingBasicVariable solver

      case m of
        Nothing -> return True
        Just xi  -> do
          li <- getLB solver xi
          vi <- getValue solver xi
          if not (testLB li vi)
            then do
              -- select the smallest non-basic variable xj such that
              -- (aij > 0 and β(xj) < uj) or (aij < 0 and β(xj) > lj)
              let q :: (Rational, Var) -> IO Bool
                  q (aij, xj) = do
                    l <- getLB solver xj
                    u <- getUB solver xj
                    v <- getValue solver xj
                    return $ (aij > 0 && (isNothing u || v < fromJust u)) ||
                             (aij < 0 && (isNothing l || fromJust l < v))

                  find :: IO (Maybe Var)
                  find = do
                    xi_def <- getRow solver xi
                    liftM (fmap snd) $ findM q (LA.terms xi_def)
              r <- find
              case r of
                Nothing -> markBad solver >> return False
                Just xj -> do
                  l <- getLB solver xi
                  pivotAndUpdate solver xi xj (fromJust l)
                  loop
            else do
              -- select the smallest non-basic variable xj such that
              -- (aij < 0 and β(xj) < uj) or (aij > 0 and β(xj) > lj)
              let q :: (Rational, Var) -> IO Bool
                  q (aij, xj) = do
                    l <- getLB solver xj
                    u <- getUB solver xj
                    v <- getValue solver xj
                    return $ (aij < 0 && (isNothing u || v < fromJust u)) ||
                             (aij > 0 && (isNothing l || fromJust l < v))

                  find :: IO (Maybe Var)
                  find = do
                    xi_def <- getRow solver xi
                    liftM (fmap snd) $ findM q (LA.terms xi_def)
              r <- find
              case r of
                Nothing -> markBad solver >> return False
                Just xj -> do
                  u <- getUB solver xi
                  pivotAndUpdate solver xi xj (fromJust u)
                  loop

  ok <- readIORef (svOk solver)
  if not ok
  then return False
  else do
    log solver "check"
    result <- recordTime solver loop
    when result $ checkFeasibility solver
    return result

-- select the smallest basic variable xi such that β(xi) < li or β(xi) > ui
selectViolatingBasicVariable :: SolverValue v => GenericSolver v -> IO (Maybe Var)
selectViolatingBasicVariable solver = do
  let
    p :: Var -> IO Bool
    p x | x == objVar = return False
    p xi = do
      li <- getLB solver xi
      ui <- getUB solver xi
      vi <- getValue solver xi
      return $ not (testLB li vi) || not (testUB ui vi)
  vs <- basicVariables solver

  ps <- readIORef (svPivotStrategy solver)
  case ps of
    PivotStrategyBlandRule ->
      findM p vs
    PivotStrategyLargestCoefficient -> do
      xs <- filterM p vs
      case xs of
        [] -> return Nothing
        _ -> do
          xs2 <- forM xs $ \xi -> do
              vi <- getValue solver xi
              li <- getLB solver xi
              ui <- getUB solver xi
              if not (testLB li vi)
                then return (xi, fromJust li .-. vi)
                else return (xi, vi .-. fromJust ui)
          return $ Just $ fst $ maximumBy (comparing snd) xs2

{--------------------------------------------------------------------
  Optimization
--------------------------------------------------------------------}

-- | results of optimization
data OptResult = Optimum | Unsat | Unbounded | ObjLimit
  deriving (Show, Eq, Ord)

data Options
  = Options
  { objLimit :: Maybe Rational
  }
  deriving (Show, Eq, Ord)

defaultOptions :: Options
defaultOptions
  = Options
  { objLimit = Nothing
  }

optimize :: Solver -> Options -> IO OptResult
optimize solver opt = do
  ret <- do
    is_fea <- isFeasible solver
    if is_fea then return True else check solver
  if not ret
    then return Unsat -- unsat
    else do
      log solver "optimize"
      result <- recordTime solver loop
      when (result == Optimum) $ checkOptimality solver
      return result
  where
    loop :: IO OptResult
    loop = do
      checkFeasibility solver
      ret <- selectEnteringVariable solver
      case ret of
       Nothing -> return Optimum
       Just (c,xj) -> do
         dir <- readIORef (svOptDir solver)
         r <- if dir==OptMin
              then if c > 0
                then decreaseNB solver xj -- xj を小さくして目的関数を小さくする
                else increaseNB solver xj -- xj を大きくして目的関数を小さくする
              else if c > 0
                then increaseNB solver xj -- xj を大きくして目的関数を大きくする
                else decreaseNB solver xj -- xj を小さくして目的関数を大きくする
         if r
           then loop
           else return Unbounded

selectEnteringVariable :: SolverValue v => GenericSolver v -> IO (Maybe (Rational, Var))
selectEnteringVariable solver = do
  ps <- readIORef (svPivotStrategy solver)
  obj_def <- getRow solver objVar
  case ps of
    PivotStrategyBlandRule ->
      findM canEnter (LA.terms obj_def)
    PivotStrategyLargestCoefficient -> do
      ts <- filterM canEnter (LA.terms obj_def)
      case ts of
        [] -> return Nothing
        _ -> return $ Just $ snd $ maximumBy (comparing fst) [(abs c, (c,xj)) | (c,xj) <- ts]
  where
    canEnter :: (Rational, Var) -> IO Bool
    canEnter (_,xj) | xj == LA.unitVar = return False
    canEnter (c,xj) = do
      dir <- readIORef (svOptDir solver)
      if dir==OptMin then
        if c > 0 then canDecrease solver xj      -- xを小さくすることで目的関数を小さくできる
        else if c < 0 then canIncrease solver xj -- xを大きくすることで目的関数を小さくできる
        else return False
      else
        if c > 0 then canIncrease solver xj      -- xを大きくすることで目的関数を大きくできる
        else if c < 0 then canDecrease solver xj -- xを小さくすることで目的関数を大きくできる
        else return False

canDecrease :: SolverValue v => GenericSolver v -> Var -> IO Bool
canDecrease solver x = do
  l <- getLB solver x
  v <- getValue solver x
  case l of
    Nothing -> return True
    Just lv -> return $! (lv < v)

canIncrease :: SolverValue v => GenericSolver v -> Var -> IO Bool
canIncrease solver x = do
  u <- getUB solver x
  v <- getValue solver x
  case u of
    Nothing -> return True
    Just uv -> return $! (v < uv)

-- | feasibility を保ちつつ non-basic variable xj の値を大きくする
increaseNB :: Solver -> Var -> IO Bool
increaseNB solver xj = do
  col <- getCol solver xj

  -- Upper bounds of θ
  -- NOTE: xj 自体の上限も考慮するのに注意
  ubs <- liftM concat $ forM ((xj,1) : IM.toList col) $ \(xi,aij) -> do
    v1 <- getValue solver xi
    li <- getLB solver xi
    ui <- getUB solver xi
    return [ assert (theta >= lzero) ((xi,v2), theta)
           | Just v2 <- [ui | aij > 0] ++ [li | aij < 0]
           , let theta = (v2 .-. v1) ./. aij ]

  -- β(xj) := β(xj) + θ なので θ を大きく
  case ubs of
    [] -> return False -- unbounded
    _ -> do
      let (xi, v) = fst $ minimumBy (comparing snd) ubs
      pivotAndUpdate solver xi xj v
      return True

-- | feasibility を保ちつつ non-basic variable xj の値を小さくする
decreaseNB :: Solver -> Var -> IO Bool
decreaseNB solver xj = do
  col <- getCol solver xj

  -- Lower bounds of θ
  -- NOTE: xj 自体の下限も考慮するのに注意
  lbs <- liftM concat $ forM ((xj,1) : IM.toList col) $ \(xi,aij) -> do
    v1 <- getValue solver xi
    li <- getLB solver xi
    ui <- getUB solver xi
    return [ assert (theta <= lzero) ((xi,v2), theta)
           | Just v2 <- [li | aij > 0] ++ [ui | aij < 0]
           , let theta = (v2 .-. v1) ./. aij ]

  -- β(xj) := β(xj) + θ なので θ を小さく
  case lbs of
    [] -> return False -- unbounded
    _ -> do
      let (xi, v) = fst $ maximumBy (comparing snd) lbs
      pivotAndUpdate solver xi xj v
      return True

dualSimplex :: Solver -> Options -> IO OptResult
dualSimplex solver opt = do
  let
    loop :: IO OptResult
    loop = do
      checkOptimality solver

      p <- prune solver opt
      if p
        then return ObjLimit
        else do
          -- select the smallest basic variable xi such that β(xi) < li or β(xi) > ui
          m <- selectViolatingBasicVariable solver
          case m of
            Nothing -> return Optimum
            Just xi  -> do
              li <- getLB solver xi
              vi <- getValue solver xi
              if not (testLB li vi)
                then do
                  -- select non-basic variable xj such that
                  -- (aij > 0 and β(xj) < uj) or (aij < 0 and β(xj) > lj)
                  let q :: (Rational, Var) -> IO Bool
                      q (aij, xj) = do
                        l <- getLB solver xj
                        u <- getUB solver xj
                        v <- getValue solver xj
                        return $ (aij > 0 && (isNothing u || v < fromJust u)) ||
                                 (aij < 0 && (isNothing l || fromJust l < v))
    
                      find :: IO (Maybe Var)
                      find = do
                        dir <- readIORef (svOptDir solver)
                        obj_def <- getRow solver objVar
                        xi_def  <- getRow solver xi
                        ws <- liftM concat $ forM (LA.terms xi_def) $ \(aij, xj) -> do
                          b <- q (aij, xj)
                          if b
                          then do
                            let cj = LA.coeff xj obj_def
                            let ratio = if dir==OptMin then (cj / aij) else - (cj / aij)
                            return [(xj, ratio) | ratio >= 0]
                          else
                            return []
                        case ws of
                          [] -> return Nothing
                          _ -> return $ Just $ fst $ minimumBy (comparing snd) ws
                  r <- find
                  case r of
                    Nothing -> markBad solver >> return Unsat
                    Just xj -> do
                      l <- getLB solver xi
                      pivotAndUpdate solver xi xj (fromJust l)
                      loop
                else do
                  -- select non-basic variable xj such that
                  -- (aij < 0 and β(xj) < uj) or (aij > 0 and β(xj) > lj)
                  let q :: (Rational, Var) -> IO Bool
                      q (aij, xj) = do
                        l <- getLB solver xj
                        u <- getUB solver xj
                        v <- getValue solver xj
                        return $ (aij < 0 && (isNothing u || v < fromJust u)) ||
                                 (aij > 0 && (isNothing l || fromJust l < v))
    
                      find :: IO (Maybe Var)
                      find = do
                        dir <- readIORef (svOptDir solver)
                        obj_def <- getRow solver objVar
                        xi_def  <- getRow solver xi
                        ws <- liftM concat $ forM (LA.terms xi_def) $ \(aij, xj) -> do
                          b <- q (aij, xj)
                          if b
                          then do
                            let cj = LA.coeff xj obj_def
                            let ratio = if dir==OptMin then - (cj / aij) else (cj / aij)
                            return [(xj, ratio) | ratio >= 0]
                          else
                            return []
                        case ws of
                          [] -> return Nothing
                          _ -> return $ Just $ fst $ minimumBy (comparing snd) ws
                  r <- find
                  case r of
                    Nothing -> markBad solver >> return Unsat
                    Just xj -> do
                      u <- getUB solver xi
                      pivotAndUpdate solver xi xj (fromJust u)
                      loop

  ok <- readIORef (svOk solver)
  if not ok
  then return Unsat
  else do
    log solver "dual simplex"
    result <- recordTime solver loop
    when (result == Optimum) $ checkFeasibility solver
    return result

prune :: Solver -> Options -> IO Bool
prune solver opt =
  case objLimit opt of
    Nothing -> return False
    Just lim -> do    
      o <- getObjValue solver
      dir <- getOptDir solver
      case dir of
        OptMin -> return $! (lim <= o)
        OptMax -> return $! (lim >= o)

{--------------------------------------------------------------------
  Extract results
--------------------------------------------------------------------}

type RawModel v = IM.IntMap v

rawModel :: GenericSolver v -> IO (RawModel v)
rawModel solver = do
  xs <- variables solver
  liftM IM.fromList $ forM xs $ \x -> do
    val <- getValue solver x
    return (x,val)

getObjValue :: GenericSolver v -> IO v
getObjValue solver = getValue solver objVar  

type Model = IM.IntMap Rational
  
{--------------------------------------------------------------------
  major function
--------------------------------------------------------------------}

update :: SolverValue v => GenericSolver v -> Var -> v -> IO ()
update solver xj v = do
  -- log solver $ printf "before update x%d (%s)" xj (show v)
  -- dump solver

  v0 <- getValue solver xj
  let diff = v .-. v0

  aj <- getCol solver xj
  modifyIORef (svModel solver) $ \m ->
    let m2 = IM.map (\aij -> aij .*. diff) aj
    in IM.insert xj v $ IM.unionWith (.+.) m2 m

  -- log solver $ printf "after update x%d (%s)" xj (show v)
  -- dump solver

pivot :: SolverValue v => GenericSolver v -> Var -> Var -> IO ()
pivot solver xi xj = do
  modifyIORef' (svNPivot solver) (+1)
  modifyIORef' (svTableau solver) $ \defs ->
    case LA.solveFor (LA.Atom (LA.varExpr xi) F.Eql (defs IM.! xi)) xj of
      Just (F.Eql, xj_def) ->
        IM.insert xj xj_def . IM.map (LA.applySubst1 xj xj_def) . IM.delete xi $ defs
      _ -> error "pivot: should not happen"

pivotAndUpdate :: SolverValue v => GenericSolver v -> Var -> Var -> v -> IO ()
pivotAndUpdate solver xi xj v | xi == xj = update solver xi v -- xi = xj is non-basic variable
pivotAndUpdate solver xi xj v = do
  -- xi is basic variable
  -- xj is non-basic varaible

  -- log solver $ printf "before pivotAndUpdate x%d x%d (%s)" xi xj (show v)
  -- dump solver

  m <- readIORef (svModel solver)

  aj <- getCol solver xj
  let aij = aj IM.! xi
  let theta = (v .-. (m IM.! xi)) ./. aij

  let m' = IM.fromList $
           [(xi, v), (xj, (m IM.! xj) .+. theta)] ++
           [(xk, (m IM.! xk) .+. (akj .*. theta)) | (xk, akj) <- IM.toList aj, xk /= xi]
  writeIORef (svModel solver) (IM.union m' m) -- note that 'IM.union' is left biased.

  pivot solver xi xj

  -- log solver $ printf "after pivotAndUpdate x%d x%d (%s)" xi xj (show v)
  -- dump solver

getLB :: GenericSolver v -> Var -> IO (Maybe v)
getLB solver x = do
  lb <- readIORef (svLB solver)
  return $ IM.lookup x lb

getUB :: GenericSolver v -> Var -> IO (Maybe v)
getUB solver x = do
  ub <- readIORef (svUB solver)
  return $ IM.lookup x ub

getTableau :: GenericSolver v -> IO (IM.IntMap (LA.Expr Rational))
getTableau solver = do
  t <- readIORef (svTableau solver)
  return $ IM.delete objVar t

getValue :: GenericSolver v -> Var -> IO v
getValue solver x = do
  m <- readIORef (svModel solver)
  return $ m IM.! x

getRow :: GenericSolver v -> Var -> IO (LA.Expr Rational)
getRow solver x = do
  -- x should be basic variable or 'objVar'
  t <- readIORef (svTableau solver)
  return $! (t IM.! x)

-- aijが非ゼロの列も全部探しているのは効率が悪い
getCol :: SolverValue v => GenericSolver v -> Var -> IO (IM.IntMap Rational)
getCol solver xj = do
  t <- readIORef (svTableau solver)
  return $ IM.mapMaybe (LA.lookupCoeff xj) t

getCoeff :: GenericSolver v -> Var -> Var -> IO Rational
getCoeff solver xi xj = do
  xi_def <- getRow solver xi
  return $! LA.coeff xj xi_def

markBad :: GenericSolver v -> IO ()
markBad solver = writeIORef (svOk solver) False

{--------------------------------------------------------------------
  utility
--------------------------------------------------------------------}

findM :: Monad m => (a -> m Bool) -> [a] -> m (Maybe a)
findM _ [] = return Nothing
findM p (x:xs) = do
  r <- p x
  if r
  then return (Just x)
  else findM p xs

testLB :: SolverValue v => Maybe v -> v -> Bool
testLB Nothing _  = True
testLB (Just l) x = l <= x

testUB :: SolverValue v => Maybe v -> v -> Bool
testUB Nothing _  = True
testUB (Just u) x = x <= u

variables :: GenericSolver v -> IO [Var]
variables solver = do
  vcnt <- nVars solver
  return [0..vcnt-1]

basicVariables :: GenericSolver v -> IO [Var]
basicVariables solver = do
  t <- readIORef (svTableau solver)
  return (IM.keys t)

modifyIORef' :: IORef a -> (a -> a) -> IO ()
modifyIORef' ref f = do
  x <- readIORef ref
  writeIORef ref $! f x

recordTime :: SolverValue v => GenericSolver v -> IO a -> IO a
recordTime solver act = do
  dumpSize solver
  writeIORef (svNPivot solver) 0

  start <- getCPUTime
  result <- act
  end <- getCPUTime

  (log solver . printf "time = %.3fs") (fromIntegral (end - start) / 10^(12::Int) :: Double)
  (log solver . printf "#pivot = %d") =<< readIORef (svNPivot solver)
  return result

showDelta :: Bool -> Delta Rational -> String
showDelta asRatio v = 
  case v of
    (Delta r k) -> 
      f r ++
        case compare k 0 of
          EQ -> ""
          GT -> " + " ++ f k ++ " delta"
          LT -> " - " ++ f (abs k) ++ " delta"
  where
    f = showRational asRatio

{--------------------------------------------------------------------
  Logging
--------------------------------------------------------------------}

-- | set callback function for receiving messages.
setLogger :: GenericSolver v -> (String -> IO ()) -> IO ()
setLogger solver logger = do
  writeIORef (svLogger solver) (Just logger)

clearLogger :: GenericSolver v -> IO ()
clearLogger solver = writeIORef (svLogger solver) Nothing

log :: GenericSolver v -> String -> IO ()
log solver msg = logIO solver (return msg)

logIO :: GenericSolver v -> IO String -> IO ()
logIO solver action = do
  m <- readIORef (svLogger solver)
  case m of
    Nothing -> return ()
    Just logger -> action >>= logger

{--------------------------------------------------------------------
  debug and tests
--------------------------------------------------------------------}

test4 :: IO ()
test4 = do
  solver <- newSolver
  setLogger solver putStrLn
  x0 <- newVar solver
  x1 <- newVar solver

  writeIORef (svTableau solver) (IM.fromList [(x1, LA.varExpr x0)])
  writeIORef (svLB solver) (IM.fromList [(x0, toValue 0), (x1, toValue 0)])
  writeIORef (svUB solver) (IM.fromList [(x0, toValue 2), (x1, toValue 3)])
  setObj solver (LA.fromTerms [(-1, x0)])

  ret <- optimize solver defaultOptions
  print ret
  dump solver

test5 :: IO ()
test5 = do
  solver <- newSolver
  setLogger solver putStrLn
  x0 <- newVar solver
  x1 <- newVar solver

  writeIORef (svTableau solver) (IM.fromList [(x1, LA.varExpr x0)])
  writeIORef (svLB solver) (IM.fromList [(x0, toValue 0), (x1, toValue 0)])
  writeIORef (svUB solver) (IM.fromList [(x0, toValue 2), (x1, toValue 0)])
  setObj solver (LA.fromTerms [(-1, x0)])

  checkFeasibility solver

  ret <- optimize solver defaultOptions
  print ret
  dump solver

test6 :: IO ()
test6 = do
  solver <- newSolver
  setLogger solver putStrLn
  x0 <- newVar solver

  assertAtom solver (LA.constExpr 1 .<. LA.varExpr x0)
  assertAtom solver (LA.constExpr 2 .>. LA.varExpr x0)

  ret <- check solver
  print ret
  dump solver

  m <- model solver
  print m

dumpSize :: SolverValue v => GenericSolver v -> IO ()
dumpSize solver = do
  t <- readIORef (svTableau solver)
  let nrows = IM.size t - 1 -- -1 is objVar
  xs <- variables solver
  let ncols = length xs - nrows
  let nnz = sum [IM.size $ LA.coeffMap xi_def | (xi,xi_def) <- IM.toList t, xi /= objVar]
  log solver $ printf "%d rows, %d columns, %d non-zeros" nrows ncols nnz

dump :: SolverValue v => GenericSolver v -> IO ()
dump solver = do
  log solver "============="

  log solver "Tableau:"
  t <- readIORef (svTableau solver)
  log solver $ printf "obj = %s" (show (t IM.! objVar))
  forM_ (IM.toList t) $ \(xi, e) -> do
    when (xi /= objVar) $ log solver $ printf "x%d = %s" xi (show e)

  log solver ""

  log solver "Assignments and Bounds:"
  objVal <- getValue solver objVar
  log solver $ printf "beta(obj) = %s" (showValue True objVal)
  xs <- variables solver 
  forM_ xs $ \x -> do
    l <- getLB solver x
    u <- getUB solver x
    v <- getValue solver x
    let f Nothing = "Nothing"
        f (Just x) = showValue True x
    log solver $ printf "beta(x%d) = %s; %s <= x%d <= %s" x (showValue True v) (f l) x (f u)

  log solver ""
  log solver "Status:"
  is_fea <- isFeasible solver
  is_opt <- isOptimal solver
  log solver $ printf "Feasible: %s" (show is_fea)
  log solver $ printf "Optimal: %s" (show is_opt)

  log solver "============="

checkFeasibility :: SolverValue v => GenericSolver v -> IO ()
checkFeasibility _ | True = return ()
checkFeasibility solver = do
  xs <- variables solver
  forM_ xs $ \x -> do
    v <- getValue solver x
    l <- getLB solver x
    u <- getUB solver x
    let f Nothing = "Nothing"
        f (Just x) = showValue True x
    unless (testLB l v) $
      error (printf "(%s) <= x%d is violated; x%d = (%s)" (f l) x x (showValue True v))
    unless (testUB u v) $
      error (printf "x%d <= (%s) is violated; x%d = (%s)" x (f u) x (showValue True v))
    return ()

checkNBFeasibility :: SolverValue v => GenericSolver v -> IO ()
checkNBFeasibility _ | True = return ()
checkNBFeasibility solver = do
  xs <- variables solver
  forM_ xs $ \x -> do
    b <- isNonBasicVariable solver x
    when b $ do
      v <- getValue solver x
      l <- getLB solver x
      u <- getUB solver x
      let f Nothing = "Nothing"
          f (Just x) = showValue True x
      unless (testLB l v) $
        error (printf "checkNBFeasibility: (%s) <= x%d is violated; x%d = (%s)" (f l) x x (showValue True v))
      unless (testUB u v) $
        error (printf "checkNBFeasibility: x%d <= (%s) is violated; x%d = (%s)" x (f u) x (showValue True v))

checkOptimality :: Solver -> IO ()
checkOptimality _ | True = return ()
checkOptimality solver = do
  ret <- selectEnteringVariable solver
  case ret of
    Nothing -> return () -- optimal
    Just (_,x) -> error (printf "checkOptimality: not optimal (x%d can be changed)" x)
