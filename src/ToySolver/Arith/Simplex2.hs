{-# LANGUAGE TypeSynonymInstances, FlexibleInstances, TypeFamilies, CPP #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.Arith.Simplex2
-- Copyright   :  (c) Masahiro Sakai 2012
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  non-portable (TypeSynonymInstances, FlexibleInstances, TypeFamilies, CPP)
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
module ToySolver.Arith.Simplex2
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
  , ConstrID
  , ConstrIDSet
  , assertAtom
  , assertAtom'
  , assertAtomEx
  , assertAtomEx'
  , assertLower
  , assertLower'
  , assertUpper
  , assertUpper'
  , setObj
  , getObj
  , OptDir (..)
  , setOptDir
  , getOptDir

  -- * Solving
  , check
  , pushBacktrackPoint
  , popBacktrackPoint
  , Options (..)
  , OptResult (..)
  , optimize
  , dualSimplex

  -- * Extract results
  , Model
  , getModel
  , RawModel
  , getRawModel
  , getValue
  , getObjValue
  , explain

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
  , Bound
  , boundValue
  , boundExplanation

  -- * Configulation
  , setLogger
  , clearLogger
  , PivotStrategy (..)
  , setPivotStrategy

  -- * Debug
  , dump

  -- * Misc
  , simplifyAtom
  ) where

import Prelude hiding (log)
import Control.Exception
import Control.Monad
import Data.Default.Class
import Data.Ord
import Data.IORef
import Data.List
import Data.Maybe
import Data.Monoid
import Data.Ratio
import Data.Map (Map)
import qualified Data.Map as Map
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import Text.Printf
import Data.OptDir
import Data.VectorSpace
import System.Clock

import qualified ToySolver.Data.LA as LA
import ToySolver.Data.LA (Atom (..))
import ToySolver.Data.OrdRel
import ToySolver.Data.Delta
import ToySolver.Internal.Util (showRational)

{--------------------------------------------------------------------
  The @Solver@ type
--------------------------------------------------------------------}

type Var = Int

data GenericSolver v
  = GenericSolver
  { svTableau :: !(IORef (IntMap (LA.Expr Rational)))
  , svLB      :: !(IORef (IntMap (v, ConstrIDSet)))
  , svUB      :: !(IORef (IntMap (v, ConstrIDSet)))
  , svModel   :: !(IORef (IntMap v))
  , svExplanation :: !(IORef ConstrIDSet)
  , svVCnt    :: !(IORef Int)
  , svOk      :: !(IORef Bool)
  , svOptDir  :: !(IORef OptDir)

  , svDefDB  :: !(IORef (Map (LA.Expr Rational) Var))

  , svLogger :: !(IORef (Maybe (String -> IO ())))
  , svPivotStrategy :: !(IORef PivotStrategy)
  , svNPivot  :: !(IORef Int)

  , svBacktrackPoints :: !(IORef [BacktrackPoint v])
  }

type Solver = GenericSolver Rational

-- special basic variable
objVar :: Int
objVar = -1

newSolver :: SolverValue v => IO (GenericSolver v)
newSolver = do
  t <- newIORef (IntMap.singleton objVar zeroV)
  l <- newIORef IntMap.empty
  u <- newIORef IntMap.empty
  m <- newIORef (IntMap.singleton objVar zeroV)
  e <- newIORef mempty
  v <- newIORef 0
  ok <- newIORef True
  dir <- newIORef OptMin
  defs <- newIORef Map.empty
  logger <- newIORef Nothing
  pivot <- newIORef PivotStrategyBlandRule
  npivot <- newIORef 0
  bps <- newIORef []
  return $
    GenericSolver
    { svTableau = t
    , svLB      = l
    , svUB      = u
    , svModel   = m
    , svExplanation = e
    , svVCnt    = v
    , svOk      = ok
    , svOptDir  = dir
    , svDefDB   = defs
    , svLogger  = logger
    , svNPivot  = npivot
    , svPivotStrategy = pivot
    , svBacktrackPoints = bps
    }

cloneSolver :: GenericSolver v -> IO (GenericSolver v)
cloneSolver solver = do
  t      <- newIORef =<< readIORef (svTableau solver)
  l      <- newIORef =<< readIORef (svLB solver)
  u      <- newIORef =<< readIORef (svUB solver)
  m      <- newIORef =<< readIORef (svModel solver)
  e      <- newIORef =<< readIORef (svExplanation solver)
  v      <- newIORef =<< readIORef (svVCnt solver)
  ok     <- newIORef =<< readIORef (svOk solver)
  dir    <- newIORef =<< readIORef (svOptDir solver)
  defs   <- newIORef =<< readIORef (svDefDB solver)
  logger <- newIORef =<< readIORef (svLogger solver)
  pivot  <- newIORef =<< readIORef (svPivotStrategy solver)
  npivot <- newIORef =<< readIORef (svNPivot solver)
  bps    <- newIORef =<< mapM cloneBacktrackPoint =<< readIORef (svBacktrackPoints solver)
  return $
    GenericSolver
    { svTableau = t
    , svLB      = l
    , svUB      = u
    , svModel   = m
    , svExplanation = e
    , svVCnt    = v
    , svOk      = ok
    , svOptDir  = dir
    , svDefDB   = defs
    , svLogger  = logger
    , svNPivot  = npivot
    , svPivotStrategy = pivot
    , svBacktrackPoints = bps
    }  

class (VectorSpace v, Scalar v ~ Rational, Ord v) => SolverValue v where
  toValue :: Rational -> v
  showValue :: Bool -> v -> String
  getModel :: GenericSolver v -> IO Model

instance SolverValue Rational where
  toValue = id
  showValue = showRational
  getModel = getRawModel

instance SolverValue (Delta Rational) where
  toValue = fromReal
  showValue = showDelta
  getModel solver = do
    xs <- variables solver
    ys <- liftM concat $ forM xs $ \x -> do
      Delta p q  <- getValue solver x
      lb <- getLB solver x
      ub <- getUB solver x
      return $
        [(p - c) / (k - q) | Just (Delta c k, _) <- return lb, c < p, k > q] ++
        [(d - p) / (q - h) | Just (Delta d h, _) <- return ub, p < d, q > h]
    let delta0 :: Rational
        delta0 = if null ys then 0.1 else minimum ys
        f :: Delta Rational -> Rational
        f (Delta r k) = r + k * delta0
    liftM (IntMap.map f) $ readIORef (svModel solver)

type ConstrID = Int
type ConstrIDSet = IntSet

type Bound v = Maybe (v, ConstrIDSet)

boundValue :: SolverValue v => Bound v -> Maybe v
boundValue = fmap fst

boundExplanation :: SolverValue v => Bound v -> ConstrIDSet
boundExplanation = maybe mempty snd

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

data BacktrackPoint v
  = BacktrackPoint
  { bpSavedLB :: !(IORef (IntMap (Bound v)))
  , bpSavedUB :: !(IORef (IntMap (Bound v)))
  }

cloneBacktrackPoint :: BacktrackPoint v -> IO (BacktrackPoint v)
cloneBacktrackPoint bp = do
  lbs <- newIORef =<< readIORef (bpSavedLB bp)
  ubs <- newIORef =<< readIORef (bpSavedUB bp)
  return $ BacktrackPoint lbs ubs

pushBacktrackPoint :: GenericSolver v -> IO ()
pushBacktrackPoint solver = do
  savedLBs <- newIORef IntMap.empty
  savedUBs <- newIORef IntMap.empty
  lbs <- readIORef (svLB solver)
  ubs <- readIORef (svUB solver)
  modifyIORef (svBacktrackPoints solver) (BacktrackPoint savedLBs savedUBs :)

popBacktrackPoint :: GenericSolver v -> IO ()
popBacktrackPoint solver = do
  bps <- readIORef (svBacktrackPoints solver)
  case bps of
    [] -> error "popBacktrackPoint: empty backtrack points"
    bp : bps' -> do
      lbs <- readIORef (svLB solver)
      savedLBs <- readIORef (bpSavedLB bp)
      writeIORef (svLB solver) $ IntMap.mergeWithKey (\_ _curr saved -> saved) id (const IntMap.empty) lbs savedLBs

      ubs <- readIORef (svUB solver)
      savedUBs <- readIORef (bpSavedUB bp)
      writeIORef (svUB solver) $ IntMap.mergeWithKey (\_ _curr saved -> saved) id (const IntMap.empty) ubs savedUBs

      writeIORef (svBacktrackPoints solver) bps'
      writeIORef (svOk solver) True

withBacktrackpoint :: GenericSolver v -> (BacktrackPoint v -> IO ()) -> IO ()
withBacktrackpoint solver f = do
  bps <- readIORef (svBacktrackPoints solver)
  case bps of
    [] -> return ()
    bp : _ -> f bp

bpSaveLB :: GenericSolver v -> Var -> IO ()
bpSaveLB solver v = do
  withBacktrackpoint solver $ \bp -> do
    saved <- readIORef (bpSavedLB bp)
    if v `IntMap.member` saved then
      return ()
    else do
      lb <- readIORef (svLB solver)
      let old = IntMap.lookup v lb
      seq old $ writeIORef (bpSavedLB bp) (IntMap.insert v old saved)

bpSaveUB :: GenericSolver v -> Var -> IO ()
bpSaveUB solver v = do
  withBacktrackpoint solver $ \bp -> do
    saved <- readIORef (bpSavedUB bp)
    if v `IntMap.member` saved then
      return ()
    else do
      ub <- readIORef (svUB solver)
      let old = IntMap.lookup v ub
      seq old $ writeIORef (bpSavedUB bp) (IntMap.insert v old saved)

{--------------------------------------------------------------------
  problem description
--------------------------------------------------------------------}

newVar :: SolverValue v => GenericSolver v -> IO Var
newVar solver = do
  v <- readIORef (svVCnt solver)
  writeIORef (svVCnt solver) $! v+1
  modifyIORef (svModel solver) (IntMap.insert v zeroV)
  return v

assertAtom :: Solver -> LA.Atom Rational -> IO ()
assertAtom solver atom = assertAtom' solver atom Nothing

assertAtom' :: Solver -> LA.Atom Rational -> Maybe ConstrID -> IO ()
assertAtom' solver atom cid = do
  (v,op,rhs') <- simplifyAtom solver atom
  case op of
    Le  -> assertUpper' solver v (toValue rhs') cid
    Ge  -> assertLower' solver v (toValue rhs') cid
    Eql -> do
      assertLower' solver v (toValue rhs') cid
      assertUpper' solver v (toValue rhs') cid
    _ -> error "unsupported"
  return ()

assertAtomEx :: GenericSolver (Delta Rational) -> LA.Atom Rational -> IO ()
assertAtomEx solver atom = assertAtomEx' solver atom Nothing

assertAtomEx' :: GenericSolver (Delta Rational) -> LA.Atom Rational -> Maybe ConstrID -> IO ()
assertAtomEx' solver atom cid = do
  (v,op,rhs') <- simplifyAtom solver atom
  case op of
    Le  -> assertUpper' solver v (toValue rhs') cid
    Ge  -> assertLower' solver v (toValue rhs') cid
    Lt  -> assertUpper' solver v (toValue rhs' ^-^ delta) cid
    Gt  -> assertLower' solver v (toValue rhs' ^+^ delta) cid
    Eql -> do
      assertLower' solver v (toValue rhs') cid
      assertUpper' solver v (toValue rhs') cid
  return ()

simplifyAtom :: SolverValue v => GenericSolver v -> LA.Atom Rational -> IO (Var, RelOp, Rational)
simplifyAtom solver (OrdRel lhs op rhs) = do
  let (lhs',rhs') =
        case LA.extract LA.unitVar (lhs ^-^ rhs) of
          (n,e) -> (e, -n)
  case LA.terms lhs' of
    [(1,v)] -> return (v, op, rhs')
    [(-1,v)] -> return (v, flipOp op, -rhs')
    _ -> do
      defs <- readIORef (svDefDB solver)
      let (c,lhs'') = scale lhs' -- lhs' = lhs'' / c = rhs'
          rhs'' = c *^ rhs'
          op''  = if c < 0 then flipOp op else op
      case Map.lookup lhs'' defs of
        Just v -> do
          return (v,op'',rhs'')
        Nothing -> do
          v <- newVar solver
          setRow solver v lhs''
          modifyIORef (svDefDB solver) $ Map.insert lhs'' v
          case LA.asConst lhs'' of
            Just 0 -> do
              modifyIORef (svLB solver) (IntMap.insert v (toValue 0, mempty))
              modifyIORef (svUB solver) (IntMap.insert v (toValue 0, mempty))
            _ -> return ()
          return (v,op'',rhs'')
  where
    scale :: LA.Expr Rational -> (Rational, LA.Expr Rational)
    scale e = (c, c *^ e)
      where
        c = c1 * c2
        c1 = fromIntegral $ foldl' lcm 1 [denominator c | (c, _) <- LA.terms e]
        c2 = signum $ head ([c | (c,x) <- LA.terms e] ++ [1])
             
assertLower :: SolverValue v => GenericSolver v -> Var -> v -> IO ()
assertLower solver x l = assertLower' solver x l Nothing

assertLower' :: SolverValue v => GenericSolver v -> Var -> v -> Maybe ConstrID -> IO ()
assertLower' solver x l cid = do
  let cidSet = IntSet.fromList $ maybeToList cid
  l0 <- getLB solver x
  u0 <- getUB solver x
  case (l0,u0) of 
    (Just (l0', _), _) | l <= l0' -> return ()
    (_, Just (u0', cidSet2)) | u0' < l -> do
      writeIORef (svExplanation solver) $ cidSet `IntSet.union` cidSet2
      markBad solver
    _ -> do
      bpSaveLB solver x
      modifyIORef (svLB solver) (IntMap.insert x (l, cidSet))
      b <- isNonBasicVariable solver x
      v <- getValue solver x
      when (b && not (l <= v)) $ update solver x l
      checkNBFeasibility solver

assertUpper :: SolverValue v => GenericSolver v -> Var -> v -> IO ()
assertUpper solver x u = assertUpper' solver x u Nothing 

assertUpper' :: SolverValue v => GenericSolver v -> Var -> v -> Maybe ConstrID -> IO ()
assertUpper' solver x u cid = do
  let cidSet = IntSet.fromList $ maybeToList cid
  l0 <- getLB solver x
  u0 <- getUB solver x
  case (l0,u0) of
    (_, Just (u0', _)) | u0' <= u -> return ()
    (Just (l0', cidSet2), _) | u < l0' -> do
      writeIORef (svExplanation solver) $ cidSet `IntSet.union` cidSet2
      markBad solver
    _ -> do
      bpSaveUB solver x
      modifyIORef (svUB solver) (IntMap.insert x (u, cidSet))
      b <- isNonBasicVariable solver x
      v <- getValue solver x
      when (b && not (v <= u)) $ update solver x u
      checkNBFeasibility solver

-- FIXME: 式に定数項が含まれる可能性を考えるとこれじゃまずい?
setObj :: SolverValue v => GenericSolver v -> LA.Expr Rational -> IO ()
setObj solver e = setRow solver objVar e

getObj :: SolverValue v => GenericSolver v -> IO (LA.Expr Rational)
getObj solver = getRow solver objVar

setRow :: SolverValue v => GenericSolver v -> Var -> LA.Expr Rational -> IO ()
setRow solver v e = do
  modifyIORef (svTableau solver) $ \t ->
    IntMap.insert v (LA.applySubst t e) t
  modifyIORef (svModel solver) $ \m -> 
    IntMap.insert v (LA.evalLinear m (toValue 1) e) m  

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
  return $ v `IntMap.member` t

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
      m <- selectViolatingBasicVariable solver

      case m of
        Nothing -> return True
        Just xi  -> do
          li <- getLB solver xi
          ui <- getUB solver xi
          isLBViolated <- do
            vi <- getValue solver xi
            return $ not (testLB li vi)
          let q = if isLBViolated
                  then -- select the smallest non-basic variable xj such that
                       -- (aij > 0 and β(xj) < uj) or (aij < 0 and β(xj) > lj)
                       canIncrease solver
                  else -- select the smallest non-basic variable xj such that
                       -- (aij < 0 and β(xj) < uj) or (aij > 0 and β(xj) > lj)
                       canDecrease solver
          xi_def <- getRow solver xi
          r <- liftM (fmap snd) $ findM q (LA.terms xi_def)              
          case r of
            Nothing -> do
              let c = if isLBViolated then li else ui
              core <- liftM (mconcat . map boundExplanation . (c :)) $ forM (LA.terms xi_def) $ \(aij, xj) -> do
                if isLBViolated then do
                  if aij > 0 then do
                    getUB solver xj
                  else do
                    getLB solver xj
                else do
                  if aij > 0 then do
                    getLB solver xj
                  else do
                    getUB solver xj
              writeIORef (svExplanation solver) core
              markBad solver
              return False
            Just xj -> do
              pivotAndUpdate solver xi xj (fromJust $ boundValue $ if isLBViolated then li else ui)
              loop

  ok <- readIORef (svOk solver)
  if not ok
  then return False
  else do
    log solver "check"
    result <- recordTime solver loop
    when result $ checkFeasibility solver
    return result

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
                then return (xi, fromJust (boundValue li) ^-^ vi)
                else return (xi, vi ^-^ fromJust (boundValue ui))
          return $ Just $ fst $ maximumBy (comparing snd) xs2

{--------------------------------------------------------------------
  Optimization
--------------------------------------------------------------------}

-- | results of optimization
data OptResult = Optimum | Unsat | Unbounded | ObjLimit
  deriving (Show, Eq, Ord)

-- | Options for solving.
--
-- The default option can be obtained by 'def'.
data Options
  = Options
  { objLimit :: Maybe Rational
  }
  deriving (Show, Eq, Ord)

instance Default Options where
  def =
    Options
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
         dir <- getOptDir solver
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
      dir <- getOptDir solver
      if dir==OptMin
       then canDecrease solver (c,xj)
       else canIncrease solver (c,xj)

canIncrease :: SolverValue v => GenericSolver v -> (Rational,Var) -> IO Bool
canIncrease solver (a,x) =
  case compare a 0 of
    EQ -> return False
    GT -> canIncrease1 solver x
    LT -> canDecrease1 solver x

canDecrease :: SolverValue v => GenericSolver v -> (Rational,Var) -> IO Bool
canDecrease solver (a,x) =
  case compare a 0 of
    EQ -> return False
    GT -> canDecrease1 solver x
    LT -> canIncrease1 solver x

canIncrease1 :: SolverValue v => GenericSolver v -> Var -> IO Bool
canIncrease1 solver x = do
  u <- getUB solver x
  v <- getValue solver x
  case u of
    Nothing -> return True
    Just (uv, _) -> return $! (v < uv)

canDecrease1 :: SolverValue v => GenericSolver v -> Var -> IO Bool
canDecrease1 solver x = do
  l <- getLB solver x
  v <- getValue solver x
  case l of
    Nothing -> return True
    Just (lv, _) -> return $! (lv < v)

-- | feasibility を保ちつつ non-basic variable xj の値を大きくする
increaseNB :: Solver -> Var -> IO Bool
increaseNB solver xj = do
  col <- getCol solver xj

  -- Upper bounds of θ
  -- NOTE: xj 自体の上限も考慮するのに注意
  ubs <- liftM concat $ forM ((xj,1) : IntMap.toList col) $ \(xi,aij) -> do
    v1 <- getValue solver xi
    li <- getLB solver xi
    ui <- getUB solver xi
    return [ assert (theta >= zeroV) ((xi,v2), theta)
           | Just v2 <- [boundValue ui | aij > 0] ++ [boundValue li | aij < 0]
           , let theta = (v2 ^-^ v1) ^/ aij ]

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
  lbs <- liftM concat $ forM ((xj,1) : IntMap.toList col) $ \(xi,aij) -> do
    v1 <- getValue solver xi
    li <- getLB solver xi
    ui <- getUB solver xi
    return [ assert (theta <= zeroV) ((xi,v2), theta)
           | Just v2 <- [boundValue li | aij > 0] ++ [boundValue ui | aij < 0]
           , let theta = (v2 ^-^ v1) ^/ aij ]

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
          m <- selectViolatingBasicVariable solver
          case m of
            Nothing -> return Optimum
            Just xi  -> do
              xi_def  <- getRow solver xi
              li <- getLB solver xi
              ui <- getUB solver xi
              isLBViolated <- do
                vi <- getValue solver xi
                return $ not (testLB li vi)
              r <- dualRTest solver xi_def isLBViolated
              case r of
                Nothing -> do
                  -- dual unbounded
                  let c = if isLBViolated then li else ui
                  core <- liftM (mconcat . map boundExplanation . (c :)) $ forM (LA.terms xi_def) $ \(aij, xj) -> do
                    if isLBViolated then do
                      if aij > 0 then do
                        getUB solver xj
                      else do
                        getLB solver xj
                    else do
                      if aij > 0 then do
                        getLB solver xj
                      else do
                        getUB solver xj
                  writeIORef (svExplanation solver) core
                  markBad solver
                  return Unsat
                Just xj -> do
                  pivotAndUpdate solver xi xj (fromJust $ boundValue $ if isLBViolated then li else ui)
                  loop

  ok <- readIORef (svOk solver)
  if not ok
  then return Unsat
  else do
    log solver "dual simplex"
    result <- recordTime solver loop
    when (result == Optimum) $ checkFeasibility solver
    return result

dualRTest :: Solver -> LA.Expr Rational -> Bool -> IO (Maybe Var)
dualRTest solver row isLBViolated = do
  -- normalize to the cases of minimization
  obj_def <- do
    def <- getRow solver objVar
    dir <- getOptDir solver
    return $
      case dir of
        OptMin -> def
        OptMax -> negateV def
  -- normalize to the cases of lower bound violation
  let xi_def =
       if isLBViolated
       then row
       else negateV row
  ws <- do
    -- select non-basic variable xj such that
    -- (aij > 0 and β(xj) < uj) or (aij < 0 and β(xj) > lj)
    liftM concat $ forM (LA.terms xi_def) $ \(aij, xj) -> do
      b <- canIncrease solver (aij, xj)
      if b
      then do
        let cj = LA.coeff xj obj_def
        let ratio = cj / aij
        return [(xj, ratio) | ratio >= 0]
      else
        return []
  case ws of
    [] -> return Nothing
    _ -> return $ Just $ fst $ minimumBy (comparing snd) ws

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

type RawModel v = IntMap v

getRawModel :: GenericSolver v -> IO (RawModel v)
getRawModel solver = do
  xs <- variables solver
  liftM IntMap.fromList $ forM xs $ \x -> do
    val <- getValue solver x
    return (x,val)

getObjValue :: GenericSolver v -> IO v
getObjValue solver = getValue solver objVar  

type Model = IntMap Rational

explain :: GenericSolver v -> IO ConstrIDSet
explain solver = readIORef (svExplanation solver)
  
{--------------------------------------------------------------------
  major function
--------------------------------------------------------------------}

update :: SolverValue v => GenericSolver v -> Var -> v -> IO ()
update solver xj v = do
  -- log solver $ printf "before update x%d (%s)" xj (show v)
  -- dump solver

  v0 <- getValue solver xj
  let diff = v ^-^ v0

  aj <- getCol solver xj
  modifyIORef (svModel solver) $ \m ->
    let m2 = IntMap.map (\aij -> aij *^ diff) aj
    in IntMap.insert xj v $ IntMap.unionWith (^+^) m2 m

  -- log solver $ printf "after update x%d (%s)" xj (show v)
  -- dump solver

pivot :: SolverValue v => GenericSolver v -> Var -> Var -> IO ()
pivot solver xi xj = do
  modifyIORef' (svNPivot solver) (+1)
  modifyIORef' (svTableau solver) $ \defs ->
    case LA.solveFor (LA.var xi .==. (defs IntMap.! xi)) xj of
      Just (Eql, xj_def) ->
        IntMap.insert xj xj_def . IntMap.map (LA.applySubst1 xj xj_def) . IntMap.delete xi $ defs
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
  let aij = aj IntMap.! xi
  let theta = (v ^-^ (m IntMap.! xi)) ^/ aij

  let m' = IntMap.fromList $
           [(xi, v), (xj, (m IntMap.! xj) ^+^ theta)] ++
           [(xk, (m IntMap.! xk) ^+^ (akj *^ theta)) | (xk, akj) <- IntMap.toList aj, xk /= xi]
  writeIORef (svModel solver) (IntMap.union m' m) -- note that 'IntMap.union' is left biased.

  pivot solver xi xj

  -- log solver $ printf "after pivotAndUpdate x%d x%d (%s)" xi xj (show v)
  -- dump solver

getLB :: GenericSolver v -> Var -> IO (Bound v)
getLB solver x = do
  lb <- readIORef (svLB solver)
  return $ IntMap.lookup x lb

getUB :: GenericSolver v -> Var -> IO (Bound v)
getUB solver x = do
  ub <- readIORef (svUB solver)
  return $ IntMap.lookup x ub

getTableau :: GenericSolver v -> IO (IntMap (LA.Expr Rational))
getTableau solver = do
  t <- readIORef (svTableau solver)
  return $ IntMap.delete objVar t

getValue :: GenericSolver v -> Var -> IO v
getValue solver x = do
  m <- readIORef (svModel solver)
  return $ m IntMap.! x

getRow :: GenericSolver v -> Var -> IO (LA.Expr Rational)
getRow solver x = do
  -- x should be basic variable or 'objVar'
  t <- readIORef (svTableau solver)
  return $! (t IntMap.! x)

-- aijが非ゼロの列も全部探しているのは効率が悪い
getCol :: SolverValue v => GenericSolver v -> Var -> IO (IntMap Rational)
getCol solver xj = do
  t <- readIORef (svTableau solver)
  return $ IntMap.mapMaybe (LA.lookupCoeff xj) t

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

testLB :: SolverValue v => Bound v -> v -> Bool
testLB Nothing _  = True
testLB (Just (l,_)) x = l <= x

testUB :: SolverValue v => Bound v -> v -> Bool
testUB Nothing _  = True
testUB (Just (u,_)) x = x <= u

variables :: GenericSolver v -> IO [Var]
variables solver = do
  vcnt <- nVars solver
  return [0..vcnt-1]

basicVariables :: GenericSolver v -> IO [Var]
basicVariables solver = do
  t <- readIORef (svTableau solver)
  return (IntMap.keys t)

recordTime :: SolverValue v => GenericSolver v -> IO a -> IO a
recordTime solver act = do
  dumpSize solver
  writeIORef (svNPivot solver) 0

  startCPU <- getTime ProcessCPUTime
  startWC  <- getTime Monotonic

  result <- act

  endCPU <- getTime ProcessCPUTime
  endWC  <- getTime Monotonic

  let durationSecs :: TimeSpec -> TimeSpec -> Double
      durationSecs start end = fromIntegral (timeSpecAsNanoSecs (end `diffTimeSpec` start)) / 10^(9::Int)
  (log solver . printf "cpu time = %.3fs") (durationSecs startCPU endCPU)
  (log solver . printf "wall clock time = %.3fs") (durationSecs startWC endWC)
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

  writeIORef (svTableau solver) (IntMap.fromList [(x1, LA.var x0)])
  writeIORef (svLB solver) $ fmap (\v -> (v, mempty)) $ IntMap.fromList [(x0, 0), (x1, 0)]
  writeIORef (svUB solver) $ fmap (\v -> (v, mempty)) $ IntMap.fromList [(x0, 2), (x1, 3)]
  setObj solver (LA.fromTerms [(-1, x0)])

  ret <- optimize solver def
  print ret
  dump solver

test5 :: IO ()
test5 = do
  solver <- newSolver
  setLogger solver putStrLn
  x0 <- newVar solver
  x1 <- newVar solver

  writeIORef (svTableau solver) (IntMap.fromList [(x1, LA.var x0)])
  writeIORef (svLB solver) $ fmap (\v -> (v, mempty)) $ IntMap.fromList [(x0, 0), (x1, 0)]
  writeIORef (svUB solver) $ fmap (\v -> (v, mempty)) $ IntMap.fromList [(x0, 2), (x1, 0)]
  setObj solver (LA.fromTerms [(-1, x0)])

  checkFeasibility solver

  ret <- optimize solver def
  print ret
  dump solver

test6 :: IO ()
test6 = do
  solver <- newSolver
  setLogger solver putStrLn
  x0 <- newVar solver

  assertAtom solver (LA.constant 1 .<. LA.var x0)
  assertAtom solver (LA.constant 2 .>. LA.var x0)

  ret <- check solver
  print ret
  dump solver

  m <- getModel solver
  print m

dumpSize :: SolverValue v => GenericSolver v -> IO ()
dumpSize solver = do
  t <- readIORef (svTableau solver)
  let nrows = IntMap.size t - 1 -- -1 is objVar
  xs <- variables solver
  let ncols = length xs - nrows
  let nnz = sum [IntMap.size $ LA.coeffMap xi_def | (xi,xi_def) <- IntMap.toList t, xi /= objVar]
  log solver $ printf "%d rows, %d columns, %d non-zeros" nrows ncols nnz

dump :: SolverValue v => GenericSolver v -> IO ()
dump solver = do
  log solver "============="

  log solver "Tableau:"
  t <- readIORef (svTableau solver)
  log solver $ printf "obj = %s" (show (t IntMap.! objVar))
  forM_ (IntMap.toList t) $ \(xi, e) -> do
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
        f (Just (x,_)) = showValue True x
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
        f (Just (x,_)) = showValue True x
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
          f (Just (x,_)) = showValue True x
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
