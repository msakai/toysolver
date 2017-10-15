{-# LANGUAGE ScopedTypeVariables, Rank2Types, TypeOperators, TypeSynonymInstances, FlexibleInstances, TypeFamilies, CPP #-}
{-# LANGUAGE BangPatterns #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.Arith.Simplex
-- Copyright   :  (c) Masahiro Sakai 2012
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  non-portable (ScopedTypeVariables, Rank2Types, TypeOperators, TypeSynonymInstances, FlexibleInstances, TypeFamilies, CPP)
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
module ToySolver.Arith.Simplex
  (
  -- * The @Solver@ type
    Solver
  , GenericSolver
  , GenericSolverM
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
  , enableTimeRecording
  , disableTimeRecording
  , Config (..)
  , setConfig
  , getConfig
  , modifyConfig
  , PivotStrategy (..)
  , showPivotStrategy
  , parsePivotStrategy
  , setPivotStrategy

  -- * Debug
  , dump

  -- * Misc
  , simplifyAtom
  ) where

import Prelude hiding (log)
import Control.Arrow ((***))
import Control.Exception
import Control.Monad
import Control.Monad.Primitive
import Data.Char
import Data.Default.Class
import Data.Ord
import Data.List
import Data.Maybe
import Data.Monoid
import Data.Primitive.MutVar
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

infixr 0 ~>
-- | A natural transformation from @f@ to @g@.
type f ~> g = forall x. f x -> g x

infixr 0 :~>, $$
-- | A natural transformation suitable for storing in a container.
newtype f :~> g = Nat { ($$) :: f ~> g }

{--------------------------------------------------------------------
  The @Solver@ type
--------------------------------------------------------------------}

type Var = Int

data GenericSolverM m v
  = GenericSolverM
  { svTableau :: !(MutVar (PrimState m) (IntMap (LA.Expr Rational)))
  , svLB      :: !(MutVar (PrimState m) (IntMap (v, ConstrIDSet)))
  , svUB      :: !(MutVar (PrimState m) (IntMap (v, ConstrIDSet)))
  , svModel   :: !(MutVar (PrimState m) (IntMap v))
  , svExplanation :: !(MutVar (PrimState m) (Maybe ConstrIDSet))
  , svVCnt    :: !(MutVar (PrimState m) Int)
  , svOptDir  :: !(MutVar (PrimState m) OptDir)

  , svDefDB  :: !(MutVar (PrimState m) (Map (LA.Expr Rational) Var))

  , svLogger :: !(MutVar (PrimState m) (Maybe (String -> m ())))
  , svRecTime :: !(MutVar (PrimState m) (Maybe (GenericSolverM m v -> (m :~> m))))
  , svConfig  :: !(MutVar (PrimState m) Config)
  , svNPivot  :: !(MutVar (PrimState m) Int)

  , svBacktrackPoints :: !(MutVar (PrimState m) [BacktrackPoint m v])
  }

type GenericSolver v = GenericSolverM IO v

type Solver = GenericSolver Rational

-- special basic variable
objVar :: Int
objVar = -1

newSolver :: (PrimMonad m, SolverValue v) => m (GenericSolverM m v)
newSolver = do
  t <- newMutVar (IntMap.singleton objVar zeroV)
  l <- newMutVar IntMap.empty
  u <- newMutVar IntMap.empty
  m <- newMutVar (IntMap.singleton objVar zeroV)
  e <- newMutVar mempty
  v <- newMutVar 0
  dir <- newMutVar OptMin
  defs <- newMutVar Map.empty
  logger <- newMutVar Nothing
  rectm <- newMutVar Nothing
  config <- newMutVar def
  npivot <- newMutVar 0
  bps <- newMutVar []
  return $
    GenericSolverM
    { svTableau = t
    , svLB      = l
    , svUB      = u
    , svModel   = m
    , svExplanation = e
    , svVCnt    = v
    , svOptDir  = dir
    , svDefDB   = defs
    , svLogger  = logger
    , svRecTime = rectm
    , svNPivot  = npivot
    , svConfig  = config
    , svBacktrackPoints = bps
    }

cloneSolver :: PrimMonad m => GenericSolverM m v -> m (GenericSolverM m v)
cloneSolver solver = do
  t      <- newMutVar =<< readMutVar (svTableau solver)
  l      <- newMutVar =<< readMutVar (svLB solver)
  u      <- newMutVar =<< readMutVar (svUB solver)
  m      <- newMutVar =<< readMutVar (svModel solver)
  e      <- newMutVar =<< readMutVar (svExplanation solver)
  v      <- newMutVar =<< readMutVar (svVCnt solver)
  dir    <- newMutVar =<< readMutVar (svOptDir solver)
  defs   <- newMutVar =<< readMutVar (svDefDB solver)
  logger <- newMutVar =<< readMutVar (svLogger solver)
  rectm  <- newMutVar =<< readMutVar (svRecTime solver)
  config <- newMutVar =<< readMutVar (svConfig solver)
  npivot <- newMutVar =<< readMutVar (svNPivot solver)
  bps    <- newMutVar =<< mapM cloneBacktrackPoint =<< readMutVar (svBacktrackPoints solver)
  return $
    GenericSolverM
    { svTableau = t
    , svLB      = l
    , svUB      = u
    , svModel   = m
    , svExplanation = e
    , svVCnt    = v
    , svOptDir  = dir
    , svDefDB   = defs
    , svLogger  = logger
    , svRecTime = rectm
    , svNPivot  = npivot
    , svConfig  = config
    , svBacktrackPoints = bps
    }  

class (VectorSpace v, Scalar v ~ Rational, Ord v) => SolverValue v where
  toValue :: Rational -> v
  showValue :: Bool -> v -> String
  getModel :: PrimMonad m => GenericSolverM m v -> m Model

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
    liftM (IntMap.map f) $ readMutVar (svModel solver)

type ConstrID = Int
type ConstrIDSet = IntSet

type Bound v = Maybe (v, ConstrIDSet)

boundValue :: SolverValue v => Bound v -> Maybe v
boundValue = fmap fst

boundExplanation :: SolverValue v => Bound v -> ConstrIDSet
boundExplanation = maybe mempty snd

addBound :: SolverValue v => Bound v -> Bound v -> Bound v
addBound b1 b2 = do
  (a1,cs1) <- b1
  (a2,cs2) <- b2
  let a3 = a1 ^+^ a2
      cs3 = IntSet.union cs1 cs2
  seq a3 $ seq cs3 $ return (a3,cs3)

scaleBound :: SolverValue v => Scalar v -> Bound v -> Bound v
scaleBound c = fmap ((c *^) *** id)

data Config
  = Config
  { configPivotStrategy :: !PivotStrategy
  , configEnableBoundTightening :: !Bool
  } deriving (Show, Eq, Ord)

instance Default Config where
  def =
    Config
    { configPivotStrategy = PivotStrategyBlandRule
    , configEnableBoundTightening = False
    }

setConfig :: PrimMonad m => GenericSolverM m v -> Config -> m ()
setConfig solver config = writeMutVar (svConfig solver) config

getConfig :: PrimMonad m => GenericSolverM m v -> m Config
getConfig solver = readMutVar (svConfig solver)

modifyConfig :: PrimMonad m => GenericSolverM m v -> (Config -> Config) -> m ()
modifyConfig solver = modifyMutVar' (svConfig solver)

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
  deriving (Eq, Ord, Enum, Bounded, Show, Read)

showPivotStrategy :: PivotStrategy -> String
showPivotStrategy PivotStrategyBlandRule = "bland-rule"
showPivotStrategy PivotStrategyLargestCoefficient = "largest-coefficient"

parsePivotStrategy :: String -> Maybe PivotStrategy
parsePivotStrategy s =
  case map toLower s of
    "bland-rule" -> Just PivotStrategyBlandRule
    "largest-coefficient" -> Just PivotStrategyLargestCoefficient
    _ -> Nothing

{-# DEPRECATED nVars "Use setConfig instead" #-}
setPivotStrategy :: PrimMonad m => GenericSolverM m v -> PivotStrategy -> m ()
setPivotStrategy solver ps = modifyConfig solver $ \config ->
  config{ configPivotStrategy = ps }

{--------------------------------------------------------------------
  problem description
--------------------------------------------------------------------}

data BacktrackPoint m v
  = BacktrackPoint
  { bpSavedLB :: !(MutVar (PrimState m) (IntMap (Bound v)))
  , bpSavedUB :: !(MutVar (PrimState m) (IntMap (Bound v)))
  }

cloneBacktrackPoint :: PrimMonad m => BacktrackPoint m v -> m (BacktrackPoint m v)
cloneBacktrackPoint bp = do
  lbs <- newMutVar =<< readMutVar (bpSavedLB bp)
  ubs <- newMutVar =<< readMutVar (bpSavedUB bp)
  return $ BacktrackPoint lbs ubs

pushBacktrackPoint :: PrimMonad m => GenericSolverM m v -> m ()
pushBacktrackPoint solver = do
  savedLBs <- newMutVar IntMap.empty
  savedUBs <- newMutVar IntMap.empty
  lbs <- readMutVar (svLB solver)
  ubs <- readMutVar (svUB solver)
  modifyMutVar (svBacktrackPoints solver) (BacktrackPoint savedLBs savedUBs :)

popBacktrackPoint :: PrimMonad m => GenericSolverM m v -> m ()
popBacktrackPoint solver = do
  bps <- readMutVar (svBacktrackPoints solver)
  case bps of
    [] -> error "popBacktrackPoint: empty backtrack points"
    bp : bps' -> do
      lbs <- readMutVar (svLB solver)
      savedLBs <- readMutVar (bpSavedLB bp)
      writeMutVar (svLB solver) $ IntMap.mergeWithKey (\_ _curr saved -> saved) id (const IntMap.empty) lbs savedLBs

      ubs <- readMutVar (svUB solver)
      savedUBs <- readMutVar (bpSavedUB bp)
      writeMutVar (svUB solver) $ IntMap.mergeWithKey (\_ _curr saved -> saved) id (const IntMap.empty) ubs savedUBs

      writeMutVar (svBacktrackPoints solver) bps'
      writeMutVar (svExplanation solver) Nothing

withBacktrackpoint :: PrimMonad m => GenericSolverM m v -> (BacktrackPoint m v -> m ()) -> m ()
withBacktrackpoint solver f = do
  bps <- readMutVar (svBacktrackPoints solver)
  case bps of
    [] -> return ()
    bp : _ -> f bp

bpSaveLB :: PrimMonad m => GenericSolverM m v -> Var -> m ()
bpSaveLB solver v = do
  withBacktrackpoint solver $ \bp -> do
    saved <- readMutVar (bpSavedLB bp)
    if v `IntMap.member` saved then
      return ()
    else do
      lb <- readMutVar (svLB solver)
      let old = IntMap.lookup v lb
      seq old $ writeMutVar (bpSavedLB bp) (IntMap.insert v old saved)

bpSaveUB :: PrimMonad m => GenericSolverM m v -> Var -> m ()
bpSaveUB solver v = do
  withBacktrackpoint solver $ \bp -> do
    saved <- readMutVar (bpSavedUB bp)
    if v `IntMap.member` saved then
      return ()
    else do
      ub <- readMutVar (svUB solver)
      let old = IntMap.lookup v ub
      seq old $ writeMutVar (bpSavedUB bp) (IntMap.insert v old saved)

{--------------------------------------------------------------------
  problem description
--------------------------------------------------------------------}

newVar :: (PrimMonad m, SolverValue v) => GenericSolverM m v -> m Var
newVar solver = do
  v <- readMutVar (svVCnt solver)
  writeMutVar (svVCnt solver) $! v+1
  modifyMutVar (svModel solver) (IntMap.insert v zeroV)
  return v

assertAtom :: PrimMonad m => GenericSolverM m Rational -> LA.Atom Rational -> m ()
assertAtom solver atom = assertAtom' solver atom Nothing

assertAtom' :: PrimMonad m => GenericSolverM m Rational -> LA.Atom Rational -> Maybe ConstrID -> m ()
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

assertAtomEx :: PrimMonad m => GenericSolverM m (Delta Rational) -> LA.Atom Rational -> m ()
assertAtomEx solver atom = assertAtomEx' solver atom Nothing

assertAtomEx' :: PrimMonad m => GenericSolverM m (Delta Rational) -> LA.Atom Rational -> Maybe ConstrID -> m ()
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

simplifyAtom :: (PrimMonad m, SolverValue v) => GenericSolverM m v -> LA.Atom Rational -> m (Var, RelOp, Rational)
simplifyAtom solver (OrdRel lhs op rhs) = do
  let (lhs',rhs') =
        case LA.extract LA.unitVar (lhs ^-^ rhs) of
          (n,e) -> (e, -n)
  case LA.terms lhs' of
    [(1,v)] -> return (v, op, rhs')
    [(-1,v)] -> return (v, flipOp op, -rhs')
    _ -> do
      defs <- readMutVar (svDefDB solver)
      let (c,lhs'') = scale lhs' -- lhs' = lhs'' / c = rhs'
          rhs'' = c *^ rhs'
          op''  = if c < 0 then flipOp op else op
      case Map.lookup lhs'' defs of
        Just v -> do
          return (v,op'',rhs'')
        Nothing -> do
          v <- newVar solver
          setRow solver v lhs''
          modifyMutVar (svDefDB solver) $ Map.insert lhs'' v
          case LA.asConst lhs'' of
            Just 0 -> do
              modifyMutVar (svLB solver) (IntMap.insert v (toValue 0, mempty))
              modifyMutVar (svUB solver) (IntMap.insert v (toValue 0, mempty))
            _ -> return ()
          return (v,op'',rhs'')
  where
    scale :: LA.Expr Rational -> (Rational, LA.Expr Rational)
    scale e = (c, c *^ e)
      where
        c = c1 * c2
        c1 = fromIntegral $ foldl' lcm 1 [denominator c | (c, _) <- LA.terms e]
        c2 = signum $ head ([c | (c,x) <- LA.terms e] ++ [1])
             
assertLower :: (PrimMonad m, SolverValue v) => GenericSolverM m v -> Var -> v -> m ()
assertLower solver x l = assertLB solver x (Just (l, IntSet.empty))

assertLower' :: (PrimMonad m, SolverValue v) => GenericSolverM m v -> Var -> v -> Maybe ConstrID -> m ()
assertLower' solver x l cid = assertLB solver x (Just (l, IntSet.fromList (maybeToList cid)))

assertLB :: (PrimMonad m, SolverValue v) => GenericSolverM m v -> Var -> Bound v -> m ()
assertLB solver x Nothing = return ()
assertLB solver x (Just (l, cidSet)) = do
  l0 <- getLB solver x
  u0 <- getUB solver x
  case (l0,u0) of 
    (Just (l0', _), _) | l <= l0' -> return ()
    (_, Just (u0', cidSet2)) | u0' < l -> do
      setExplanation solver $ cidSet `IntSet.union` cidSet2
    _ -> do
      bpSaveLB solver x
      modifyMutVar (svLB solver) (IntMap.insert x (l, cidSet))
      b <- isNonBasicVariable solver x
      v <- getValue solver x
      when (b && not (l <= v)) $ update solver x l
      checkNBFeasibility solver

assertUpper :: (PrimMonad m, SolverValue v) => GenericSolverM m v -> Var -> v -> m ()
assertUpper solver x u = assertUB solver x (Just (u, IntSet.empty))

assertUpper' :: (PrimMonad m, SolverValue v) => GenericSolverM m v -> Var -> v -> Maybe ConstrID -> m ()
assertUpper' solver x u cid = assertUB solver x (Just (u, IntSet.fromList (maybeToList cid)))

assertUB :: (PrimMonad m, SolverValue v) => GenericSolverM m v -> Var -> Bound v -> m ()
assertUB solver x Nothing = return ()
assertUB solver x (Just (u, cidSet)) = do
  l0 <- getLB solver x
  u0 <- getUB solver x
  case (l0,u0) of
    (_, Just (u0', _)) | u0' <= u -> return ()
    (Just (l0', cidSet2), _) | u < l0' -> do
      setExplanation solver $ cidSet `IntSet.union` cidSet2
    _ -> do
      bpSaveUB solver x
      modifyMutVar (svUB solver) (IntMap.insert x (u, cidSet))
      b <- isNonBasicVariable solver x
      v <- getValue solver x
      when (b && not (v <= u)) $ update solver x u
      checkNBFeasibility solver

-- FIXME: 式に定数項が含まれる可能性を考えるとこれじゃまずい?
setObj :: (PrimMonad m, SolverValue v) => GenericSolverM m v -> LA.Expr Rational -> m ()
setObj solver e = setRow solver objVar e

getObj :: (PrimMonad m, SolverValue v) => GenericSolverM m v -> m (LA.Expr Rational)
getObj solver = getRow solver objVar

setRow :: (PrimMonad m, SolverValue v) => GenericSolverM m v -> Var -> LA.Expr Rational -> m ()
setRow solver v e = do
  modifyMutVar (svTableau solver) $ \t ->
    IntMap.insert v (LA.applySubst t e) t
  modifyMutVar (svModel solver) $ \m -> 
    IntMap.insert v (LA.evalLinear m (toValue 1) e) m  

setOptDir :: PrimMonad m => GenericSolverM m v -> OptDir -> m ()
setOptDir solver dir = writeMutVar (svOptDir solver) dir

getOptDir :: PrimMonad m => GenericSolverM m v -> m OptDir
getOptDir solver = readMutVar (svOptDir solver)

{--------------------------------------------------------------------
  Status
--------------------------------------------------------------------}

nVars :: PrimMonad m => GenericSolverM m v -> m Int
nVars solver = readMutVar (svVCnt solver)

isBasicVariable :: PrimMonad m => GenericSolverM m v -> Var -> m Bool
isBasicVariable solver v = do
  t <- readMutVar (svTableau solver)
  return $ v `IntMap.member` t

isNonBasicVariable  :: PrimMonad m => GenericSolverM m v -> Var -> m Bool
isNonBasicVariable solver x = liftM not (isBasicVariable solver x)

isFeasible :: (PrimMonad m, SolverValue v) => GenericSolverM m v -> m Bool
isFeasible solver = do
  xs <- variables solver
  liftM and $ forM xs $ \x -> do
    v <- getValue solver x
    l <- getLB solver x
    u <- getUB solver x
    return (testLB l v && testUB u v)

isOptimal :: (PrimMonad m, SolverValue v) => GenericSolverM m v -> m Bool
isOptimal solver = do
  obj <- getRow solver objVar
  ret <- selectEnteringVariable solver
  return $! isNothing ret

{--------------------------------------------------------------------
  Satisfiability solving
--------------------------------------------------------------------}

check :: forall m v. (PrimMonad m, SolverValue v) => GenericSolverM m v -> m Bool
check solver = do
  let
    loop :: m Bool
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
              setExplanation solver core
              return False
            Just xj -> do
              pivotAndUpdate solver xi xj (fromJust $ boundValue $ if isLBViolated then li else ui)
              m <- readMutVar (svExplanation solver)
              if isJust m then
                return False
              else
                loop

  m <- readMutVar (svExplanation solver)
  case m of
    Just _ -> return False
    Nothing -> do
      log solver "check"
      result <- recordTime solver loop
      when result $ checkFeasibility solver
      return result

selectViolatingBasicVariable :: forall m v. (PrimMonad m, SolverValue v) => GenericSolverM m v -> m (Maybe Var)
selectViolatingBasicVariable solver = do
  let
    p :: Var -> m Bool
    p x | x == objVar = return False
    p xi = do
      li <- getLB solver xi
      ui <- getUB solver xi
      vi <- getValue solver xi
      return $ not (testLB li vi) || not (testUB ui vi)
  vs <- basicVariables solver

  config <- getConfig solver
  case configPivotStrategy config of
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

tightenBounds :: (PrimMonad m, SolverValue v) => GenericSolverM m v -> Var -> m ()
tightenBounds solver x = do
  -- x must be basic variable
  defs <- readMutVar (svTableau solver)
  let x_def = defs IntMap.! x
      f (!lb,!ub) (c,xk) = do
        if LA.unitVar == xk then do
          return (addBound lb (Just (toValue c, IntSet.empty)), addBound ub (Just (toValue c, IntSet.empty)))
        else do
          lb_k <- getLB solver xk
          ub_k <- getUB solver xk
          if c > 0 then do
            return (addBound lb (scaleBound c lb_k), addBound ub (scaleBound c ub_k))
          else do
            return (addBound lb (scaleBound c ub_k), addBound ub (scaleBound c lb_k))
  (lb,ub) <- foldM f (Just (zeroV, IntSet.empty), Just (zeroV, IntSet.empty)) (LA.terms x_def)
  assertLB solver x lb
  assertUB solver x ub

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

optimize :: forall m. PrimMonad m => GenericSolverM m Rational -> Options -> m OptResult
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
    loop :: m OptResult
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

selectEnteringVariable :: forall m v. (PrimMonad m, SolverValue v) => GenericSolverM m v -> m (Maybe (Rational, Var))
selectEnteringVariable solver = do
  config <- getConfig solver
  obj_def <- getRow solver objVar
  case configPivotStrategy config of
    PivotStrategyBlandRule ->
      findM canEnter (LA.terms obj_def)
    PivotStrategyLargestCoefficient -> do
      ts <- filterM canEnter (LA.terms obj_def)
      case ts of
        [] -> return Nothing
        _ -> return $ Just $ snd $ maximumBy (comparing fst) [(abs c, (c,xj)) | (c,xj) <- ts]
  where
    canEnter :: (Rational, Var) -> m Bool
    canEnter (_,xj) | xj == LA.unitVar = return False
    canEnter (c,xj) = do
      dir <- getOptDir solver
      if dir==OptMin
       then canDecrease solver (c,xj)
       else canIncrease solver (c,xj)

canIncrease :: (PrimMonad m, SolverValue v) => GenericSolverM m v -> (Rational,Var) -> m Bool
canIncrease solver (a,x) =
  case compare a 0 of
    EQ -> return False
    GT -> canIncrease1 solver x
    LT -> canDecrease1 solver x

canDecrease :: (PrimMonad m, SolverValue v) => GenericSolverM m v -> (Rational,Var) -> m Bool
canDecrease solver (a,x) =
  case compare a 0 of
    EQ -> return False
    GT -> canDecrease1 solver x
    LT -> canIncrease1 solver x

canIncrease1 :: (PrimMonad m, SolverValue v) => GenericSolverM m v -> Var -> m Bool
canIncrease1 solver x = do
  u <- getUB solver x
  v <- getValue solver x
  case u of
    Nothing -> return True
    Just (uv, _) -> return $! (v < uv)

canDecrease1 :: (PrimMonad m, SolverValue v) => GenericSolverM m v -> Var -> m Bool
canDecrease1 solver x = do
  l <- getLB solver x
  v <- getValue solver x
  case l of
    Nothing -> return True
    Just (lv, _) -> return $! (lv < v)

-- | feasibility を保ちつつ non-basic variable xj の値を大きくする
increaseNB :: PrimMonad m => GenericSolverM m Rational -> Var -> m Bool
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
decreaseNB :: PrimMonad m => GenericSolverM m Rational -> Var -> m Bool
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

dualSimplex :: forall m. PrimMonad m => GenericSolverM m Rational -> Options -> m OptResult
dualSimplex solver opt = do
  let
    loop :: m OptResult
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
                  setExplanation solver core
                  return Unsat
                Just xj -> do
                  pivotAndUpdate solver xi xj (fromJust $ boundValue $ if isLBViolated then li else ui)
                  m <- readMutVar (svExplanation solver)
                  if isJust m then
                    return Unsat
                  else
                    loop

  m <- readMutVar (svExplanation solver)
  case m of
    Just _ -> return Unsat
    Nothing -> do
      log solver "dual simplex"
      result <- recordTime solver loop
      when (result == Optimum) $ checkFeasibility solver
      return result

dualRTest :: PrimMonad m => GenericSolverM m Rational -> LA.Expr Rational -> Bool -> m (Maybe Var)
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

prune :: PrimMonad m => GenericSolverM m Rational -> Options -> m Bool
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

getRawModel :: PrimMonad m => GenericSolverM m v -> m (RawModel v)
getRawModel solver = do
  xs <- variables solver
  liftM IntMap.fromList $ forM xs $ \x -> do
    val <- getValue solver x
    return (x,val)

getObjValue :: PrimMonad m => GenericSolverM m v -> m v
getObjValue solver = getValue solver objVar  

type Model = IntMap Rational

explain :: PrimMonad m => GenericSolverM m v -> m ConstrIDSet
explain solver = do
  m <- readMutVar (svExplanation solver)
  case m of
    Nothing -> error "no explanation is available"
    Just cs -> return cs

{--------------------------------------------------------------------
  major function
--------------------------------------------------------------------}

update :: (PrimMonad m, SolverValue v) => GenericSolverM m v -> Var -> v -> m ()
update solver xj v = do
  -- log solver $ printf "before update x%d (%s)" xj (show v)
  -- dump solver

  v0 <- getValue solver xj
  let diff = v ^-^ v0

  aj <- getCol solver xj
  modifyMutVar (svModel solver) $ \m ->
    let m2 = IntMap.map (\aij -> aij *^ diff) aj
    in IntMap.insert xj v $ IntMap.unionWith (^+^) m2 m

  -- log solver $ printf "after update x%d (%s)" xj (show v)
  -- dump solver

pivot :: (PrimMonad m, SolverValue v) => GenericSolverM m v -> Var -> Var -> m ()
pivot solver xi xj = do
  modifyMutVar' (svNPivot solver) (+1)
  modifyMutVar' (svTableau solver) $ \defs ->
    case LA.solveFor (LA.var xi .==. (defs IntMap.! xi)) xj of
      Just (Eql, xj_def) ->
        IntMap.insert xj xj_def . IntMap.map (LA.applySubst1 xj xj_def) . IntMap.delete xi $ defs
      _ -> error "pivot: should not happen"

pivotAndUpdate :: (PrimMonad m, SolverValue v) => GenericSolverM m v -> Var -> Var -> v -> m ()
pivotAndUpdate solver xi xj v | xi == xj = update solver xi v -- xi = xj is non-basic variable
pivotAndUpdate solver xi xj v = do
  -- xi is basic variable
  -- xj is non-basic varaible

  -- log solver $ printf "before pivotAndUpdate x%d x%d (%s)" xi xj (show v)
  -- dump solver

  m <- readMutVar (svModel solver)

  aj <- getCol solver xj
  let aij = aj IntMap.! xi
  let theta = (v ^-^ (m IntMap.! xi)) ^/ aij

  let m' = IntMap.fromList $
           [(xi, v), (xj, (m IntMap.! xj) ^+^ theta)] ++
           [(xk, (m IntMap.! xk) ^+^ (akj *^ theta)) | (xk, akj) <- IntMap.toList aj, xk /= xi]
  writeMutVar (svModel solver) (IntMap.union m' m) -- note that 'IntMap.union' is left biased.

  pivot solver xi xj

  config <- getConfig solver
  when (configEnableBoundTightening config) $ do
    tightenBounds solver xj

  -- log solver $ printf "after pivotAndUpdate x%d x%d (%s)" xi xj (show v)
  -- dump solver

getLB :: PrimMonad m => GenericSolverM m v -> Var -> m (Bound v)
getLB solver x = do
  lb <- readMutVar (svLB solver)
  return $ IntMap.lookup x lb

getUB :: PrimMonad m => GenericSolverM m v -> Var -> m (Bound v)
getUB solver x = do
  ub <- readMutVar (svUB solver)
  return $ IntMap.lookup x ub

getTableau :: PrimMonad m => GenericSolverM m v -> m (IntMap (LA.Expr Rational))
getTableau solver = do
  t <- readMutVar (svTableau solver)
  return $ IntMap.delete objVar t

getValue :: PrimMonad m => GenericSolverM m v -> Var -> m v
getValue solver x = do
  m <- readMutVar (svModel solver)
  return $ m IntMap.! x

getRow :: PrimMonad m => GenericSolverM m v -> Var -> m (LA.Expr Rational)
getRow solver x = do
  -- x should be basic variable or 'objVar'
  t <- readMutVar (svTableau solver)
  return $! (t IntMap.! x)

-- aijが非ゼロの列も全部探しているのは効率が悪い
getCol :: (PrimMonad m, SolverValue v) => GenericSolverM m v -> Var -> m (IntMap Rational)
getCol solver xj = do
  t <- readMutVar (svTableau solver)
  return $ IntMap.mapMaybe (LA.lookupCoeff xj) t

getCoeff :: PrimMonad m => GenericSolverM m v -> Var -> Var -> m Rational
getCoeff solver xi xj = do
  xi_def <- getRow solver xi
  return $! LA.coeff xj xi_def

setExplanation :: PrimMonad m => GenericSolverM m v -> ConstrIDSet -> m ()
setExplanation solver !cs = do
  m <- readMutVar (svExplanation solver)
  case m of
    Just _ -> return ()
    Nothing -> writeMutVar (svExplanation solver) (Just cs)

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

variables :: PrimMonad m => GenericSolverM m v -> m [Var]
variables solver = do
  vcnt <- nVars solver
  return [0..vcnt-1]

basicVariables :: PrimMonad m => GenericSolverM m v -> m [Var]
basicVariables solver = do
  t <- readMutVar (svTableau solver)
  return (IntMap.keys t)

recordTime :: (PrimMonad m, SolverValue v) => GenericSolverM m v -> m a -> m a
recordTime solver act = do
  dumpSize solver
  writeMutVar (svNPivot solver) 0
  rectm <- readMutVar (svRecTime solver)
  result <-
    case rectm of
      Nothing -> act
      Just f -> f solver $$ act
  (log solver . printf "#pivot = %d") =<< readMutVar (svNPivot solver)
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
setLogger :: PrimMonad m => GenericSolverM m v -> (String -> m ()) -> m ()
setLogger solver logger = do
  writeMutVar (svLogger solver) (Just logger)

clearLogger :: PrimMonad m => GenericSolverM m v -> m ()
clearLogger solver = writeMutVar (svLogger solver) Nothing

log :: PrimMonad m => GenericSolverM m v -> String -> m ()
log solver msg = logM solver (return msg)

logM :: PrimMonad m => GenericSolverM m v -> m String -> m ()
logM solver action = do
  m <- readMutVar (svLogger solver)
  case m of
    Nothing -> return ()
    Just logger -> action >>= logger

enableTimeRecording :: GenericSolverM IO v -> IO ()
enableTimeRecording solver = do
  writeMutVar (svRecTime solver) (Just f)
  where
    f solver = Nat $ \act -> do
        startCPU <- getTime ProcessCPUTime
        startWC  <- getTime Monotonic
        result <- act
        endCPU <- getTime ProcessCPUTime
        endWC  <- getTime Monotonic
        let durationSecs :: TimeSpec -> TimeSpec -> Double
            durationSecs start end = fromIntegral (toNanoSecs (end `diffTimeSpec` start)) / 10^(9::Int)      
        (log solver . printf "cpu time = %.3fs") (durationSecs startCPU endCPU)
        (log solver . printf "wall clock time = %.3fs") (durationSecs startWC endWC)
        return result

disableTimeRecording :: PrimMonad m => GenericSolverM m v -> m ()
disableTimeRecording solver = writeMutVar (svRecTime solver) Nothing

{--------------------------------------------------------------------
  debug and tests
--------------------------------------------------------------------}

test4 :: IO ()
test4 = do
  solver <- newSolver
  setLogger solver putStrLn
  x0 <- newVar solver
  x1 <- newVar solver

  writeMutVar (svTableau solver) (IntMap.fromList [(x1, LA.var x0)])
  writeMutVar (svLB solver) $ fmap (\v -> (v, mempty)) $ IntMap.fromList [(x0, 0), (x1, 0)]
  writeMutVar (svUB solver) $ fmap (\v -> (v, mempty)) $ IntMap.fromList [(x0, 2), (x1, 3)]
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

  writeMutVar (svTableau solver) (IntMap.fromList [(x1, LA.var x0)])
  writeMutVar (svLB solver) $ fmap (\v -> (v, mempty)) $ IntMap.fromList [(x0, 0), (x1, 0)]
  writeMutVar (svUB solver) $ fmap (\v -> (v, mempty)) $ IntMap.fromList [(x0, 2), (x1, 0)]
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

dumpSize :: forall m v. PrimMonad m => SolverValue v => GenericSolverM m v -> m ()
dumpSize solver = do
  t <- readMutVar (svTableau solver)
  let nrows = IntMap.size t - 1 -- -1 is objVar
  xs <- variables solver
  let ncols = length xs - nrows
  let nnz = sum [IntMap.size $ LA.coeffMap xi_def | (xi,xi_def) <- IntMap.toList t, xi /= objVar]
  log solver $ printf "%d rows, %d columns, %d non-zeros" nrows ncols nnz

dump :: PrimMonad m => SolverValue v => GenericSolverM m v -> m ()
dump solver = do
  log solver "============="

  log solver "Tableau:"
  t <- readMutVar (svTableau solver)
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

checkFeasibility :: (PrimMonad m, SolverValue v) => GenericSolverM m v -> m ()
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

checkNBFeasibility :: (PrimMonad m, SolverValue v) => GenericSolverM m v -> m ()
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

checkOptimality :: (PrimMonad m, SolverValue v) => GenericSolverM m v -> m ()
checkOptimality _ | True = return ()
checkOptimality solver = do
  ret <- selectEnteringVariable solver
  case ret of
    Nothing -> return () -- optimal
    Just (_,x) -> error (printf "checkOptimality: not optimal (x%d can be changed)" x)
