-----------------------------------------------------------------------------
-- |
-- Module      :  MIPSolver2
-- Copyright   :  (c) Masahiro Sakai 2012
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  non-portable
--
-- Naïve implementation of MIP solver based on Simplex2 module
-- 
-- Reference:
--
-- * <http://www.math.cuhk.edu.hk/~wei/lpch3.pdf>
-- 
-- * R. C. Daniel and Martyn Jeffreys.
--   "Unboundedness in Integer and Discrete Programming L.P. Relaxations"
--   The Journal of the Operational Research Society, Vol. 30, No. 12. (1979)
--   <http://www.jstor.org/stable/3009435>
-- 
-----------------------------------------------------------------------------
module MIPSolver2
  (
  -- * The @Solver@ type
    Solver
  , newSolver

  -- * Solving
  , optimize

  -- * Extract results
  , model
  , getObjValue

  -- * Configulation
  , setLogger
  , setShowRational
  ) where

import Prelude hiding (log)

import Control.Monad
import Control.Exception (assert)
import Data.List
import Data.OptDir
import Data.Ord
import Data.IORef
import Data.Maybe
import Data.Ratio
import qualified Data.IntSet as IS
import qualified Data.IntMap as IM
import qualified SeqQueue as SQ
import Text.Printf

import qualified LA
import Formula (RelOp (..), (.<=.), (.>=.), (.==.))
import qualified Simplex2
import Simplex2 (OptResult (..), Var (..), Model (..))
import qualified OmegaTest
import Linear
import Util (isInteger, fracPart)

data Solver
  = MIP
  { mipRootLP :: Simplex2.Solver
  , mipIVs    :: IS.IntSet
  , mipBest   :: IORef (Maybe Node)

  , mipLogger :: IORef (Maybe (String -> IO ()))
  , mipShowRational :: IORef Bool
  }

data Node =
  Node
  { ndLP    :: Simplex2.Solver
  , ndDepth :: {-# UNPACK #-} !Int
  }

newSolver :: Simplex2.Solver -> IS.IntSet -> IO Solver
newSolver lp ivs = do
  lp2 <- Simplex2.cloneSolver lp

  forM_ (IS.toList ivs) $ \v -> do
    lb <- Simplex2.getLB lp2 v
    case lb of
      Just l | not (isInteger l) ->
        Simplex2.assertLower lp2 v (fromInteger (ceiling l))
      _ -> return ()
    u <- Simplex2.getUB lp2 v
    case u of
      Just u | not (isInteger u) ->
        Simplex2.assertLower lp2 v (fromInteger (floor u))
      _ -> return ()

  bestRef <- newIORef Nothing
  logRef  <- newIORef Nothing
  showRef <- newIORef False

  return $
    MIP
    { mipRootLP = lp2
    , mipIVs    = ivs
    , mipBest   = bestRef
    , mipLogger = logRef
    , mipShowRational = showRef
    }

optimize :: Solver -> (Model -> Rational -> IO ()) -> IO OptResult
optimize solver update = do
  let lp = mipRootLP solver
  log solver "MIP: Solving LP relaxation..."
  ret <- Simplex2.optimize lp
  case ret of
    Unbounded -> do
      log solver "MIP: LP relaxation is unbounded"
      let ivs = mipIVs solver
      if IS.null ivs
        then return Unbounded
        else do
          {-
            Fallback to Fourier-Motzkin + OmegaTest
            * In general, original problem may have optimal
              solution even though LP relaxiation is unbounded.
            * But if restricted to rational numbers, the
              original problem is unbounded or unsatisfiable
              when LP relaxation is unbounded.
          -}
          log solver "MIP: falling back to Fourier-Motzkin + OmegaTest"
          t <- Simplex2.getTableau lp
          let ds = [LA.varExpr v .==. def | (v, def) <- IM.toList t]
          n <- Simplex2.nVars lp
          bs <- liftM concat $ forM [0..n-1] $ \v -> do
            lb <- Simplex2.getLB lp v
            ub <- Simplex2.getUB lp v
            return $ [LA.varExpr v .>=. LA.constExpr (fromJust lb) | isJust lb] ++
                     [LA.varExpr v .<=. LA.constExpr (fromJust ub) | isJust ub]
          case OmegaTest.solveQFLA (bs ++ ds) ivs of
            Just _ -> return Unbounded
            Nothing -> return Unsat

    Optimum -> do
      s0 <- showValue solver =<< Simplex2.getObjValue lp
      log solver ("MIP: LP relaxation optimum is " ++ s0)
      log solver "MIP: Integer optimization begins..."
      let root = Node{ ndLP = lp, ndDepth = 0 }
      q <- SQ.newFifo :: IO (SQ.SeqQueue Node)
      SQ.enqueue q root
      let loop = do
            size <- SQ.queueSize q
            m <- SQ.dequeue q
            case m of
              Nothing -> return ()
              Just nd -> do
                let lp = ndLP nd
                val <- Simplex2.getObjValue lp
                p <- prune solver val
                if p
                  then loop
                  else do
                    xs <- violated nd (mipIVs solver)
                    case xs of
                      [] -> do
                        writeIORef (mipBest solver) (Just nd)
                        m <- Simplex2.model lp
                        update m val
                        loop
                      _ -> do
                        r <- if ndDepth nd `mod` 100 /= 0
                             then return Nothing
                             else liftM listToMaybe $ filterM (canDeriveGomoryCut lp) $ map fst xs
                        case r of
                          Nothing -> do -- branch
                            let (v0,val0) = fst $ maximumBy (comparing snd)
                                            [((v,val), abs (fromIntegral (round val) - val)) | (v,val) <- xs]
                            let lp1 = lp
                            lp2 <- Simplex2.cloneSolver lp
                            Simplex2.assertAtom lp1 (LA.varExpr v0 .<=. LA.constExpr (fromIntegral (floor val0)))
                            Simplex2.assertAtom lp2 (LA.varExpr v0 .>=. LA.constExpr (fromIntegral (ceiling val0)))
                            b <- Simplex2.dualSimplex lp1
                            when (b == Optimum) $ SQ.enqueue q (Node lp1 (ndDepth nd + 1))
                            b <- Simplex2.dualSimplex lp2
                            when (b == Optimum) $ SQ.enqueue q (Node lp2 (ndDepth nd + 1))
                          Just v -> do -- cut
                            atom <- deriveGomoryCut lp (mipIVs solver) v
                            Simplex2.assertAtom lp atom
                            b <- Simplex2.dualSimplex lp
                            when (b == Optimum) $ SQ.enqueue q (Node lp (ndDepth nd + 1))
                        loop

      loop
      m <- readIORef (mipBest solver)
      case m of
        Nothing -> return Unsat
        Just _ -> return Optimum

model :: Solver -> IO Model
model solver = do
  m <- readIORef (mipBest solver)
  case m of
    Nothing -> error "no model"
    Just node -> Simplex2.model (ndLP node)

getObjValue :: Solver -> IO Rational
getObjValue solver = do
  m <- readIORef (mipBest solver)
  case m of
    Nothing -> error "no model"
    Just node -> Simplex2.getObjValue (ndLP node)

violated :: Node -> IS.IntSet -> IO [(Var, Rational)]
violated node ivs = do
  m <- Simplex2.model (ndLP node)
  let p (v,val) = v `IS.member` ivs && not (isInteger val)
  return $ filter p (IM.toList m)

prune :: Solver -> Rational -> IO Bool
prune solver lb = do
  b <- readIORef (mipBest solver)
  case b of
    Nothing -> return False
    Just bestNode -> do
      bestObj <- Simplex2.getObjValue (ndLP bestNode)
      dir <- Simplex2.getOptDir (mipRootLP solver)
      return $ if dir==OptMin then bestObj <= lb else bestObj >= lb

showValue :: Solver -> Rational -> IO String
showValue solver v
  | denominator v == 1 = return $ show (numerator v)
  | otherwise = do
      printRat <- readIORef (mipShowRational solver)
      if printRat
        then return $ show (numerator v) ++ "/" ++ show (denominator v)
        else return $ show (fromRational v :: Double)

setShowRational :: Solver -> Bool -> IO ()
setShowRational solver = writeIORef (mipShowRational solver)

{--------------------------------------------------------------------
  Logging
--------------------------------------------------------------------}

-- | set callback function for receiving messages.
setLogger :: Solver -> (String -> IO ()) -> IO ()
setLogger solver logger = do
  writeIORef (mipLogger solver) (Just logger)

log :: Solver -> String -> IO ()
log solver msg = logIO solver (return msg)

logIO :: Solver -> IO String -> IO ()
logIO solver action = do
  m <- readIORef (mipLogger solver)
  case m of
    Nothing -> return ()
    Just logger -> action >>= logger

{--------------------------------------------------------------------
  GomoryCut
--------------------------------------------------------------------}

deriveGomoryCut :: Simplex2.Solver -> IS.IntSet -> Var -> IO (LA.Atom Rational)
deriveGomoryCut lp ivs xi = do
  v0 <- Simplex2.getValue lp xi
  let f0 = fracPart v0
  assert (0 < f0 && f0 < 1) $ return ()

  row <- Simplex2.getRow lp xi

  -- remove fixed variables
  let p (aij,xj) = do
        lb <- Simplex2.getLB lp xj
        ub <- Simplex2.getUB lp xj
        case (lb,ub) of
          (Just l, Just u) -> return (l < u)
          _ -> return True
  ns <- filterM p $ LA.terms row

  js <- flip filterM ns $ \(_, xj) -> do
    vj <- Simplex2.getValue lp xj
    lb <- Simplex2.getLB lp xj
    return $ Just vj == lb
  ks <- flip filterM ns $ \(_, xj) -> do
    vj <- Simplex2.getValue lp xj
    ub <- Simplex2.getUB lp xj
    return $ Just vj == ub

  xs1 <- forM js $ \(aij, xj) -> do
    vj <- Simplex2.getValue lp xj
    let fj = fracPart vj
    Just lj <- Simplex2.getLB lp xj
    let c = if xj `IS.member` ivs
            then (if fj <= 1 - f0 then fj  / (1 - f0) else ((1 - fj) / f0))
            else (if aij > 0      then aij / (1 - f0) else (-aij     / f0))
    return $ c .*. (LA.varExpr xj .-. LA.constExpr lj)
  xs2 <- forM ks $ \(aij, xj) -> do
    vj <- Simplex2.getValue lp xj
    let fj = fracPart vj
    Just uj <- Simplex2.getUB lp xj
    let c = if xj `IS.member` ivs
            then (if fj <= f0 then fj  / f0 else ((1 - fj) / (1 - f0)))
            else (if aij > 0  then aij / f0 else (-aij     / (1 - f0)))
    return $ c .*. (LA.constExpr uj .-. LA.varExpr xj)

  return $ lsum xs1 .+. lsum xs2 .>=. LA.constExpr 1

-- TODO: Simplex2をδに対応させたら、xi, xj がδを含まない有理数であるという条件も必要
canDeriveGomoryCut :: Simplex2.Solver -> Var -> IO Bool
canDeriveGomoryCut lp xi = do
  b <- Simplex2.isBasicVariable lp xi
  if not b
    then return False
    else do
      val <- Simplex2.getValue lp xi
      if isInteger val
        then return False
        else do
          row <- Simplex2.getRow lp xi
          ys <- forM (LA.terms row) $ \(ai,xj) -> do
            vj <- Simplex2.getValue lp xj
            lb <- Simplex2.getLB lp xj
            ub <- Simplex2.getUB lp xj
            return $ Just vj == lb || Just vj == ub
          return (and ys)
