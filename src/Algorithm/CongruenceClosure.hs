{-# OPTIONS_GHC -Wall #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Algorithm.CongruenceClosure
-- Copyright   :  (c) Masahiro Sakai 2012
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  portable
--
-- References:
--
-- * R. Nieuwenhuis and A. Oliveras, "Fast congruence closure and extensions,"
--   Information and Computation, vol. 205, no. 4, pp. 557-580, Apr. 2007.
--   <http://www.lsi.upc.edu/~oliveras/espai/papers/IC.pdf>
--
-----------------------------------------------------------------------------
module Algorithm.CongruenceClosure
  ( Solver
  , Var
  , FlatTerm (..)
  , newSolver
  , newVar
  , merge
  , areCongruent
  ) where

import Prelude hiding (lookup)

import Control.Monad
import Data.IORef
import Data.Maybe
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap

type Var = Int

data FlatTerm
  = FTConst Var
  | FTApp Var Var
  deriving (Ord, Eq, Show)

type Eqn1 = (FlatTerm, Var)
type PendingEqn = Either (Var,Var) (Eqn1, Eqn1)

data Solver
  = Solver
  { svVarCounter           :: IORef Int
  , svPending              :: IORef [PendingEqn]
  , svRepresentativeTable  :: IORef (IntMap Var) -- 本当は配列が良い
  , svClassList            :: IORef (IntMap [Var])
  , svUseList              :: IORef (IntMap [Eqn1])
  , svLookupTable          :: IORef (IntMap (IntMap Eqn1))
  }

newSolver :: IO Solver
newSolver = do
  vcnt     <- newIORef 0
  pending  <- newIORef []
  rep      <- newIORef IntMap.empty
  classes  <- newIORef IntMap.empty
  useList  <- newIORef IntMap.empty
  lookup   <- newIORef IntMap.empty
  return $
    Solver
    { svVarCounter          = vcnt
    , svPending             = pending
    , svRepresentativeTable = rep
    , svClassList           = classes
    , svUseList             = useList
    , svLookupTable         = lookup
    }

newVar :: Solver -> IO Var
newVar solver = do
  v <- readIORef (svVarCounter solver)
  writeIORef (svVarCounter solver) $! v + 1
  modifyIORef (svRepresentativeTable solver) (IntMap.insert v v)
  modifyIORef (svClassList solver) (IntMap.insert v [v])
  modifyIORef (svUseList solver) (IntMap.insert v [])
  return v

merge :: Solver -> (FlatTerm, Var) -> IO ()
merge solver (s, a) = do
  case s of
    FTConst c -> do
      addToPending solver (Left (c, a))
      propagate solver
    FTApp a1 a2 -> do
      a1' <- getRepresentative solver a1
      a2' <- getRepresentative solver a2
      ret <- lookup solver a1' a2'
      case ret of
        Just (FTApp b1 b2, b) -> do
          addToPending solver $ Right ((FTApp a1 a2, a), (FTApp b1 b2, b))
          propagate solver
        Nothing -> do
          setLookup solver a1' a2' (FTApp a1 a2, a)
          modifyIORef (svUseList solver) $
            IntMap.alter (Just . ((FTApp a1 a2, a) :) . fromMaybe []) a1' .
            IntMap.alter (Just . ((FTApp a1 a2, a) :) . fromMaybe []) a2'

propagate :: Solver -> IO ()
propagate solver = go
  where
    go = do
      ps <- readIORef (svPending solver)
      case ps of
        [] -> return ()
        (p:ps') -> do
          writeIORef (svPending solver) ps'
          processEqn p
          go

    processEqn p = do
      let (a,b) = case p of
                    Left (a,b) -> (a,b)
                    Right ((_, a), (_, b)) -> (a,b)
      a' <- getRepresentative solver a
      b' <- getRepresentative solver b
      if a' == b'
        then return ()
        else do
          clist <- readIORef (svClassList  solver)
          let classA = clist IntMap.! a'
              classB = clist IntMap.! b'
          if length classA < length classB
            then update a' b' classA classB
            else update b' a' classB classA

    update a' b' classA classB = do
      modifyIORef (svRepresentativeTable solver) $ 
        IntMap.union (IntMap.fromList [(c,b') | c <- classA])
      modifyIORef (svClassList solver) $
        IntMap.insert b' (classA ++ classB) . IntMap.delete a'

      useList <- readIORef (svUseList solver)
      forM_ (useList IntMap.! a') $ \(FTApp c1 c2, c) -> do -- FIXME: not exhaustive
        c1' <- getRepresentative solver c1
        c2' <- getRepresentative solver c2
        ret <- lookup solver c1' c2'
        case ret of
          Just (FTApp d1 d2, d) -> do -- FIXME: not exhaustive
            addToPending solver $ Right ((FTApp c1 c2, c), (FTApp d1 d2, d))
          Nothing -> do
            return ()
      writeIORef (svUseList solver) $ IntMap.delete a' useList        

areCongruent :: Solver -> FlatTerm -> FlatTerm -> IO Bool
areCongruent solver t1 t2 = do
  u1 <- normalize solver t1
  u2 <- normalize solver t2
  return $ u1 == u2

normalize :: Solver -> FlatTerm -> IO FlatTerm
normalize solver (FTConst c) = liftM FTConst $ getRepresentative solver c
normalize solver (FTApp t1 t2) = do
  u1 <- getRepresentative solver t1
  u2 <- getRepresentative solver t2
  ret <- lookup solver u1 u2
  case ret of
    Just (FTApp _ _, a) -> liftM FTConst $ getRepresentative solver a
    Nothing -> return $ FTApp u1 u2

{--------------------------------------------------------------------
  Helper funcions
--------------------------------------------------------------------}

lookup :: Solver -> Var -> Var -> IO (Maybe Eqn1)
lookup solver c1 c2 = do
  tbl <- readIORef $ svLookupTable solver
  return $ do
     m <- IntMap.lookup c1 tbl
     IntMap.lookup c2 m

setLookup :: Solver -> Var -> Var -> Eqn1 -> IO ()
setLookup solver a1 a2 eqn = do
  modifyIORef (svLookupTable solver) $
    IntMap.insertWith IntMap.union a1 (IntMap.singleton a2 eqn)

addToPending :: Solver -> PendingEqn -> IO ()
addToPending solver eqn = modifyIORef (svPending solver) (eqn :)

getRepresentative :: Solver -> Var -> IO Var
getRepresentative solver c = do
  m <- readIORef $ svRepresentativeTable solver
  return $ m IntMap.! c
