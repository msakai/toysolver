{-# OPTIONS_GHC -Wall #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.CongruenceClosure
-- Copyright   :  (c) Masahiro Sakai 2012, 2015
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
module ToySolver.CongruenceClosure
  ( Solver
  , Var
  , Term (..)
  , FlatTerm (..)
  , newSolver
  , newVar
  , merge
  , mergeFlatTerm
  , areCongruent
  , areCongruentFlatTerm
  ) where

import Prelude hiding (lookup)

import Control.Exception (assert)
import Control.Monad
import Data.IORef
import Data.Maybe
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import Data.Map (Map)
import qualified Data.Map as Map
    
type Var = Int

data Term = TApp Var [Term]

data FlatTerm
  = FTConst Var
  | FTApp Var Var
  deriving (Ord, Eq, Show)

-- | @Eqn a b c@ represents an equation "f(a,b) = c"
data Eqn1 = Eqn1 Var Var Var

type PendingEqn = Either (Var,Var) (Eqn1, Eqn1)

data Solver
  = Solver
  { svVarCounter           :: IORef Int
  , svDefs                 :: IORef (IntMap (Var,Var), Map (Var,Var) Var)
  , svPending              :: IORef [PendingEqn]
  , svRepresentativeTable  :: IORef (IntMap Var) -- 本当は配列が良い
  , svClassList            :: IORef (IntMap [Var])
  , svUseList              :: IORef (IntMap [Eqn1])
  , svLookupTable          :: IORef (IntMap (IntMap Eqn1))
  }

newSolver :: IO Solver
newSolver = do
  vcnt     <- newIORef 0
  defs     <- newIORef (IntMap.empty, Map.empty)
  pending  <- newIORef []
  rep      <- newIORef IntMap.empty
  classes  <- newIORef IntMap.empty
  useList  <- newIORef IntMap.empty
  lookup   <- newIORef IntMap.empty
  return $
    Solver
    { svVarCounter          = vcnt
    , svDefs                = defs
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

merge :: Solver -> Term -> Term -> IO ()
merge solver t u = do
  t' <- transform solver t
  u' <- transform solver u
  case (t', u') of
    (FTConst c, _) -> mergeFlatTerm solver (u', c)
    (_, FTConst c) -> mergeFlatTerm solver (t', c)
    _ -> do
      c <- nameFlatTerm solver u'
      mergeFlatTerm solver (t', c)

mergeFlatTerm :: Solver -> (FlatTerm, Var) -> IO ()
mergeFlatTerm solver (s, a) = do
  case s of
    FTConst c -> do
      addToPending solver (Left (c, a))
      propagate solver
    FTApp a1 a2 -> do
      let eq1 = Eqn1 a1 a2 a
      a1' <- getRepresentative solver a1
      a2' <- getRepresentative solver a2
      ret <- lookup solver a1' a2'
      case ret of
        Just eq2 -> do
          addToPending solver $ Right (eq1, eq2)
          propagate solver
        Nothing -> do          
          setLookup solver a1' a2' eq1
          modifyIORef (svUseList solver) $
            IntMap.alter (Just . (eq1 :) . fromMaybe []) a1' .
            IntMap.alter (Just . (eq1 :) . fromMaybe []) a2'

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
                    Right (Eqn1 _ _ a, Eqn1 _ _ b) -> (a,b)
      a' <- getRepresentative solver a
      b' <- getRepresentative solver b
      unless (a' == b') $ do
        clist <- readIORef (svClassList  solver)
        let classA = clist IntMap.! a'
            classB = clist IntMap.! b'
        if length classA < length classB then
          update a' b' classA classB
        else
          update b' a' classB classA

    update a' b' classA classB = do
      modifyIORef (svRepresentativeTable solver) $ 
        -- Note that 'IntMap.union' is left biased.
        IntMap.union (IntMap.fromList [(c,b') | c <- classA])
      modifyIORef (svClassList solver) $
        IntMap.insert b' (classA ++ classB) . IntMap.delete a'

      useList <- readIORef (svUseList solver)
      forM_ (useList IntMap.! a') $ \eq1@(Eqn1 c1 c2 _) -> do
        c1' <- getRepresentative solver c1
        c2' <- getRepresentative solver c2
        assert (a' == c1' || a' == c2') $ return ()
        -- unless (a' == c1' || a' == c2') $ error "CongruenceClosure.propagate.update: should not happen"
        ret <- lookup solver c1' c2'
        case ret of
          Just eq2 -> do
            addToPending solver $ Right (eq1, eq2)
          Nothing -> do
            return ()
      writeIORef (svUseList solver) $ IntMap.delete a' useList        

areCongruent :: Solver -> Term -> Term -> IO Bool
areCongruent solver t1 t2 = do
  u1 <- transform solver t1
  u2 <- transform solver t2
  areCongruentFlatTerm solver u1 u2

areCongruentFlatTerm :: Solver -> FlatTerm -> FlatTerm -> IO Bool
areCongruentFlatTerm solver t1 t2 = do
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
    Just (Eqn1 _ _ a) -> liftM FTConst $ getRepresentative solver a
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

transform :: Solver -> Term -> IO FlatTerm
transform solver (TApp f xs) = do
  xs' <- mapM (transform solver) xs
  let phi t u = do
        t' <- nameFlatTerm solver t
        u' <- nameFlatTerm solver u
        return $ FTApp t' u'
  foldM phi (FTConst f) xs'

-- バックトラックとの関係が悩ましい
-- 最初からその変数が存在したかのようにふるまいたいが
nameFlatTerm :: Solver -> FlatTerm -> IO Var
nameFlatTerm _ (FTConst c) = return c
nameFlatTerm solver (FTApp c d) = do
  (defs1,defs2) <- readIORef $ svDefs solver
  case Map.lookup (c,d) defs2 of
    Just a -> return a
    Nothing -> do
      a <- newVar solver
      writeIORef (svDefs solver) (IntMap.insert a (c,d) defs1, Map.insert (c,d) a defs2)
      mergeFlatTerm solver (FTApp c d, a)
      return a
