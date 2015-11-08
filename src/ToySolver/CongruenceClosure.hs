{-# LANGUAGE BangPatterns #-}
{-# OPTIONS_GHC -Wall #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.CongruenceClosure
-- Copyright   :  (c) Masahiro Sakai 2012, 2015
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  non-portable (BangPatterns)
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
  , merge'    
  , mergeFlatTerm
  , mergeFlatTerm'
  , areCongruent
  , areCongruentFlatTerm
  , explain
  , explainFlatTerm
  , explainVar

  , pushBacktrackPoint
  , popBacktrackPoint
  ) where

import Prelude hiding (lookup)

import Control.Exception (assert)
import Control.Monad
import Data.IORef
import Data.Maybe
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Semigroup

import qualified ToySolver.Internal.Data.Vec as Vec
    
type Var = Int

data Term = TApp Var [Term]

data FlatTerm
  = FTConst Var
  | FTApp Var Var
  deriving (Ord, Eq, Show)

type ConstrID = Int

-- | @Eqn0 cid a b@ represents an equation "a = b"
data Eqn0 = Eqn0 (Maybe ConstrID) Var Var
  deriving (Eq, Ord, Show)

-- | @Eqn1 cid a b c@ represents an equation "f(a,b) = c"
data Eqn1 = Eqn1 (Maybe ConstrID) Var Var Var
  deriving (Eq, Ord, Show)

type PendingEqn = Either Eqn0 (Eqn1, Eqn1)

data Class
  = ClassSingleton !Var
  | ClassUnion !Int Class Class
  deriving (Show)

instance Semigroup Class where
  xs <> ys = ClassUnion (classSize xs + classSize ys) xs ys
  stimes = stimesIdempotent

classSize :: Class -> Int
classSize (ClassSingleton _) = 1
classSize (ClassUnion size _ _) = size

-- Use mono-traversable package?
classToList :: Class -> [Var]
classToList c = f c []
  where
    f (ClassSingleton v) = (v :)
    f (ClassUnion _ xs ys) = f xs . f ys

{-
-- Use mono-traversable package?
classForM_ :: Monad m => (Var -> m ()) -> Class -> m ()
classForM_ f = g
  where
    g (ClassSingleton v) = f v
    g (ClassUnion _ xs ys) = g xs >> g ys
-}

data Solver
  = Solver
  { svVarCounter           :: IORef Int
  , svDefs                 :: IORef (IntMap (Var,Var), Map (Var,Var) Var)
  , svPending              :: IORef [PendingEqn]
  , svRepresentativeTable  :: IORef (IntMap Var) -- 本当は配列が良い
  , svClassList            :: IORef (IntMap Class)
  , svParent               :: IORef (IntMap (Var, PendingEqn))
  , svUseList              :: IORef (IntMap [(Eqn1, Level, Gen)])
  , svLookupTable          :: IORef (IntMap (IntMap Eqn1))

  -- for Backtracking
  , svTrail :: Vec.Vec [TrailItem]
  , svLevelGen :: Vec.UVec Int
  }

newSolver :: IO Solver
newSolver = do
  vcnt     <- newIORef 0
  defs     <- newIORef (IntMap.empty, Map.empty)
  pending  <- newIORef []
  rep      <- newIORef IntMap.empty
  classes  <- newIORef IntMap.empty
  parent   <- newIORef IntMap.empty
  useList  <- newIORef IntMap.empty
  lookup   <- newIORef IntMap.empty

  trail <- Vec.new
  gen <- Vec.new
  Vec.push gen 0
      
  return $
    Solver
    { svVarCounter          = vcnt
    , svDefs                = defs
    , svPending             = pending
    , svRepresentativeTable = rep
    , svClassList           = classes
    , svParent              = parent
    , svUseList             = useList
    , svLookupTable         = lookup

    , svTrail = trail
    , svLevelGen = gen
    }

newVar :: Solver -> IO Var
newVar solver = do
  v <- readIORef (svVarCounter solver)
  writeIORef (svVarCounter solver) $! v + 1
  modifyIORef (svRepresentativeTable solver) (IntMap.insert v v)
  modifyIORef (svClassList solver) (IntMap.insert v (ClassSingleton v))
  modifyIORef (svUseList solver) (IntMap.insert v [])
  return v

merge :: Solver -> Term -> Term -> IO ()
merge solver t u = merge' solver t u Nothing

merge' :: Solver -> Term -> Term -> Maybe ConstrID -> IO ()
merge' solver t u cid = do
  t' <- transform solver t
  u' <- transform solver u
  case (t', u') of
    (FTConst c, _) -> mergeFlatTerm' solver u' c cid
    (_, FTConst c) -> mergeFlatTerm' solver t' c cid
    _ -> do
      c <- nameFlatTerm solver u'
      mergeFlatTerm' solver t' c cid

mergeFlatTerm :: Solver -> FlatTerm -> Var -> IO ()
mergeFlatTerm solver s a = mergeFlatTerm' solver s a Nothing

mergeFlatTerm' :: Solver -> FlatTerm -> Var -> Maybe ConstrID -> IO ()
mergeFlatTerm' solver s a cid = do
  case s of
    FTConst c -> do
      let eq1 = Eqn0 cid c a
      addToPending solver (Left eq1)
      propagate solver
      checkInvariant solver
    FTApp a1 a2 -> do
      let eq1 = Eqn1 cid a1 a2 a
      a1' <- getRepresentative solver a1
      a2' <- getRepresentative solver a2
      ret <- lookup solver a1' a2'
      case ret of
        Just eq2 -> do
          addToPending solver $ Right (eq1, eq2)
          propagate solver
          checkInvariant solver
        Nothing -> do          
          setLookup solver a1' a2' eq1
          lv <- getCurrentLevel solver
          gen <- getLevelGen solver lv
          modifyIORef (svUseList solver) $
            IntMap.adjust ((eq1, lv, gen) :) a1' .
            IntMap.adjust ((eq1, lv, gen) :) a2'
          checkInvariant solver

propagate :: Solver -> IO ()
propagate solver = go
  where
    go = do
      checkInvariant solver
      ps <- readIORef (svPending solver)
      case ps of
        [] -> return ()
        (p:ps') -> do
          writeIORef (svPending solver) ps'
          processEqn p
          go

    processEqn p = do
      let (a,b) = case p of
                    Left (Eqn0 _ a b) -> (a,b)
                    Right (Eqn1 _ _ _ a, Eqn1 _ _ _ b) -> (a,b)
      a' <- getRepresentative solver a
      b' <- getRepresentative solver b
      unless (a' == b') $ do
        clist <- readIORef (svClassList  solver)
        let classA = clist IntMap.! a'
            classB = clist IntMap.! b'
        (a,b,a',b',classA,classB) <- return $
          if classSize classA < classSize classB then
            (a,b,a',b',classA,classB)
          else
            (b,a,b',a',classB,classA)
        origRootA <- updateParent a b p
        update a' b' classA classB
        addToTrail solver (TrailMerge a' b' a origRootA)

    update a' b' classA classB = do
      modifyIORef (svRepresentativeTable solver) $ 
        -- Note that 'IntMap.union' is left biased.
        IntMap.union (IntMap.fromList [(c,b') | c <- classToList classA])
      modifyIORef (svClassList solver) $
        IntMap.insert b' (classA <> classB) . IntMap.delete a'

      lv <- getCurrentLevel solver
      lv_gen <- getLevelGen solver lv
      useList <- readIORef (svUseList solver)
      useList_a' <- flip filterM (useList IntMap.! a') $ \(eq1@(Eqn1 _ c1 c2 _), lv2, lv2_gen2) -> do
        lv2_gen <- getLevelGen solver lv2
        if lv2 <= lv && lv2_gen2 == lv2_gen then do
          c1' <- getRepresentative solver c1
          c2' <- getRepresentative solver c2
          assert (b' == c1' || b' == c2') $ return ()
          -- unless (b' == c1' || b' == c2') $ error "CongruenceClosure.propagate.update: should not happen"
          ret <- lookup solver c1' c2'
          case ret of
            Just eq2 -> do
              addToPending solver $ Right (eq1, eq2)
            Nothing -> do
              setLookup solver c1' c2' eq1
              modifyIORef (svUseList solver) $ IntMap.adjust ((eq1, lv, lv_gen) :) b'
              return ()
          return True
        else do
          -- out-of-date entry
          return False
      modifyIORef (svUseList solver) (IntMap.insert a' useList_a')

    -- Insert edge a→b labelled with a_eq_b into the proof forest, and re-orient its original ancestors.
    updateParent a b a_eq_b = do
      let loop d (c, c_eq_d) = do
            tbl <- readIORef (svParent solver)
            writeIORef (svParent solver) (IntMap.insert d (c, c_eq_d) tbl)
            case IntMap.lookup d tbl of
              Nothing -> return d
              Just (e, d_eq_e) -> loop e (d, d_eq_e)
      loop a (b, a_eq_b)

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
    Just (Eqn1 _ _ _ a) -> liftM FTConst $ getRepresentative solver a
    Nothing -> return $ FTApp u1 u2

checkInvariant :: Solver -> IO ()
checkInvariant solver | True = return ()
checkInvariant solver = do
  nv <- readIORef (svVarCounter solver)
  representativeTable <- readIORef (svRepresentativeTable solver)
  classList <- readIORef (svClassList solver)
                         
  let representatives = IntSet.fromList [a' | (_,a') <- IntMap.toList representativeTable]
  unless (IntMap.keysSet classList == representatives) $
    error "CongruenceClosure.checkInvariant: IntMap.keysSet classList /= representatives"

  unless (IntSet.unions (map (IntSet.fromList . classToList) (IntMap.elems classList)) == IntSet.fromList [0..nv-1]) $
    error "CongruenceClosure.checkInvariant: classList is not exhaustive"
  forM_ (IntMap.toList classList) $ \(a, bs) -> do
    forM_ (classToList bs) $ \b -> do
      b' <- getRepresentative solver b
      unless (a == b') $
        error "CongruenceClosure.checkInvariant: inconsistency between classList and representativeTable"

  pendings <- readIORef (svPending solver)
  forM_ pendings $ \p -> do
    case p of
      Left _ -> return ()
      Right (Eqn1 _ a1 a2 _, Eqn1 _ b1 b2 _) -> do
        a1' <- getRepresentative solver a1
        a2' <- getRepresentative solver a2
        b1' <- getRepresentative solver b1
        b2' <- getRepresentative solver b2
        unless (a1' == b1' && a2' == b2') $
          error "CongruenceClosure.checkInvariant: error in pendingList"

  useList <- readIORef (svUseList solver)
  lv <- getCurrentLevel solver
  forM_ (IntSet.toList representatives) $ \a -> do
    forM_ (useList IntMap.! a) $ \(Eqn1 _ b1 b2 _, lv2, lv2_gen2) -> do
      lv2_gen <- getLevelGen solver lv2
      when (lv2 <= lv && lv2_gen2 == lv2_gen) $ do
        b1' <- getRepresentative solver b1
        b2' <- getRepresentative solver b2
        unless (a == b1' || a == b2') $
          error "CongruenceClosure.checkInvariant: error in useList"

  forM_ (IntSet.toList representatives) $ \b -> do
    forM_ (IntSet.toList representatives) $ \c -> do
      m <- lookup solver b c
      case m of
        Nothing -> return ()
        Just (Eqn1 _ a1 a2 _) -> do
          a1' <- getRepresentative solver a1
          a2' <- getRepresentative solver a2
          unless (b == a1' && c == a2') $
            error "CongruenceClosure.checkInvariant: error in lookupTable"

explain :: Solver -> Term -> Term -> IO (Maybe IntSet)
explain solver t1 t2 = do
  c1 <- transform solver t1
  c2 <- transform solver t2
  explainFlatTerm solver c1 c2

explainFlatTerm :: Solver -> FlatTerm -> FlatTerm -> IO (Maybe IntSet)
explainFlatTerm solver t1 t2 = do
  c1 <- nameFlatTerm solver t1
  c2 <- nameFlatTerm solver t2
  explainVar solver c1 c2

explainVar :: Solver -> Var -> Var -> IO (Maybe IntSet)
explainVar solver c1 c2 = do
  n <- readIORef (svVarCounter solver)
  
  -- Additional union-find data structure
  representativeTable2 <- newIORef (IntMap.fromList [(a,a) | a <- [0..n-1]])
  classList2 <- newIORef (IntMap.fromList [(a, IntSet.singleton a) | a <- [0..n-1]])
  highestNodeTable <- newIORef (IntMap.fromList [(a,a) | a <- [0..n-1]])
                
  let getRepresentative2 :: Var -> IO Var
      getRepresentative2 a = do
        m <- readIORef representativeTable2
        return $ m IntMap.! a

      highestNode :: Var -> IO Var
      highestNode c = do
        d <- getRepresentative2 c
        m <- readIORef highestNodeTable
        return $ m IntMap.! d

      union :: Var -> Var -> IO ()
      union a b = do
        a' <- getRepresentative2 a
        b' <- getRepresentative2 b
        cls <- readIORef classList2
        let classA = cls IntMap.! a'
            classB = cls IntMap.! b'
        h <- highestNode b'
        if IntSet.size classA < IntSet.size classB then do
          update a' b' classA classB h
        else do
          update b' a' classB classA h

        where
          update a' b' classA classB h = do
            modifyIORef representativeTable2 $ 
              -- Note that 'IntMap.union' is left biased.
              IntMap.union (IntMap.fromAscList [(c,b') | c <- IntSet.toAscList classA])
            modifyIORef classList2 $
              IntMap.insert b' (classA `IntSet.union` classB) . IntMap.delete a'
            modifyIORef highestNodeTable $
              IntMap.insert b' h . IntMap.delete a'

  pendingProofs <- newIORef ([(c1,c2)] :: [(Var,Var)])
  result <- newIORef ([] :: [Int])

  let loop = do
        ps <- readIORef pendingProofs
        case ps of
          [] -> return True
          ((a,b) : ps') -> do
            writeIORef pendingProofs ps'
            m <- nearestCommonAncestor solver a b
            case m of
              Nothing -> return False
              Just c -> do
                explainAlongPath a c
                explainAlongPath b c
                loop

      explainAlongPath :: Var -> Var -> IO ()
      explainAlongPath a c = do
        a <- highestNode a
        -- note that c is already @highestNode c@
        let loop a =
              unless (a == c) $ do
                Just (b, eq) <- getParent solver a
                case eq of
                  Left (Eqn0 cid _ _) -> do
                    modifyIORef result (maybeToList cid ++)
                  Right (Eqn1 cid1 a1 a2 _, Eqn1 cid2 b1 b2 _) -> do
                    modifyIORef result (catMaybes [cid1,cid2] ++)
                    modifyIORef pendingProofs (\xs -> (a1,b1) : (a2,b2) : xs)
                union a b
                loop =<< highestNode b
        loop a

  b <- loop
  if b
  then liftM (Just . IntSet.fromList) $ readIORef result
  else return Nothing

-- -------------------------------------------------------------------
-- Backtracking
-- -------------------------------------------------------------------

type Level = Int
type Gen = Int

data TrailItem
  = TrailMerge !Var !Var !Var !Var
  | TrailSetLookup !Var !Var
  deriving (Show)

addToTrail :: Solver -> TrailItem -> IO ()
addToTrail solver item = do
  lv <- getCurrentLevel solver
  when (lv /= 0) $ do
    xs <- Vec.unsafeRead (svTrail solver) (lv - 1)
    seq item $ Vec.unsafeWrite (svTrail solver) (lv - 1) (item : xs)
       
getCurrentLevel :: Solver -> IO Level
getCurrentLevel solver = Vec.getSize (svTrail solver)

getLevelGen :: Solver -> Level -> IO Gen
getLevelGen solver lv = Vec.unsafeRead (svLevelGen solver) lv

pushBacktrackPoint :: Solver -> IO ()
pushBacktrackPoint solver = do
  Vec.push (svTrail solver) []
  lv <- getCurrentLevel solver
  size <- Vec.getSize (svLevelGen solver)
  if lv < size then do
    g <- Vec.unsafeRead (svLevelGen solver) lv
    Vec.unsafeWrite (svLevelGen solver) lv (g + 1)
  else
    Vec.push (svLevelGen solver) 0

popBacktrackPoint :: Solver -> IO ()
popBacktrackPoint solver = do
  xs <- Vec.unsafePop (svTrail solver)
  forM_ xs $ \item -> do
    case item of
      TrailSetLookup a' b' -> do
        modifyIORef (svLookupTable solver) (IntMap.adjust (IntMap.delete b') a')
      TrailMerge a' b' a origRootA -> do
        -- Revert changes to Union-Find data strucutres
        classList <- readIORef (svClassList solver)
        let (ClassUnion _ origClassA origClassB) = classList IntMap.! b'
        modifyIORef (svRepresentativeTable solver) $
          -- Note that 'IntMap.union' is left biased.
          IntMap.union (IntMap.fromList [(c,a') | c <- classToList origClassA])                                                          
        writeIORef (svClassList solver) $
          IntMap.insert a' origClassA $ IntMap.insert b' origClassB $ classList

        -- Revert changes to proof-forest data strucutres
        let loop c p = do
              tbl <- readIORef (svParent solver)
              writeIORef (svParent solver) (IntMap.update (const p) c tbl)
              unless (c == a) $ do
                let (d, c_eq_d) = tbl IntMap.! c
                loop d (Just (c, c_eq_d))
        loop origRootA Nothing

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
  addToTrail solver (TrailSetLookup a1 a2)

addToPending :: Solver -> PendingEqn -> IO ()
addToPending solver eqn = modifyIORef (svPending solver) (eqn :)

getRepresentative :: Solver -> Var -> IO Var
getRepresentative solver c = do
  m <- readIORef $ svRepresentativeTable solver
  return $ m IntMap.! c

getParent :: Solver -> Var -> IO (Maybe (Var, PendingEqn))
getParent solver c = do
  m <- readIORef $ svParent solver
  return $ IntMap.lookup c m

nearestCommonAncestor :: Solver -> Var -> Var -> IO (Maybe Var)
nearestCommonAncestor solver a b = do
  let loop c !ret = do
        m <- getParent solver c
        case m of
          Nothing -> return ret
          Just (d,_) -> loop d (IntSet.insert d ret)
  a_ancestors <- loop a (IntSet.singleton a)

  let loop2 c = do
        if c `IntSet.member` a_ancestors then
          return (Just c)
        else do
          m <- getParent solver c
          case m of
            Nothing -> return Nothing
            Just (d,_) -> loop2 d
  loop2 b

transform :: Solver -> Term -> IO FlatTerm
transform solver (TApp f xs) = do
  xs' <- mapM (transform solver) xs
  let phi t u = do
        t' <- nameFlatTerm solver t
        u' <- nameFlatTerm solver u
        return $ FTApp t' u'
  foldM phi (FTConst f) xs'

nameFlatTerm :: Solver -> FlatTerm -> IO Var
nameFlatTerm _ (FTConst c) = return c
nameFlatTerm solver (FTApp c d) = do
  (defs1,defs2) <- readIORef $ svDefs solver
  a <- case Map.lookup (c,d) defs2 of
         Just a -> return a
         Nothing -> do
           a <- newVar solver
           writeIORef (svDefs solver) (IntMap.insert a (c,d) defs1, Map.insert (c,d) a defs2)
           return a
  -- We call 'mergeFlatTerm' everytime, because backtracking might have canceled its effect.
  mergeFlatTerm solver (FTApp c d) a
  return a
