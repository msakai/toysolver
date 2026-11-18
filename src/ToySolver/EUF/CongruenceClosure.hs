{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_HADDOCK show-extensions #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.EUF.CongruenceClosure
-- Copyright   :  (c) Masahiro Sakai 2012, 2015
-- License     :  BSD-style
--
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  non-portable
--
-- References:
--
-- * R. Nieuwenhuis and A. Oliveras, "Fast congruence closure and extensions,"
--   Information and Computation, vol. 205, no. 4, pp. 557-580, Apr. 2007.
--   <http://www.lsi.upc.edu/~oliveras/espai/papers/IC.pdf>
--
-----------------------------------------------------------------------------
module ToySolver.EUF.CongruenceClosure
  (
  -- * The @Solver@ type
    Solver
  , newSolver

  -- * Problem description
  , FSym
  , Term (..)
  , FlatTerm (..)
  , ConstrID
  , newFSym
  , VAFun (..)
  , newFun
  , newConst
  , merge
  , merge'
  , mergeFlatTerm
  , mergeFlatTerm'

  -- * Query
  , areCongruent
  , areCongruentFlatTerm

  -- * Explanation
  , explain
  , explainFlatTerm
  , explainConst

  -- * Model Construction
  , Entity
  , EntityTuple
  , Model (..)
  , getModel
  , eval
  , evalAp

  -- * Backtracking
  , pushBacktrackPoint
  , popBacktrackPoint

  -- * Low-level operations
  , termToFlatTerm
  , termToFSym
  , fsymToTerm
  , fsymToFlatTerm
  , flatTermToFSym
  ) where

import Prelude hiding (lookup)

import Control.Exception (assert)
import Control.Loop
import Control.Monad
import Control.Monad.ST
import Control.Monad.Primitive
import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IntMap
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Primitive.MutVar
import Data.Set (Set)
import qualified Data.Set as Set

import ToySolver.EUF.CongruenceClosure.Base
import qualified ToySolver.Internal.Data.Vec as Vec

data FlatTerm
  = FTConst !FSym
  | FTApp !FSym !FSym
  deriving (Ord, Eq, Show)

type ConstrID = Int

-- | @Eqn0 cid a b@ represents an equation "a = b"
data Eqn0 = Eqn0 (Maybe ConstrID) !FSym !FSym
  deriving (Eq, Ord, Show)

-- | @Eqn1 cid a b c@ represents an equation "f(a,b) = c"
data Eqn1 = Eqn1 (Maybe ConstrID) !FSym !FSym !FSym
  deriving (Eq, Ord, Show)

-- | An equation @a = b@ represented as either
--
-- * @a = b@ or
--
-- * @f(a1,a2) = a, f(b1,b2) = b@ where @a1 = b1@ and @a2 = b2@ has already been derived.
--
type Eqn = Either Eqn0 (Eqn1, Eqn1)

data Class
  = ClassSingleton !FSym
  | ClassUnion !Int Class Class
  deriving (Show)

instance Semigroup Class where
  xs <> ys = ClassUnion (classSize xs + classSize ys) xs ys

classSize :: Class -> Int
classSize (ClassSingleton _) = 1
classSize (ClassUnion size _ _) = size

-- Use mono-traversable package?
classToList :: Class -> [FSym]
classToList c = f c []
  where
    f (ClassSingleton v) = (v :)
    f (ClassUnion _ xs ys) = f xs . f ys

-- Use mono-traversable package?
classForM_ :: Monad m => Class -> (FSym -> m ()) -> m ()
classForM_ xs f = g xs
  where
    g (ClassSingleton v) = f v
    g (ClassUnion _ xs ys) = g xs >> g ys

data Solver s
  = Solver
  { svDefs                 :: !(MutVar s (IntMap (FSym,FSym), Map (FSym,FSym) FSym))
  , svRepresentativeTable  :: !(Vec.UVec s FSym)
  , svClassList            :: !(Vec.Vec s Class)
  , svParent               :: !(MutVar s (IntMap (FSym, Eqn)))
  , svUseList              :: !(MutVar s (IntMap [(Eqn1, Level, Gen)]))
  , svLookupTable          :: !(MutVar s (IntMap (IntMap Eqn1)))

  -- workspace for constraint propagation
  , svPending :: !(Vec.Vec s Eqn)

  -- workspace for explanation generation
  , svERepresentativeTable :: !(Vec.UVec s FSym)
  , svEClassList           :: !(Vec.Vec s Class)
  , svEHighestNodeTable    :: !(Vec.UVec s FSym)
  , svEPendingProofs       :: !(Vec.Vec s (FSym,FSym))

  -- for backtracking
  , svTrail :: !(Vec.Vec s [TrailItem])
  , svLevelGen :: !(Vec.UVec s Int)
  , svIsAfterBacktracking :: !(MutVar s Bool)
  }

newSolver :: PrimMonad m => m (Solver (PrimState m))
newSolver = stToPrim $ do
  defs     <- newMutVar (IntMap.empty, Map.empty)
  rep      <- Vec.new
  classes  <- Vec.new
  parent   <- newMutVar IntMap.empty
  useList  <- newMutVar IntMap.empty
  lookup   <- newMutVar IntMap.empty

  pending  <- Vec.new

  repE     <- Vec.new
  classesE <- Vec.new
  highE    <- Vec.new
  pendingE <- Vec.new

  trail <- Vec.new
  gen <- Vec.new
  Vec.push gen 0
  isAfterBT <- newMutVar False

  return $
    Solver
    { svDefs                = defs
    , svRepresentativeTable = rep
    , svClassList           = classes
    , svParent              = parent
    , svUseList             = useList
    , svLookupTable         = lookup

    -- workspace for constraint propagation
    , svPending = pending

    -- workspace for explanation generation
    , svERepresentativeTable = repE
    , svEClassList           = classesE
    , svEHighestNodeTable    = highE
    , svEPendingProofs       = pendingE

    -- for backtracking
    , svTrail = trail
    , svLevelGen = gen
    , svIsAfterBacktracking = isAfterBT
    }

getNFSyms :: PrimMonad m => Solver (PrimState m) -> m Int
getNFSyms solver = Vec.getSize (svRepresentativeTable solver)

newFSym :: PrimMonad m => Solver (PrimState m) -> m FSym
newFSym solver = stToPrim $ do
  v <- getNFSyms solver
  Vec.push (svRepresentativeTable solver) v
  Vec.push (svClassList solver) (ClassSingleton v)
  modifyMutVar' (svUseList solver) (IntMap.insert v [])
  Vec.push (svERepresentativeTable solver) v
  Vec.push (svEClassList solver) undefined
  Vec.push (svEHighestNodeTable solver) v
  return v

newFun :: (PrimMonad m, VAFun a) => Solver (PrimState m) -> m a
newFun solver = stToPrim $ do
  c <- newFSym solver
  return $ withVArgs (TApp c)

newConst :: PrimMonad m => Solver (PrimState m) -> m Term
newConst = newFun

merge :: PrimMonad m => Solver (PrimState m) -> Term -> Term -> m ()
merge solver t u = stToPrim $ merge' solver t u Nothing

merge' :: PrimMonad m => Solver (PrimState m) -> Term -> Term -> Maybe ConstrID -> m ()
merge' solver t u cid = stToPrim $ do
  t' <- termToFlatTerm solver t
  u' <- termToFlatTerm solver u
  case (t', u') of
    (FTConst c, _) -> mergeFlatTerm' solver u' c cid
    (_, FTConst c) -> mergeFlatTerm' solver t' c cid
    _ -> do
      c <- flatTermToFSym solver u'
      mergeFlatTerm' solver t' c cid

mergeFlatTerm :: PrimMonad m => Solver (PrimState m) -> FlatTerm -> FSym -> m ()
mergeFlatTerm solver s a = stToPrim $ mergeFlatTerm' solver s a Nothing

mergeFlatTerm' :: PrimMonad m => Solver (PrimState m) -> FlatTerm -> FSym -> Maybe ConstrID -> m ()
mergeFlatTerm' solver s a cid = stToPrim $ do
  initAfterBacktracking solver
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
          modifyMutVar' (svUseList solver) $
            IntMap.adjust ((eq1, lv, gen) :) a1' .
            IntMap.adjust ((eq1, lv, gen) :) a2'
          checkInvariant solver

propagate :: PrimMonad m => Solver (PrimState m) -> m ()
propagate solver = stToPrim $ go
  where
    go = do
      checkInvariant solver
      n <- Vec.getSize (svPending solver)
      unless (n == 0) $ do
        processEqn =<< Vec.unsafePop (svPending solver)
        go

    processEqn p = do
      let (a,b) = case p of
                    Left (Eqn0 _ a b) -> (a,b)
                    Right (Eqn1 _ _ _ a, Eqn1 _ _ _ b) -> (a,b)
      a' <- getRepresentative solver a
      b' <- getRepresentative solver b
      unless (a' == b') $ do
        classA <- Vec.unsafeRead (svClassList  solver) a'
        classB <- Vec.unsafeRead (svClassList  solver) b'
        (a,b,a',b',classA,classB) <- return $
          if classSize classA < classSize classB then
            (a,b,a',b',classA,classB)
          else
            (b,a,b',a',classB,classA)
        origRootA <- updateParent a b p
        update a' b' classA classB
        addToTrail solver (TrailMerge a' b' a origRootA)

    update a' b' classA classB = do
      classForM_ classA $ \c -> do
        Vec.unsafeWrite (svRepresentativeTable solver) c b'
      Vec.unsafeWrite (svClassList solver) b' (classA <> classB)

      lv <- getCurrentLevel solver
      lv_gen <- getLevelGen solver lv
      useList <- readMutVar (svUseList solver)
      useList_a' <- flip filterM (useList IntMap.! a') $ \(eq1@(Eqn1 _ c1 c2 _), lv2, lv2_gen2) -> do
        lv2_gen <- getLevelGen solver lv2
        if lv2 <= lv && lv2_gen2 == lv2_gen then do
          c1' <- getRepresentative solver c1
          c2' <- getRepresentative solver c2
          assert (b' == c1' || b' == c2') $ return ()
          -- unless (b' == c1' || b' == c2') $ error "ToySolver.EUF.CongruenceClosure.propagate.update: should not happen"
          ret <- lookup solver c1' c2'
          case ret of
            Just eq2 -> do
              addToPending solver $ Right (eq1, eq2)
            Nothing -> do
              setLookup solver c1' c2' eq1
              modifyMutVar (svUseList solver) $ IntMap.adjust ((eq1, lv, lv_gen) :) b'
              return ()
          return True
        else do
          -- out-of-date entry
          return False
      modifyMutVar' (svUseList solver) (IntMap.insert a' useList_a')

    -- Insert edge a→b labelled with a_eq_b into the proof forest, and re-orient its original ancestors.
    updateParent a b a_eq_b = do
      let loop d (c, c_eq_d) = do
            tbl <- readMutVar (svParent solver)
            writeMutVar (svParent solver) (IntMap.insert d (c, c_eq_d) tbl)
            case IntMap.lookup d tbl of
              Nothing -> return d
              Just (e, d_eq_e) -> loop e (d, d_eq_e)
      loop a (b, a_eq_b)

areCongruent :: PrimMonad m => Solver (PrimState m) -> Term -> Term -> m Bool
areCongruent solver t1 t2 = stToPrim $ do
  u1 <- termToFlatTerm solver t1
  u2 <- termToFlatTerm solver t2
  areCongruentFlatTerm solver u1 u2

areCongruentFlatTerm :: PrimMonad m => Solver (PrimState m) -> FlatTerm -> FlatTerm -> m Bool
areCongruentFlatTerm solver t1 t2 = stToPrim $ do
  initAfterBacktracking solver
  u1 <- normalize solver t1
  u2 <- normalize solver t2
  return $ u1 == u2

normalize :: PrimMonad m => Solver (PrimState m) -> FlatTerm -> m FlatTerm
normalize solver (FTConst c) = stToPrim $ liftM FTConst $ getRepresentative solver c
normalize solver (FTApp t1 t2) = stToPrim $ do
  u1 <- getRepresentative solver t1
  u2 <- getRepresentative solver t2
  ret <- lookup solver u1 u2
  case ret of
    Just (Eqn1 _ _ _ a) -> liftM FTConst $ getRepresentative solver a
    Nothing -> return $ FTApp u1 u2

checkInvariant :: PrimMonad m => Solver (PrimState m) -> m ()
checkInvariant _ | True = return ()
checkInvariant solver = stToPrim $ do
  nv <- getNFSyms solver

  representatives <- liftM IntSet.fromList $ Vec.getElems (svRepresentativeTable solver)

  ref <- newMutVar IntSet.empty
  forM_ (IntSet.toList representatives) $ \a' -> do
    bs <- Vec.read (svClassList solver) a'
    forM_ (classToList bs) $ \b -> do
      b' <- getRepresentative solver b
      unless (a' == b') $
        error "ToySolver.EUF.CongruenceClosure.checkInvariant: inconsistency between classList and representativeTable"
      modifyMutVar' ref (IntSet.insert b)

  xs <- readMutVar ref
  unless (xs == IntSet.fromList [0..nv-1]) $
    error "ToySolver.EUF.CongruenceClosure.checkInvariant: classList is not exhaustive"

  pendings <- Vec.getElems (svPending solver)
  forM_ pendings $ \p -> do
    case p of
      Left _ -> return ()
      Right (Eqn1 _ a1 a2 _, Eqn1 _ b1 b2 _) -> do
        a1' <- getRepresentative solver a1
        a2' <- getRepresentative solver a2
        b1' <- getRepresentative solver b1
        b2' <- getRepresentative solver b2
        unless (a1' == b1' && a2' == b2') $
          error "ToySolver.EUF.CongruenceClosure.checkInvariant: error in pendingList"

  useList <- readMutVar (svUseList solver)
  lv <- getCurrentLevel solver
  forM_ (IntSet.toList representatives) $ \a -> do
    forM_ (useList IntMap.! a) $ \(Eqn1 _ b1 b2 _, lv2, lv2_gen2) -> do
      lv2_gen <- getLevelGen solver lv2
      when (lv2 <= lv && lv2_gen2 == lv2_gen) $ do
        b1' <- getRepresentative solver b1
        b2' <- getRepresentative solver b2
        unless (a == b1' || a == b2') $
          error "ToySolver.EUF.CongruenceClosure.checkInvariant: error in useList"

  forM_ (IntSet.toList representatives) $ \b -> do
    forM_ (IntSet.toList representatives) $ \c -> do
      m <- lookup solver b c
      case m of
        Nothing -> return ()
        Just (Eqn1 _ a1 a2 _) -> do
          a1' <- getRepresentative solver a1
          a2' <- getRepresentative solver a2
          unless (b == a1' && c == a2') $
            error "ToySolver.EUF.CongruenceClosure.checkInvariant: error in lookupTable"

-- -------------------------------------------------------------------
-- Explanation
-- -------------------------------------------------------------------

explain :: PrimMonad m => Solver (PrimState m) -> Term -> Term -> m (Maybe IntSet)
explain solver t1 t2 = stToPrim $ do
  c1 <- termToFlatTerm solver t1
  c2 <- termToFlatTerm solver t2
  explainFlatTerm solver c1 c2

explainFlatTerm :: PrimMonad m => Solver (PrimState m) -> FlatTerm -> FlatTerm -> m (Maybe IntSet)
explainFlatTerm solver t1 t2 = stToPrim $ do
  c1 <- flatTermToFSym solver t1
  c2 <- flatTermToFSym solver t2
  explainConst solver c1 c2

explainConst :: forall m. PrimMonad m => Solver (PrimState m) -> FSym -> FSym -> m (Maybe IntSet)
explainConst solver c1 c2 = stToPrim $ do
  initAfterBacktracking solver
  n <- getNFSyms solver

  -- Additional union-find data structure
  forLoop 0 (<n) (+1) $ \a -> do
    Vec.unsafeWrite (svERepresentativeTable solver) a a
    Vec.unsafeWrite (svEClassList solver) a (ClassSingleton a)
    Vec.unsafeWrite (svEHighestNodeTable solver) a a

  let union :: FSym -> FSym -> ST (PrimState m) ()
      union a b = do
        a' <- getERepresentative solver a
        b' <- getERepresentative solver b
        classA <- Vec.unsafeRead (svEClassList solver) a'
        classB <- Vec.unsafeRead (svEClassList solver) b'
        h <- getHighestNode solver b'
        (b'', classA, classB) <-
          if classSize classA < classSize classB then do
            return (b', classA, classB)
          else
            return (a', classB, classA)
        classForM_ classA $ \c -> do
          Vec.unsafeWrite (svERepresentativeTable solver) c b''
        Vec.unsafeWrite (svEClassList solver) b'' (classA <> classB)
        Vec.unsafeWrite (svEHighestNodeTable solver) b'' h

  Vec.clear (svEPendingProofs solver)
  Vec.push (svEPendingProofs solver) (c1,c2)
  result <- newMutVar IntSet.empty

  let loop = do
        n <- Vec.getSize (svEPendingProofs solver)
        if n == 0 then
          return True
        else do
          (a,b) <- Vec.unsafePop (svEPendingProofs solver)
          m <- nearestCommonAncestor solver a b
          case m of
            Nothing -> return False
            Just c -> do
              explainAlongPath a c
              explainAlongPath b c
              loop

      explainAlongPath :: FSym -> FSym -> ST (PrimState m) ()
      explainAlongPath a c = do
        a <- getHighestNode solver a
        -- note that c is already @getHighestNode solver c@
        let loop a =
              unless (a == c) $ do
                ret <- getParent solver a
                case ret of
                  Nothing -> error "should not happen"
                  Just (b, eq) -> do
                    case eq of
                      Left (Eqn0 cid _ _) -> do
                        modifyMutVar' result (maybeToIntSet cid <>)
                      Right (Eqn1 cid1 a1 a2 _, Eqn1 cid2 b1 b2 _) -> do
                        modifyMutVar' result ((maybeToIntSet cid1 <> maybeToIntSet cid2) <>)
                        Vec.push (svEPendingProofs solver) (a1,b1)
                        Vec.push (svEPendingProofs solver) (a2,b2)
                    union a b
                    loop =<< getHighestNode solver b
        loop a

  b <- loop
  if b
  then liftM Just $ readMutVar result
  else return Nothing

-- -------------------------------------------------------------------
-- Model construction
-- -------------------------------------------------------------------

type Entity = Int
type EntityTuple = [Entity]

data Model
  = Model
  { mUniverse    :: !IntSet
  , mFunctions   :: !(IntMap (Map EntityTuple Entity))
  , mUnspecified :: !Entity
  , mEquivClasses :: [(Set Term, Entity)]
  }
  deriving (Show)

getModel :: PrimMonad m => Solver (PrimState m) -> m Model
getModel solver = stToPrim $ do
  n <- Vec.getSize (svRepresentativeTable solver)
  univRef <- newMutVar IntSet.empty
  reprRef <- newMutVar IntMap.empty
  forM_ [0..n-1] $ \a -> do
    a' <- Vec.unsafeRead (svRepresentativeTable solver) a
    when (a == a') $ modifyMutVar' univRef (IntSet.insert a)
    modifyMutVar' reprRef (IntMap.insert a a')
  -- univ <- readMutVar univRef
  repr <- readMutVar reprRef

  lookups <- readMutVar (svLookupTable solver)
  -- (defs1,_) <- readMutVar (svDefs solver)

  let -- "(b,c) ∈ appRel[a]" means f(b,c)=a
      appRel :: IntMap (Set (FSym, FSym))
      appRel = IntMap.fromListWith Set.union $
        [ (repr IntMap.! c, Set.singleton (repr IntMap.! a, repr IntMap.! b))
        | (a,m) <- IntMap.toList lookups, (b, Eqn1 _ _ _ c) <- IntMap.toList m
        ]

      partialApps :: IntSet
      partialApps = IntSet.fromList [b | xs <- IntMap.elems appRel, (b,_) <- Set.toList xs]

      xs1 :: IntMap (Map EntityTuple Entity)
      xs1 = IntMap.fromListWith Map.union $
              [ (f, Map.singleton (reverse argsRev) (repr IntMap.! a))
              | a <- IntMap.keys (IntMap.withoutKeys appRel partialApps)
              , (f, argsRev) <- expand a
              ]
        where
          expand :: FSym -> [(FSym, [FSym])]
          expand a =
            case IntMap.lookup a appRel of
              Nothing -> return (repr IntMap.! a, [])
              Just xs -> do
                (c,d) <- Set.toList xs
                (f,xs) <- expand c
                return (f, repr IntMap.! d : xs)

      xs2 :: IntMap (Map EntityTuple Entity)
      xs2 = fmap (Map.singleton []) (repr `IntMap.difference` xs1)

      funcs :: IntMap (Map EntityTuple Entity)
      funcs = IntMap.unionWith Map.union xs1 xs2

      used :: IntSet
      used = IntSet.unions [IntSet.fromList (y : xs) | m <- IntMap.elems funcs, (xs,y) <- Map.toList m]

  classes <- forM (IntSet.toList used) $ \a -> do
    classA <- Vec.unsafeRead (svClassList  solver) a
    classA' <- liftM Set.fromList $ mapM (fsymToTerm solver) (classToList classA)
    return (classA', a)

  -- renaming
  let univ2 :: IntSet
      univ2 = IntSet.insert (-1) $ IntSet.fromList [0 .. IntSet.size used - 1]

      to_univ2' :: IntMap Entity
      to_univ2' = IntMap.fromList (zip (IntSet.toList used) [0..])

      to_univ2 :: FSym -> Entity
      to_univ2 = (to_univ2' IntMap.!)

      funcs2 :: IntMap (Map EntityTuple Entity)
      funcs2 = fmap (\m -> Map.fromList [(map to_univ2 xs, to_univ2 y) | (xs,y) <- Map.toList m]) funcs

      classes2 :: [(Set Term, Entity)]
      classes2 = [(classA, to_univ2 a) | (classA,a) <- classes]

  return $
    Model
    { mUniverse    = univ2
    , mFunctions   = funcs2
    , mUnspecified = -1
    , mEquivClasses = classes2
    }

eval :: Model -> Term -> Entity
eval m (TApp f xs) = evalAp m f (map (eval m) xs)

evalAp :: Model -> FSym -> [Entity] -> Entity
evalAp m f xs =
  case IntMap.lookup f (mFunctions m) of
    Nothing -> mUnspecified m
    Just fdef ->
      case Map.lookup xs fdef of
        Nothing -> mUnspecified m
        Just e -> e

-- -------------------------------------------------------------------
-- Backtracking
-- -------------------------------------------------------------------

type Level = Int
type Gen = Int

data TrailItem
  = TrailMerge !FSym !FSym !FSym !FSym
  | TrailSetLookup !FSym !FSym
  deriving (Show)

addToTrail :: PrimMonad m => Solver (PrimState m) -> TrailItem -> m ()
addToTrail solver item = stToPrim $ do
  lv <- getCurrentLevel solver
  when (lv /= 0) $ do
    seq item $ Vec.unsafeModify (svTrail solver) (lv - 1) (item :)

getCurrentLevel :: PrimMonad m => Solver (PrimState m) -> m Level
getCurrentLevel solver = Vec.getSize (svTrail solver)

getLevelGen :: PrimMonad m => Solver (PrimState m) -> Level -> m Gen
getLevelGen solver lv = Vec.unsafeRead (svLevelGen solver) lv

pushBacktrackPoint :: PrimMonad m => Solver (PrimState m) -> m ()
pushBacktrackPoint solver = stToPrim $ do
  Vec.push (svTrail solver) []
  lv <- getCurrentLevel solver
  size <- Vec.getSize (svLevelGen solver)
  if lv < size then do
    g <- Vec.unsafeRead (svLevelGen solver) lv
    Vec.unsafeWrite (svLevelGen solver) lv (g + 1)
  else
    Vec.push (svLevelGen solver) 0

popBacktrackPoint :: PrimMonad m => Solver (PrimState m) -> m ()
popBacktrackPoint solver = stToPrim $ do
  writeMutVar (svIsAfterBacktracking solver) True
  xs <- Vec.unsafePop (svTrail solver)
  forM_ xs $ \item -> do
    case item of
      TrailSetLookup a' b' -> do
        modifyMutVar' (svLookupTable solver) (IntMap.adjust (IntMap.delete b') a')
      TrailMerge a' b' a origRootA -> do
        -- Revert changes to Union-Find data strucutres
        ret <- Vec.unsafeRead (svClassList solver) b'
        case ret of
          ClassSingleton _ -> error "should not happen"
          ClassUnion _ origClassA origClassB -> do
            classForM_ origClassA $ \c -> do
              Vec.unsafeWrite (svRepresentativeTable solver) c a'
            Vec.unsafeWrite (svClassList solver) b' origClassB

        -- Revert changes to proof-forest data strucutres
        let loop c p = do
              tbl <- readMutVar (svParent solver)
              writeMutVar (svParent solver) (IntMap.update (const p) c tbl)
              unless (c == a) $ do
                let (d, c_eq_d) = tbl IntMap.! c
                loop d (Just (c, c_eq_d))
        loop origRootA Nothing

initAfterBacktracking :: PrimMonad m => Solver (PrimState m) -> m ()
initAfterBacktracking solver = stToPrim $ do
  b <- readMutVar (svIsAfterBacktracking solver)
  when b $ do
    writeMutVar (svIsAfterBacktracking solver) False
    (defs, _) <- readMutVar (svDefs solver)
    forM_ (IntMap.toList defs) $ \(a,(a1,a2)) -> do
      mergeFlatTerm solver (FTApp a1 a2) a

{--------------------------------------------------------------------
  Helper funcions
--------------------------------------------------------------------}

lookup :: Solver s -> FSym -> FSym -> ST s (Maybe Eqn1)
lookup solver c1 c2 = do
  tbl <- readMutVar $ svLookupTable solver
  return $ do
     m <- IntMap.lookup c1 tbl
     IntMap.lookup c2 m

setLookup :: Solver s -> FSym -> FSym -> Eqn1 -> ST s ()
setLookup solver a1 a2 eqn = do
  modifyMutVar' (svLookupTable solver) $
    IntMap.insertWith IntMap.union a1 (IntMap.singleton a2 eqn)
  addToTrail solver (TrailSetLookup a1 a2)

addToPending :: Solver s -> Eqn -> ST s ()
addToPending solver eqn = Vec.push (svPending solver) eqn

getRepresentative :: Solver s -> FSym -> ST s FSym
getRepresentative solver c = Vec.unsafeRead (svRepresentativeTable solver) c

getParent :: Solver s -> FSym -> ST s (Maybe (FSym, Eqn))
getParent solver c = do
  m <- readMutVar $ svParent solver
  return $ IntMap.lookup c m

getERepresentative :: Solver s -> FSym -> ST s FSym
getERepresentative solver a = Vec.unsafeRead (svERepresentativeTable solver) a

getHighestNode :: Solver s -> FSym -> ST s FSym
getHighestNode solver c = stToPrim $ do
  d <- getERepresentative solver c
  Vec.unsafeRead (svEHighestNodeTable solver) d

nearestCommonAncestor :: Solver s -> FSym -> FSym -> ST s (Maybe FSym)
nearestCommonAncestor solver a b = do
  let loop c !ret = do
        m <- getParent solver c
        case m of
          Nothing -> return ret
          Just (d,_) -> loop d (IntSet.insert d ret)
  a_ancestors <- loop a (IntSet.singleton a)

  let loop2 c = do
        if c `IntSet.member` a_ancestors then
          liftM Just $ getHighestNode solver c
        else do
          m <- getParent solver c
          case m of
            Nothing -> return Nothing
            Just (d,_) -> loop2 d
  loop2 b

termToFlatTerm :: PrimMonad m => Solver (PrimState m) -> Term -> m FlatTerm
termToFlatTerm solver (TApp f xs) = stToPrim $ do
  xs' <- mapM (termToFlatTerm solver) xs
  let phi t u = do
        t' <- flatTermToFSym solver t
        u' <- flatTermToFSym solver u
        return $ FTApp t' u'
  foldM phi (FTConst f) xs'

flatTermToFSym :: PrimMonad m => Solver (PrimState m) -> FlatTerm -> m FSym
flatTermToFSym _ (FTConst c) = return c
flatTermToFSym solver (FTApp c d) = stToPrim $ do
  (defs1,defs2) <- readMutVar $ svDefs solver
  a <- case Map.lookup (c,d) defs2 of
         Just a -> return a
         Nothing -> do
           a <- newFSym solver
           writeMutVar (svDefs solver) (IntMap.insert a (c,d) defs1, Map.insert (c,d) a defs2)
           mergeFlatTerm solver (FTApp c d) a
           return a
  return a

fsymToFlatTerm :: PrimMonad m => Solver (PrimState m) -> FSym -> m FlatTerm
fsymToFlatTerm solver a = stToPrim $ do
  (defs1,_) <- readMutVar $ svDefs solver
  case IntMap.lookup a defs1 of
    Just (c,d) -> return (FTApp c d)
    Nothing -> return (FTConst a)

termToFSym :: PrimMonad m => Solver (PrimState m) -> Term -> m FSym
termToFSym solver t = stToPrim $ flatTermToFSym solver =<< termToFlatTerm solver t

fsymToTerm :: PrimMonad m => Solver (PrimState m) -> FSym -> m Term
fsymToTerm solver a = stToPrim $ do
  (defs1,_) <- readMutVar $ svDefs solver
  let convert :: FSym -> Term
      convert a =
        case convert' a of
          (f, xs) -> TApp f (reverse xs)
      convert' :: FSym -> (FSym, [Term])
      convert' a =
        case IntMap.lookup a defs1 of
          Nothing -> (a, [])
          Just (c,d) ->
            case convert' c of
              (f,xs) -> (f, convert d : xs)
  return (convert a)

maybeToIntSet :: Maybe Int -> IntSet
maybeToIntSet Nothing  = IntSet.empty
maybeToIntSet (Just x) = IntSet.singleton x
