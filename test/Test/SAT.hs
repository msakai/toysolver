{-# LANGUAGE CPP #-}
{-# LANGUAGE TemplateHaskell, ScopedTypeVariables, FlexibleContexts #-}
module Test.SAT (satTestGroup) where

import Control.Applicative
import Control.Monad
import Data.Array.IArray
import Data.Default.Class
import qualified Data.Foldable as F
import Data.IORef
import Data.List
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe
import Data.Set (Set)
import qualified Data.Set as Set
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import qualified Data.Traversable as Traversable
import qualified Data.Vector as V
import qualified System.Random.MWC as Rand

import Test.Tasty
import Test.Tasty.QuickCheck hiding ((.&&.), (.||.))
import Test.Tasty.HUnit
import Test.Tasty.TH
import qualified Test.QuickCheck.Monadic as QM

import ToySolver.Data.LBool
import ToySolver.Data.BoolExpr
import ToySolver.Data.Boolean
import qualified ToySolver.SAT as SAT
import qualified ToySolver.SAT.Types as SAT
import ToySolver.SAT.TheorySolver
import qualified ToySolver.SAT.Encoder.Tseitin as Tseitin
import qualified ToySolver.SAT.Encoder.PB as PB
import qualified ToySolver.SAT.Encoder.PB.Internal.Sorter as PBEncSorter
import qualified ToySolver.SAT.Encoder.PBNLC as PBNLC
import qualified ToySolver.SAT.MUS as MUS
import qualified ToySolver.SAT.MUS.Enum as MUSEnum
import qualified ToySolver.SAT.PBO as PBO
import qualified ToySolver.SAT.Store.CNF as CNFStore
import qualified ToySolver.SAT.ExistentialQuantification as ExistentialQuantification

import qualified Data.PseudoBoolean as PBFile
import qualified ToySolver.Converter.PB2SAT as PB2SAT
import qualified ToySolver.Converter.WBO2MaxSAT as WBO2MaxSAT
import qualified ToySolver.Converter.WBO2PB as WBO2PB
import qualified ToySolver.Converter.SAT2KSAT as SAT2KSAT
import qualified ToySolver.Text.CNF as CNF
import qualified ToySolver.Text.MaxSAT as MaxSAT

import ToySolver.Data.OrdRel
import qualified ToySolver.Data.LA as LA
import qualified ToySolver.Arith.Simplex as Simplex
import qualified ToySolver.EUF.EUFSolver as EUF

allAssignments :: Int -> [SAT.Model]
allAssignments nv = [array (1,nv) (zip [1..nv] xs) | xs <- replicateM nv [True,False]]

prop_solveCNF :: Property
prop_solveCNF = QM.monadicIO $ do
  cnf <- QM.pick arbitraryCNF
  solver <- arbitrarySolver
  ret <- QM.run $ solveCNF solver cnf
  case ret of
    Just m -> QM.assert $ evalCNF m cnf
    Nothing -> do
      forM_ (allAssignments (CNF.numVars cnf)) $ \m -> do
        QM.assert $ not (evalCNF m cnf)

solveCNF :: SAT.Solver -> CNF.CNF -> IO (Maybe SAT.Model)
solveCNF solver cnf = do
  SAT.newVars_ solver (CNF.numVars cnf)
  forM_ (CNF.clauses cnf) $ \c -> SAT.addClause solver (SAT.unpackClause c)
  ret <- SAT.solve solver
  if ret then do
    m <- SAT.getModel solver
    return (Just m)
  else do
    return Nothing

arbitraryCNF :: Gen CNF.CNF
arbitraryCNF = do
  nv <- choose (0,10)
  nc <- choose (0,50)
  cs <- replicateM nc $ do
    len <- choose (0,10)
    if nv == 0 then
      return $ SAT.packClause []
    else
      SAT.packClause <$> (replicateM len $ choose (-nv, nv) `suchThat` (/= 0))
  return $
    CNF.CNF
    { CNF.numVars = nv
    , CNF.numClauses = nc
    , CNF.clauses = cs
    }

evalCNF :: SAT.Model -> CNF.CNF -> Bool
evalCNF m cnf = all (SAT.evalClause m . SAT.unpackClause) (CNF.clauses cnf)


prop_solvePB :: Property
prop_solvePB = QM.monadicIO $ do
  prob@(nv,_) <- QM.pick arbitraryPB
  solver <- arbitrarySolver
  ret <- QM.run $ solvePB solver prob
  case ret of
    Just m -> QM.assert $ evalPB m prob
    Nothing -> do
      forM_ (allAssignments nv) $ \m -> do
        QM.assert $ not (evalPB m prob)

data PBRel = PBRelGE | PBRelEQ | PBRelLE deriving (Eq, Ord, Enum, Bounded, Show)

instance Arbitrary PBRel where
  arbitrary = arbitraryBoundedEnum  

evalPBRel :: Ord a => PBRel -> a -> a -> Bool
evalPBRel PBRelGE = (>=)
evalPBRel PBRelLE = (<=)
evalPBRel PBRelEQ = (==)

solvePB :: SAT.Solver -> (Int,[(PBRel,SAT.PBLinSum,Integer)]) -> IO (Maybe SAT.Model)
solvePB solver (nv,cs) = do
  SAT.newVars_ solver nv
  forM_ cs $ \(o,lhs,rhs) -> do
    case o of
      PBRelGE -> SAT.addPBAtLeast solver lhs rhs
      PBRelLE -> SAT.addPBAtMost solver lhs rhs
      PBRelEQ -> SAT.addPBExactly solver lhs rhs
  ret <- SAT.solve solver
  if ret then do
    m <- SAT.getModel solver
    return (Just m)
  else do
    return Nothing

arbitraryPB :: Gen (Int,[(PBRel,SAT.PBLinSum,Integer)])
arbitraryPB = do
  nv <- choose (0,10)
  nc <- choose (0,50)
  cs <- replicateM nc $ do
    rel <- arbitrary
    lhs <- arbitraryPBLinSum nv
    rhs <- arbitrary
    return $ (rel,lhs,rhs)
  return (nv, cs)

arbitraryPBLinSum :: Int -> Gen SAT.PBLinSum
arbitraryPBLinSum nv = do
  len <- choose (0,10)
  if nv == 0 then
    return []
  else
    replicateM len $ do
      l <- choose (-nv, nv) `suchThat` (/= 0)
      c <- arbitrary
      return (c,l)

evalPB :: SAT.Model -> (Int,[(PBRel,SAT.PBLinSum,Integer)]) -> Bool
evalPB m (_,cs) = all (\(o,lhs,rhs) -> evalPBRel o (SAT.evalPBLinSum m lhs) rhs) cs

prop_optimizePBO :: Property
prop_optimizePBO = QM.monadicIO $ do
  prob@(nv,_) <- QM.pick arbitraryPB
  obj <- QM.pick $ arbitraryPBLinSum nv
  solver <- arbitrarySolver
  opt <- arbitraryOptimizer solver obj
  ret <- QM.run $ optimizePBO solver opt prob
  case ret of
    Just (m, v) -> do
      QM.assert $ evalPB m prob
      QM.assert $ SAT.evalPBLinSum m obj == v
      forM_ (allAssignments nv) $ \m2 -> do
        QM.assert $ not (evalPB m2 prob) || SAT.evalPBLinSum m obj <= SAT.evalPBLinSum m2 obj
    Nothing -> do
      forM_ (allAssignments nv) $ \m -> do
        QM.assert $ not (evalPB m prob)
           
optimizePBO :: SAT.Solver -> PBO.Optimizer -> (Int,[(PBRel,SAT.PBLinSum,Integer)]) -> IO (Maybe (SAT.Model, Integer))
optimizePBO solver opt (nv,cs) = do
  SAT.newVars_ solver nv
  forM_ cs $ \(o,lhs,rhs) -> do
    case o of
      PBRelGE -> SAT.addPBAtLeast solver lhs rhs
      PBRelLE -> SAT.addPBAtMost solver lhs rhs
      PBRelEQ -> SAT.addPBExactly solver lhs rhs
  PBO.optimize opt
  PBO.getBestSolution opt

evalWBO :: SAT.Model -> (Int, [(Maybe Integer, (PBRel,SAT.PBLinSum,Integer))], Maybe Integer) -> Maybe Integer
evalWBO m (nv,cs,top) = do
  cost <- liftM sum $ forM cs $ \(w,(o,lhs,rhs)) -> do
    if evalPBRel o (SAT.evalPBLinSum m lhs) rhs then
      return 0
    else
      w
  case top of
    Just t -> guard (cost < t)
    Nothing -> return ()
  return cost

arbitraryWBO :: Gen (Int, [(Maybe Integer, (PBRel,SAT.PBLinSum,Integer))], Maybe Integer)
arbitraryWBO = do
  (nv,cs) <- arbitraryPB
  cs2 <- forM cs $ \c -> do
    b <- arbitrary
    cost <- if b then return Nothing
            else liftM (Just . (1+) . abs) arbitrary
    return (cost, c)
  b <- arbitrary
  top <- if b then return Nothing
         else liftM (Just . (1+) . abs) arbitrary
  return (nv,cs2,top)

optimizeWBO
  :: SAT.Solver
  -> PBO.Method
  -> (Int, [(Maybe Integer, (PBRel,SAT.PBLinSum,Integer))], Maybe Integer)
  -> IO (Maybe (SAT.Model, Integer))
optimizeWBO solver method (nv,cs,top) = do
  SAT.newVars_ solver nv
  obj <- liftM catMaybes $ forM cs $ \(cost, (o,lhs,rhs)) -> do
    case cost of
      Nothing -> do
        case o of
          PBRelGE -> SAT.addPBAtLeast solver lhs rhs
          PBRelLE -> SAT.addPBAtMost solver lhs rhs
          PBRelEQ -> SAT.addPBExactly solver lhs rhs
        return Nothing
      Just w -> do
        sel <- SAT.newVar solver
        case o of
          PBRelGE -> SAT.addPBAtLeastSoft solver sel lhs rhs
          PBRelLE -> SAT.addPBAtMostSoft solver sel lhs rhs
          PBRelEQ -> SAT.addPBExactlySoft solver sel lhs rhs
        return $ Just (w,-sel)
  case top of
    Nothing -> return ()
    Just c -> SAT.addPBAtMost solver obj (c-1)
  opt <- PBO.newOptimizer solver obj
  PBO.optimize opt
  liftM (fmap (\(m, val) -> (SAT.restrictModel nv m, val))) $ PBO.getBestSolution opt

prop_solvePBNLC :: Property
prop_solvePBNLC = QM.monadicIO $ do
  prob@(nv,_) <- QM.pick arbitraryPBNLC
  solver <- arbitrarySolver
  ret <- QM.run $ solvePBNLC solver prob
  case ret of
    Just m -> QM.assert $ evalPBNLC m prob
    Nothing -> do
      forM_ (allAssignments nv) $ \m -> do
        QM.assert $ not (evalPBNLC m prob)

solvePBNLC :: SAT.Solver -> (Int,[(PBRel,SAT.PBSum,Integer)]) -> IO (Maybe SAT.Model)
solvePBNLC solver (nv,cs) = do
  SAT.newVars_ solver nv
  enc <- PBNLC.newEncoder solver =<< Tseitin.newEncoder solver
  forM_ cs $ \(o,lhs,rhs) -> do
    case o of
      PBRelGE -> PBNLC.addPBNLAtLeast enc lhs rhs
      PBRelLE -> PBNLC.addPBNLAtMost enc lhs rhs
      PBRelEQ -> PBNLC.addPBNLExactly enc lhs rhs
  ret <- SAT.solve solver
  if ret then do
    m <- SAT.getModel solver
    return $ Just $ SAT.restrictModel nv m
  else do
    return Nothing

optimizePBNLC
  :: SAT.Solver
  -> PBO.Method
  -> (Int, SAT.PBSum, [(PBRel,SAT.PBSum,Integer)])
  -> IO (Maybe (SAT.Model, Integer))
optimizePBNLC solver method (nv,obj,cs) = do
  SAT.newVars_ solver nv
  enc <- PBNLC.newEncoder solver =<< Tseitin.newEncoder solver
  forM_ cs $ \(o,lhs,rhs) -> do
    case o of
      PBRelGE -> PBNLC.addPBNLAtLeast enc lhs rhs
      PBRelLE -> PBNLC.addPBNLAtMost enc lhs rhs
      PBRelEQ -> PBNLC.addPBNLExactly enc lhs rhs
  obj2 <- PBNLC.linearizePBSumWithPolarity enc Tseitin.polarityNeg obj
  opt <- PBO.newOptimizer2 solver obj2 (\m -> SAT.evalPBSum m obj)
  PBO.setMethod opt method
  PBO.optimize opt
  liftM (fmap (\(m, val) -> (SAT.restrictModel nv m, val))) $ PBO.getBestSolution opt

arbitraryPBNLC :: Gen (Int,[(PBRel,SAT.PBSum,Integer)])
arbitraryPBNLC = do
  nv <- choose (0,10)
  nc <- choose (0,50)
  cs <- replicateM nc $ do
    rel <- arbitrary
    len <- choose (0,10)
    lhs <-
      if nv == 0 then
        return []
      else
        replicateM len $ do
          ls <- listOf $ choose (-nv, nv) `suchThat` (/= 0)
          c <- arbitrary
          return (c,ls)
    rhs <- arbitrary
    return $ (rel,lhs,rhs)
  return (nv, cs)

evalPBNLC :: SAT.Model -> (Int,[(PBRel,SAT.PBSum,Integer)]) -> Bool
evalPBNLC m (_,cs) = all (\(o,lhs,rhs) -> evalPBRel o (SAT.evalPBSum m lhs) rhs) cs


prop_solveXOR :: Property
prop_solveXOR = QM.monadicIO $ do
  prob@(nv,_) <- QM.pick arbitraryXOR
  solver <- arbitrarySolver
  ret <- QM.run $ solveXOR solver prob
  case ret of
    Just m -> QM.assert $ evalXOR m prob
    Nothing -> do
      forM_ (allAssignments nv) $ \m -> do
        QM.assert $ not (evalXOR m prob)

solveXOR :: SAT.Solver -> (Int,[SAT.XORClause]) -> IO (Maybe SAT.Model)
solveXOR solver (nv,cs) = do
  SAT.modifyConfig solver $ \config -> config{ SAT.configCheckModel = True }
  SAT.newVars_ solver nv
  forM_ cs $ \c -> SAT.addXORClause solver (fst c) (snd c)
  ret <- SAT.solve solver
  if ret then do
    m <- SAT.getModel solver
    return (Just m)
  else do
    return Nothing

arbitraryXOR :: Gen (Int,[SAT.XORClause])
arbitraryXOR = do
  nv <- choose (0,10)
  nc <- choose (0,50)
  cs <- replicateM nc $ do
    len <- choose (0,10)    
    lhs <-
      if nv == 0 then
        return []
      else
        replicateM len $ choose (-nv, nv) `suchThat` (/= 0)
    rhs <- arbitrary
    return (lhs,rhs)
  return (nv, cs)

evalXOR :: SAT.Model -> (Int,[SAT.XORClause]) -> Bool
evalXOR m (_,cs) = all (SAT.evalXORClause m) cs


newTheorySolver :: CNF.CNF -> IO TheorySolver
newTheorySolver cnf = do
  let nv = CNF.numVars cnf
      cs = CNF.clauses cnf
  solver <- SAT.newSolver
  SAT.newVars_ solver nv
  forM_ cs $ \c -> SAT.addClause solver (SAT.unpackClause c)
  
  ref <- newIORef []
  let tsolver =
        TheorySolver
        { thAssertLit = \_ l -> do
            if abs l > nv then
              return True
            else do
              m <- readIORef ref
              case m of
                [] -> SAT.addClause solver [l]
                xs : xss -> writeIORef ref ((l : xs) : xss)
              return True
        , thCheck = \_ -> do
            xs <- liftM concat $ readIORef ref
            SAT.solveWith solver xs
        , thExplain = \m -> do
            case m of
              Nothing -> SAT.getFailedAssumptions solver
              Just _ -> return []
        , thPushBacktrackPoint = modifyIORef ref ([] :)
        , thPopBacktrackPoint = modifyIORef ref tail
        , thConstructModel = return ()
        }
  return tsolver

prop_solveCNF_using_BooleanTheory :: Property
prop_solveCNF_using_BooleanTheory = QM.monadicIO $ do
  cnf <- QM.pick arbitraryCNF
  let nv = CNF.numVars cnf
      nc = CNF.numClauses cnf
      cs = CNF.clauses cnf
      cnf1 = cnf{ CNF.clauses = [c | (i,c) <- zip [0..] cs, i `mod` 2 == 0], CNF.numClauses = nc - (nc `div` 2) }
      cnf2 = cnf{ CNF.clauses = [c | (i,c) <- zip [0..] cs, i `mod` 2 /= 0], CNF.numClauses = nc `div` 2 }

  solver <- arbitrarySolver

  ret <- QM.run $ do
    SAT.newVars_ solver nv

    tsolver <- newTheorySolver cnf1
    SAT.setTheory solver tsolver

    forM_ (CNF.clauses cnf2) $ \c -> SAT.addClause solver (SAT.unpackClause c)
    ret <- SAT.solve solver
    if ret then do
      m <- SAT.getModel solver
      return (Just m)
    else do
      return Nothing

  case ret of
    Just m -> QM.assert $ evalCNF m cnf
    Nothing -> do
      forM_ (allAssignments nv) $ \m -> do
        QM.assert $ not (evalCNF m cnf)

case_QF_LRA :: Assertion
case_QF_LRA = do
  satSolver <- SAT.newSolver
  lraSolver <- Simplex.newSolver

  tblRef <- newIORef $ Map.empty
  defsRef <- newIORef $ IntMap.empty
  let abstractLAAtom :: LA.Atom Rational -> IO SAT.Lit
      abstractLAAtom atom = do
        (v,op,rhs) <- Simplex.simplifyAtom lraSolver atom
        tbl <- readIORef tblRef
        (vLt, vEq, vGt) <-
          case Map.lookup (v,rhs) tbl of
            Just (vLt, vEq, vGt) -> return (vLt, vEq, vGt)
            Nothing -> do
              vLt <- SAT.newVar satSolver
              vEq <- SAT.newVar satSolver
              vGt <- SAT.newVar satSolver
              SAT.addClause satSolver [vLt,vEq,vGt]
              SAT.addClause satSolver [-vLt, -vEq]
              SAT.addClause satSolver [-vLt, -vGt]                 
              SAT.addClause satSolver [-vEq, -vGt]
              writeIORef tblRef (Map.insert (v,rhs) (vLt, vEq, vGt) tbl)
              let xs = IntMap.fromList
                       [ (vEq,  LA.var v .==. LA.constant rhs)
                       , (vLt,  LA.var v .<.  LA.constant rhs)
                       , (vGt,  LA.var v .>.  LA.constant rhs)
                       , (-vLt, LA.var v .>=. LA.constant rhs)
                       , (-vGt, LA.var v .<=. LA.constant rhs)
                       ]
              modifyIORef defsRef (IntMap.union xs)
              return (vLt, vEq, vGt)
        case op of
          Lt  -> return vLt
          Gt  -> return vGt
          Eql -> return vEq
          Le  -> return (-vGt)
          Ge  -> return (-vLt)
          NEq -> return (-vEq)

      abstract :: BoolExpr (Either SAT.Lit (LA.Atom Rational)) -> IO (BoolExpr SAT.Lit)
      abstract = Traversable.mapM f
        where
          f (Left lit) = return lit
          f (Right atom) = abstractLAAtom atom

  let tsolver =
        TheorySolver
        { thAssertLit = \_ l -> do
            defs <- readIORef defsRef
            case IntMap.lookup l defs of
              Nothing -> return True
              Just atom -> do
                Simplex.assertAtomEx' lraSolver atom (Just l)
                return True
        , thCheck = \_ -> do
            Simplex.check lraSolver
        , thExplain = \m -> do
            case m of
              Nothing -> liftM IntSet.toList $ Simplex.explain lraSolver
              Just _ -> return []
        , thPushBacktrackPoint = do
            Simplex.pushBacktrackPoint lraSolver
        , thPopBacktrackPoint = do
            Simplex.popBacktrackPoint lraSolver
        , thConstructModel = do
            return ()
        }
  SAT.setTheory satSolver tsolver

  enc <- Tseitin.newEncoder satSolver
  let addFormula :: BoolExpr (Either SAT.Lit (LA.Atom Rational)) -> IO ()
      addFormula c = Tseitin.addFormula enc =<< abstract c

  a <- SAT.newVar satSolver
  x <- Simplex.newVar lraSolver
  y <- Simplex.newVar lraSolver

  let le1 = LA.fromTerms [(2,x), (1/3,y)] .<=. LA.constant (-4) -- 2 x + (1/3) y <= -4
      eq2 = LA.fromTerms [(1.5,x)] .==. LA.fromTerms [(-2,x)] -- 1.5 y = -2 x
      gt3 = LA.var x .>. LA.var y -- x > y
      lt4 = LA.fromTerms [(3,x)] .<. LA.fromTerms [(-1,LA.unitVar), (1/5,x), (1/5,y)] -- 3 x < -1 + (1/5) (x + y)

      c1, c2 :: BoolExpr (Either SAT.Lit (LA.Atom Rational))
      c1 = ite (Atom (Left a) :: BoolExpr (Either SAT.Lit (LA.Atom Rational))) (Atom $ Right le1) (Atom $ Right eq2)
      c2 = Atom (Right gt3) .||. (Atom (Left a) .<=>. Atom (Right lt4))

  addFormula c1
  addFormula c2

  ret <- SAT.solve satSolver
  ret @?= True

  m1 <- SAT.getModel satSolver
  m2 <- Simplex.getModel lraSolver
  defs <- readIORef defsRef
  let f (Left lit) = SAT.evalLit m1 lit
      f (Right atom) = LA.eval m2 atom
  fold f c1 @?= True
  fold f c2 @?= True


case_QF_EUF :: Assertion
case_QF_EUF = do
  satSolver <- SAT.newSolver
  eufSolver <- EUF.newSolver
  enc <- Tseitin.newEncoder satSolver
  
  tblRef <- newIORef (Map.empty :: Map (EUF.Term, EUF.Term) SAT.Var)
  defsRef <- newIORef (IntMap.empty :: IntMap (EUF.Term, EUF.Term))
  eufModelRef <- newIORef (undefined :: EUF.Model)
 
  let abstractEUFAtom :: (EUF.Term, EUF.Term) -> IO SAT.Lit
      abstractEUFAtom (t1,t2) | t1 >= t2 = abstractEUFAtom (t2,t1)
      abstractEUFAtom (t1,t2) = do
        tbl <- readIORef tblRef
        case Map.lookup (t1,t2) tbl of
          Just v -> return v
          Nothing -> do
            v <- SAT.newVar satSolver
            writeIORef tblRef $! Map.insert (t1,t2) v tbl
            modifyIORef' defsRef $! IntMap.insert v (t1,t2)
            return v

      abstract :: BoolExpr (Either SAT.Lit (EUF.Term, EUF.Term)) -> IO (BoolExpr SAT.Lit)
      abstract = Traversable.mapM f
        where
          f (Left lit) = return lit
          f (Right atom) = abstractEUFAtom atom

  let tsolver =
        TheorySolver
        { thAssertLit = \_ l -> do
            defs <- readIORef defsRef
            case IntMap.lookup (SAT.litVar l) defs of
              Nothing -> return True
              Just (t1,t2) -> do
                if SAT.litPolarity l then
                  EUF.assertEqual' eufSolver t1 t2 (Just l)
                else
                  EUF.assertNotEqual' eufSolver t1 t2 (Just l)
                return True
        , thCheck = \callback -> do
            b <- EUF.check eufSolver
            when b $ do
              defs <- readIORef defsRef
              forM_ (IntMap.toList defs) $ \(v, (t1, t2)) -> do
                b2 <- EUF.areEqual eufSolver t1 t2
                when b2 $ do
                  callback v
                  return ()
            return b            
        , thExplain = \m -> do
            case m of
              Nothing -> liftM IntSet.toList $ EUF.explain eufSolver Nothing
              Just v -> do
                defs <- readIORef defsRef
                case IntMap.lookup v defs of
                  Nothing -> error "should not happen"
                  Just (t1,t2) -> do
                    liftM IntSet.toList $ EUF.explain eufSolver (Just (t1,t2))
        , thPushBacktrackPoint = do
            EUF.pushBacktrackPoint eufSolver
        , thPopBacktrackPoint = do
            EUF.popBacktrackPoint eufSolver
        , thConstructModel = do
            writeIORef eufModelRef =<< EUF.getModel eufSolver
            return ()
        }
  SAT.setTheory satSolver tsolver

  true  <- EUF.newConst eufSolver
  false <- EUF.newConst eufSolver
  EUF.assertNotEqual eufSolver true false
  boolToTermRef <- newIORef (IntMap.empty :: IntMap EUF.Term)
  termToBoolRef <- newIORef (Map.empty :: Map EUF.Term SAT.Lit)

  let connectBoolTerm :: SAT.Lit -> EUF.Term -> IO ()
      connectBoolTerm lit t = do
        lit1 <- abstractEUFAtom (t, true)
        lit2 <- abstractEUFAtom (t, false)
        SAT.addClause satSolver [-lit, lit1]  --  lit  ->  lit1
        SAT.addClause satSolver [-lit1, lit]  --  lit1 ->  lit
        SAT.addClause satSolver [lit, lit2]   -- -lit  ->  lit2
        SAT.addClause satSolver [-lit2, -lit] --  lit2 -> -lit
        modifyIORef' boolToTermRef $ IntMap.insert lit t
        modifyIORef' termToBoolRef $ Map.insert t lit

      boolToTerm :: SAT.Lit -> IO EUF.Term
      boolToTerm lit = do
        tbl <- readIORef boolToTermRef
        case IntMap.lookup lit tbl of
          Just t -> return t
          Nothing -> do
            t <- EUF.newConst eufSolver
            connectBoolTerm lit t
            return t

      termToBool :: EUF.Term -> IO SAT.Lit
      termToBool t = do
        tbl <- readIORef termToBoolRef
        case Map.lookup t tbl of
          Just lit -> return lit
          Nothing -> do
            lit <- SAT.newVar satSolver
            connectBoolTerm lit t
            return lit

  let addFormula :: BoolExpr (Either SAT.Lit (EUF.Term, EUF.Term)) -> IO ()
      addFormula c = Tseitin.addFormula enc =<< abstract c

  do
    x <- SAT.newVar satSolver
    x' <- boolToTerm x
    f <- EUF.newFun eufSolver
    fx <- termToBool (f x')
    ftt <- abstractEUFAtom (f true, true)
    ret <- SAT.solveWith satSolver [-fx, ftt]
    ret @?= True

    m1 <- SAT.getModel satSolver
    m2 <- readIORef eufModelRef
    let e (Left lit) = SAT.evalLit m1 lit
        e (Right (lhs,rhs)) = EUF.eval m2 lhs == EUF.eval m2 rhs
    fold e (notB (Atom (Left fx)) .||. (Atom (Right (f true, true)))) @?= True
    SAT.evalLit m1 x @?= False

    ret <- SAT.solveWith satSolver [-fx, ftt, x]
    ret @?= False

  do
    -- a : Bool
    -- f : U -> U
    -- x : U
    -- y : U
    -- (a or x=y)
    -- f x /= f y
    a <- SAT.newVar satSolver
    f <- EUF.newFun eufSolver
    x <- EUF.newConst eufSolver
    y <- EUF.newConst eufSolver
    let c1, c2 :: BoolExpr (Either SAT.Lit (EUF.Term, EUF.Term))
        c1 = Atom (Left a) .||. Atom (Right (x,y))
        c2 = notB $ Atom (Right (f x, f y))
    addFormula c1
    addFormula c2
    ret <- SAT.solve satSolver
    ret @?= True
    m1 <- SAT.getModel satSolver
    m2 <- readIORef eufModelRef
    let e (Left lit) = SAT.evalLit m1 lit
        e (Right (lhs,rhs)) = EUF.eval m2 lhs == EUF.eval m2 rhs
    fold e c1 @?= True
    fold e c2 @?= True

    ret <- SAT.solveWith satSolver [-a]
    ret @?= False

-- should be SAT
case_solve_SAT :: Assertion
case_solve_SAT = do
  solver <- SAT.newSolver
  x1 <- SAT.newVar solver
  x2 <- SAT.newVar solver
  SAT.addClause solver [x1, x2]  -- x1 or x2
  SAT.addClause solver [x1, -x2] -- x1 or not x2
  SAT.addClause solver [-x1, -x2] -- not x1 or not x2
  ret <- SAT.solve solver
  ret @?= True

-- shuld be UNSAT
case_solve_UNSAT :: Assertion
case_solve_UNSAT = do
  solver <- SAT.newSolver
  x1 <- SAT.newVar solver
  x2 <- SAT.newVar solver
  SAT.addClause solver [x1,  x2]  -- x1 or x2
  SAT.addClause solver [-x1, x2]  -- not x1 or x2
  SAT.addClause solver [x1,  -x2] -- x1 or not x2
  SAT.addClause solver [-x1, -x2] -- not x2 or not x2
  ret <- SAT.solve solver
  ret @?= False

-- top level でいきなり矛盾
case_root_inconsistent :: Assertion
case_root_inconsistent = do
  solver <- SAT.newSolver
  x1 <- SAT.newVar solver
  SAT.addClause solver [x1]
  SAT.addClause solver [-x1]
  ret <- SAT.solve solver -- unsat
  ret @?= False

-- incremental に制約を追加
case_incremental_solving :: Assertion
case_incremental_solving = do
  solver <- SAT.newSolver
  x1 <- SAT.newVar solver
  x2 <- SAT.newVar solver
  SAT.addClause solver [x1,  x2]  -- x1 or x2
  SAT.addClause solver [x1,  -x2] -- x1 or not x2
  SAT.addClause solver [-x1, -x2] -- not x1 or not x2
  ret <- SAT.solve solver -- sat
  ret @?= True

  SAT.addClause solver [-x1, x2]  -- not x1 or x2
  ret <- SAT.solve solver -- unsat
  ret @?= False

-- 制約なし
case_empty_constraint :: Assertion
case_empty_constraint = do
  solver <- SAT.newSolver
  ret <- SAT.solve solver
  ret @?= True

-- 空の節
case_empty_claue :: Assertion
case_empty_claue = do
  solver <- SAT.newSolver
  SAT.addClause solver []
  ret <- SAT.solve solver
  ret @?= False

-- 自明に真な節
case_excluded_middle_claue :: Assertion
case_excluded_middle_claue = do
  solver <- SAT.newSolver
  x1 <- SAT.newVar solver
  SAT.addClause solver [x1, -x1] -- x1 or not x1
  ret <- SAT.solve solver
  ret @?= True

-- 冗長な節
case_redundant_clause :: Assertion
case_redundant_clause = do
  solver <- SAT.newSolver
  x1 <- SAT.newVar solver
  SAT.addClause solver [x1,x1] -- x1 or x1
  ret <- SAT.solve solver
  ret @?= True

case_instantiateClause :: Assertion
case_instantiateClause = do
  solver <- SAT.newSolver
  x1 <- SAT.newVar solver
  x2 <- SAT.newVar solver
  SAT.addClause solver [x1]
  SAT.addClause solver [x1,x2]
  SAT.addClause solver [-x1,x2]
  ret <- SAT.solve solver
  ret @?= True

case_instantiateAtLeast :: Assertion
case_instantiateAtLeast = do
  solver <- SAT.newSolver
  x1 <- SAT.newVar solver
  x2 <- SAT.newVar solver
  x3 <- SAT.newVar solver
  x4 <- SAT.newVar solver
  SAT.addClause solver [x1]

  SAT.addAtLeast solver [x1,x2,x3,x4] 2
  ret <- SAT.solve solver
  ret @?= True

  SAT.addAtLeast solver [-x1,-x2,-x3,-x4] 2
  ret <- SAT.solve solver
  ret @?= True

case_inconsistent_AtLeast :: Assertion
case_inconsistent_AtLeast = do
  solver <- SAT.newSolver
  x1 <- SAT.newVar solver
  x2 <- SAT.newVar solver
  SAT.addAtLeast solver [x1,x2] 3
  ret <- SAT.solve solver -- unsat
  ret @?= False

case_trivial_AtLeast :: Assertion
case_trivial_AtLeast = do
  solver <- SAT.newSolver
  x1 <- SAT.newVar solver
  x2 <- SAT.newVar solver
  SAT.addAtLeast solver [x1,x2] 0
  ret <- SAT.solve solver
  ret @?= True

  solver <- SAT.newSolver
  x1 <- SAT.newVar solver
  x2 <- SAT.newVar solver
  SAT.addAtLeast solver [x1,x2] (-1)
  ret <- SAT.solve solver
  ret @?= True

case_AtLeast_1 :: Assertion
case_AtLeast_1 = do
  solver <- SAT.newSolver
  x1 <- SAT.newVar solver
  x2 <- SAT.newVar solver
  x3 <- SAT.newVar solver
  SAT.addAtLeast solver [x1,x2,x3] 2
  SAT.addAtLeast solver [-x1,-x2,-x3] 2
  ret <- SAT.solve solver -- unsat
  ret @?= False

case_AtLeast_2 :: Assertion
case_AtLeast_2 = do
  solver <- SAT.newSolver
  x1 <- SAT.newVar solver
  x2 <- SAT.newVar solver
  x3 <- SAT.newVar solver
  x4 <- SAT.newVar solver
  SAT.addAtLeast solver [x1,x2,x3,x4] 2
  SAT.addClause solver [-x1,-x2]
  SAT.addClause solver [-x1,-x3]
  ret <- SAT.solve solver
  ret @?= True

case_AtLeast_3 :: Assertion
case_AtLeast_3 = do
  forM_ [(-1) .. 3] $ \n -> do
    solver <- SAT.newSolver
    x1 <- SAT.newVar solver
    x2 <- SAT.newVar solver
    SAT.addAtLeast solver [x1,x2] n
    ret <- SAT.solve solver
    assertEqual ("case_AtLeast3_" ++ show n) (n <= 2) ret

-- from http://www.cril.univ-artois.fr/PB11/format.pdf
case_PB_sample1 :: Assertion
case_PB_sample1 = do
  solver <- SAT.newSolver

  x1 <- SAT.newVar solver
  x2 <- SAT.newVar solver
  x3 <- SAT.newVar solver
  x4 <- SAT.newVar solver
  x5 <- SAT.newVar solver

  SAT.addPBAtLeast solver [(1,x1),(4,x2),(-2,x5)] 2
  SAT.addPBAtLeast solver [(-1,x1),(4,x2),(-2,x5)] 3
  SAT.addPBAtLeast solver [(12345678901234567890,x4),(4,x3)] 10
  SAT.addPBExactly solver [(2,x2),(3,x4),(2,x1),(3,x5)] 5

  ret <- SAT.solve solver
  ret @?= True

-- 一部の変数を否定に置き換えたもの
case_PB_sample1' :: Assertion
case_PB_sample1' = do
  solver <- SAT.newSolver

  x1 <- SAT.newVar solver
  x2 <- SAT.newVar solver
  x3 <- SAT.newVar solver
  x4 <- SAT.newVar solver
  x5 <- SAT.newVar solver

  SAT.addPBAtLeast solver [(1,x1),(4,-x2),(-2,x5)] 2
  SAT.addPBAtLeast solver [(-1,x1),(4,-x2),(-2,x5)] 3
  SAT.addPBAtLeast solver [(12345678901234567890,-x4),(4,x3)] 10
  SAT.addPBExactly solver [(2,-x2),(3,-x4),(2,x1),(3,x5)] 5

  ret <- SAT.solve solver
  ret @?= True

-- いきなり矛盾したPB制約
case_root_inconsistent_PB :: Assertion
case_root_inconsistent_PB = do
  solver <- SAT.newSolver
  x1 <- SAT.newVar solver
  x2 <- SAT.newVar solver
  SAT.addPBAtLeast solver [(2,x1),(3,x2)] 6
  ret <- SAT.solve solver
  ret @?= False

case_pb_propagate :: Assertion
case_pb_propagate = do
  solver <- SAT.newSolver
  x1 <- SAT.newVar solver
  x2 <- SAT.newVar solver
  SAT.addPBAtLeast solver [(1,x1),(3,x2)] 3
  SAT.addClause solver [-x1]
  ret <- SAT.solve solver
  ret @?= True

case_solveWith_1 :: Assertion
case_solveWith_1 = do
  solver <- SAT.newSolver
  x1 <- SAT.newVar solver
  x2 <- SAT.newVar solver
  x3 <- SAT.newVar solver
  SAT.addClause solver [x1, x2]       -- x1 or x2
  SAT.addClause solver [x1, -x2]      -- x1 or not x2
  SAT.addClause solver [-x1, -x2]     -- not x1 or not x2
  SAT.addClause solver [-x3, -x1, x2] -- not x3 or not x1 or x2

  ret <- SAT.solve solver -- sat
  ret @?= True

  ret <- SAT.solveWith solver [x3] -- unsat
  ret @?= False

  ret <- SAT.solve solver -- sat
  ret @?= True

case_solveWith_2 :: Assertion
case_solveWith_2 = do
  solver <- SAT.newSolver
  x1 <- SAT.newVar solver
  x2 <- SAT.newVar solver
  SAT.addClause solver [-x1, x2] -- -x1 or x2
  SAT.addClause solver [x1]      -- x1

  ret <- SAT.solveWith solver [x2]
  ret @?= True

  ret <- SAT.solveWith solver [-x2]
  ret @?= False

case_getVarFixed :: Assertion
case_getVarFixed = do
  solver <- SAT.newSolver
  x1 <- SAT.newVar solver
  x2 <- SAT.newVar solver
  SAT.addClause solver [x1,x2]

  ret <- SAT.getVarFixed solver x1
  ret @?= lUndef

  SAT.addClause solver [-x1]
  
  ret <- SAT.getVarFixed solver x1
  ret @?= lFalse

  ret <- SAT.getLitFixed solver (-x1)
  ret @?= lTrue

  ret <- SAT.getLitFixed solver x2
  ret @?= lTrue

case_getAssumptionsImplications_case1 :: Assertion
case_getAssumptionsImplications_case1 = do
  solver <- SAT.newSolver
  x1 <- SAT.newVar solver
  x2 <- SAT.newVar solver
  x3 <- SAT.newVar solver
  SAT.addClause solver [x1,x2,x3]

  SAT.addClause solver [-x1]
  ret <- SAT.solveWith solver [-x2]
  ret @?= True
  xs <- SAT.getAssumptionsImplications solver
  xs @?= [x3]

prop_getAssumptionsImplications :: Property
prop_getAssumptionsImplications = QM.monadicIO $ do
  cnf <- QM.pick arbitraryCNF
  solver <- arbitrarySolver
  ls <- QM.pick $ liftM concat $ mapM (\v -> elements [[],[-v],[v]]) [1..CNF.numVars cnf]
  ret <- QM.run $ do
    SAT.newVars_ solver (CNF.numVars cnf)
    forM_ (CNF.clauses cnf) $ \c -> SAT.addClause solver (SAT.unpackClause c)
    SAT.solveWith solver ls
  when ret $ do
    xs <- QM.run $ SAT.getAssumptionsImplications solver
    forM_ xs $ \x -> do
      ret2 <- QM.run $ SAT.solveWith solver (-x : ls)
      QM.assert $ not ret2

------------------------------------------------------------------------

-- -4*(not x1) + 3*x1 + 10*(not x2)
-- = -4*(1 - x1) + 3*x1 + 10*(not x2)
-- = -4 + 4*x1 + 3*x1 + 10*(not x2)
-- = 7*x1 + 10*(not x2) - 4
case_normalizePBLinSum_1 :: Assertion
case_normalizePBLinSum_1 = do
  sort e @?= sort [(7,x1),(10,-x2)]
  c @?= -4
  where
    x1 = 1
    x2 = 2
    (e,c) = SAT.normalizePBLinSum ([(-4,-x1),(3,x1),(10,-x2)], 0)

prop_normalizePBLinSum :: Property
prop_normalizePBLinSum = forAll g $ \(nv, (s,n)) ->
    let (s2,n2) = SAT.normalizePBLinSum (s,n)
    in flip all (allAssignments nv) $ \m ->
         SAT.evalPBLinSum m s + n == SAT.evalPBLinSum m s2 + n2
  where
    g :: Gen (Int, (SAT.PBLinSum, Integer))
    g = do
      nv <- choose (0, 10)
      s <- forM [1..nv] $ \x -> do
        c <- arbitrary
        p <- arbitrary
        return (c, SAT.literal x p)
      n <- arbitrary
      return (nv, (s,n))

-- -4*(not x1) + 3*x1 + 10*(not x2) >= 3
-- ⇔ -4*(1 - x1) + 3*x1 + 10*(not x2) >= 3
-- ⇔ -4 + 4*x1 + 3*x1 + 10*(not x2) >= 3
-- ⇔ 7*x1 + 10*(not x2) >= 7
-- ⇔ 7*x1 + 7*(not x2) >= 7
-- ⇔ x1 + (not x2) >= 1
case_normalizePBLinAtLeast_1 :: Assertion
case_normalizePBLinAtLeast_1 = (sort lhs, rhs) @?= (sort [(1,x1),(1,-x2)], 1)
  where
    x1 = 1
    x2 = 2
    (lhs,rhs) = SAT.normalizePBLinAtLeast ([(-4,-x1),(3,x1),(10,-x2)], 3)

prop_normalizePBLinAtLeast :: Property
prop_normalizePBLinAtLeast = forAll g $ \(nv, c) ->
    let c2 = SAT.normalizePBLinAtLeast c
    in flip all (allAssignments nv) $ \m ->
         SAT.evalPBLinAtLeast m c == SAT.evalPBLinAtLeast m c2
  where
    g :: Gen (Int, SAT.PBLinAtLeast)
    g = do
      nv <- choose (0, 10)
      lhs <- forM [1..nv] $ \x -> do
        c <- arbitrary
        p <- arbitrary
        return (c, SAT.literal x p)
      rhs <- arbitrary
      return (nv, (lhs,rhs))

case_normalizePBLinExactly_1 :: Assertion
case_normalizePBLinExactly_1 = (sort lhs, rhs) @?= ([], 1)
  where
    x1 = 1
    x2 = 2
    (lhs,rhs) = SAT.normalizePBLinExactly ([(6,x1),(4,x2)], 2)

case_normalizePBLinExactly_2 :: Assertion
case_normalizePBLinExactly_2 = (sort lhs, rhs) @?= ([], 1)
  where
    x1 = 1
    x2 = 2
    x3 = 3
    (lhs,rhs) = SAT.normalizePBLinExactly ([(2,x1),(2,x2),(2,x3)], 3)

prop_normalizePBLinExactly :: Property
prop_normalizePBLinExactly = forAll g $ \(nv, c) ->
    let c2 = SAT.normalizePBLinExactly c
    in flip all (allAssignments nv) $ \m ->
         SAT.evalPBLinExactly m c == SAT.evalPBLinExactly m c2
  where
    g :: Gen (Int, SAT.PBLinExactly)
    g = do
      nv <- choose (0, 10)
      lhs <- forM [1..nv] $ \x -> do
        c <- arbitrary
        p <- arbitrary
        return (c, SAT.literal x p)
      rhs <- arbitrary
      return (nv, (lhs,rhs))

prop_cutResolve :: Property
prop_cutResolve =
  forAll (choose (1, 10)) $ \nv ->
    forAll (g nv True) $ \c1 ->
      forAll (g nv False) $ \c2 ->
        let c3 = SAT.cutResolve c1 c2 1
        in flip all (allAssignments nv) $ \m ->
             not (SAT.evalPBLinExactly m c1 && SAT.evalPBLinExactly m c2) || SAT.evalPBLinExactly m c3
  where
    g :: Int -> Bool -> Gen SAT.PBLinExactly
    g nv b = do
      lhs <- forM [1..nv] $ \x -> do
        if x==1 then do
          c <- liftM ((1+) . abs) arbitrary
          return (c, SAT.literal x b)
        else do
          c <- arbitrary
          p <- arbitrary
          return (c, SAT.literal x p)
      rhs <- arbitrary
      return (lhs, rhs)

case_cutResolve_1 :: Assertion
case_cutResolve_1 = (sort lhs, rhs) @?= (sort [(1,x3),(1,x4)], 1)
  where
    x1 = 1
    x2 = 2
    x3 = 3
    x4 = 4
    pb1 = ([(1,x1), (1,x2), (1,x3)], 1)
    pb2 = ([(2,-x1), (2,-x2), (1,x4)], 3)
    (lhs,rhs) = SAT.cutResolve pb1 pb2 x1

case_cutResolve_2 :: Assertion
case_cutResolve_2 = (sort lhs, rhs) @?= (sort lhs2, rhs2)
  where
    x1 = 1
    x2 = 2
    x3 = 3
    x4 = 4
    pb1 = ([(3,x1), (2,-x2), (1,x3), (1,x4)], 3)
    pb2 = ([(1,-x3), (1,x4)], 1)
    (lhs,rhs) = SAT.cutResolve pb1 pb2 x3
    (lhs2,rhs2) = ([(2,x1),(1,-x2),(1,x4)],2) -- ([(3,x1),(2,-x2),(2,x4)], 3)

case_cardinalityReduction :: Assertion
case_cardinalityReduction = (sort lhs, rhs) @?= ([1,2,3,4,5],4)
  where
    (lhs, rhs) = SAT.cardinalityReduction ([(6,1),(5,2),(4,3),(3,4),(2,5),(1,6)], 17)

case_pbSubsume_clause :: Assertion
case_pbSubsume_clause = SAT.pbSubsume ([(1,1),(1,-3)],1) ([(1,1),(1,2),(1,-3),(1,4)],1) @?= True

case_pbSubsume_1 :: Assertion
case_pbSubsume_1 = SAT.pbSubsume ([(1,1),(1,2),(1,-3)],2) ([(1,1),(2,2),(1,-3),(1,4)],1) @?= True

case_pbSubsume_2 :: Assertion
case_pbSubsume_2 = SAT.pbSubsume ([(1,1),(1,2),(1,-3)],2) ([(1,1),(2,2),(1,-3),(1,4)],3) @?= False

------------------------------------------------------------------------

case_normalizeXORClause_False =
  SAT.normalizeXORClause ([],True) @?= ([],True)

case_normalizeXORClause_True =
  SAT.normalizeXORClause ([],False) @?= ([],False)

-- x ⊕ y ⊕ x = y
case_normalizeXORClause_case1 =
  SAT.normalizeXORClause ([1,2,1],True) @?= ([2],True)

-- x ⊕ ¬x = x ⊕ x ⊕ 1 = 1
case_normalizeXORClause_case2 =
  SAT.normalizeXORClause ([1,-1],True) @?= ([],False)

prop_normalizeXORClause :: Property
prop_normalizeXORClause = forAll g $ \(nv, c) ->
    let c2 = SAT.normalizeXORClause c
    in flip all (allAssignments nv) $ \m ->
         SAT.evalXORClause m c == SAT.evalXORClause m c2
  where
    g :: Gen (Int, SAT.XORClause)
    g = do
      nv <- choose (0, 10)
      len <- choose (0, nv)
      lhs <- replicateM len $ choose (-nv, nv) `suchThat` (/= 0)
      rhs <- arbitrary
      return (nv, (lhs,rhs))

case_evalXORClause_case1 =
  SAT.evalXORClause (array (1,2) [(1,True),(2,True)] :: Array Int Bool) ([1,2], True) @?= False

case_evalXORClause_case2 =
  SAT.evalXORClause (array (1,2) [(1,False),(2,True)] :: Array Int Bool) ([1,2], True) @?= True

case_xor_case1 = do
  solver <- SAT.newSolver
  SAT.modifyConfig solver $ \config -> config{ SAT.configCheckModel = True }
  x1 <- SAT.newVar solver
  x2 <- SAT.newVar solver
  x3 <- SAT.newVar solver
  SAT.addXORClause solver [x1, x2] True -- x1 ⊕ x2 = True
  SAT.addXORClause solver [x2, x3] True -- x2 ⊕ x3 = True
  SAT.addXORClause solver [x3, x1] True -- x3 ⊕ x1 = True
  ret <- SAT.solve solver
  ret @?= False

case_xor_case2 = do
  solver <- SAT.newSolver
  SAT.modifyConfig solver $ \config -> config{ SAT.configCheckModel = True }
  x1 <- SAT.newVar solver
  x2 <- SAT.newVar solver
  x3 <- SAT.newVar solver
  SAT.addXORClause solver [x1, x2] True -- x1 ⊕ x2 = True
  SAT.addXORClause solver [x1, x3] True -- x1 ⊕ x3 = True
  SAT.addClause solver [x2]

  ret <- SAT.solve solver
  ret @?= True
  m <- SAT.getModel solver
  m ! x1 @?= False
  m ! x2 @?= True
  m ! x3 @?= True

case_xor_case3 = do
  solver <- SAT.newSolver
  SAT.modifyConfig solver $ \config -> config{ SAT.configCheckModel = True }
  x1 <- SAT.newVar solver
  x2 <- SAT.newVar solver
  x3 <- SAT.newVar solver
  x4 <- SAT.newVar solver
  SAT.addXORClause solver [x1,x2,x3,x4] True
  SAT.addAtLeast solver [x1,x2,x3,x4] 2
  ret <- SAT.solve solver
  ret @?= True

------------------------------------------------------------------------

-- from "Pueblo: A Hybrid Pseudo-Boolean SAT Solver"
-- clauseがunitになるレベルで、PB制約が違反状態のままという例。
case_hybridLearning_1 :: Assertion
case_hybridLearning_1 = do
  solver <- SAT.newSolver
  [x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11] <- replicateM 11 (SAT.newVar solver)

  SAT.addClause solver [x11, x10, x9] -- C1
  SAT.addClause solver [x8, x7, x6]   -- C2
  SAT.addClause solver [x5, x4, x3]   -- C3
  SAT.addAtLeast solver [-x2, -x5, -x8, -x11] 3 -- C4
  SAT.addAtLeast solver [-x1, -x4, -x7, -x10] 3 -- C5

  replicateM 3 (SAT.varBumpActivity solver x3)
  SAT.setVarPolarity solver x3 False

  replicateM 2 (SAT.varBumpActivity solver x6)
  SAT.setVarPolarity solver x6 False

  replicateM 1 (SAT.varBumpActivity solver x9)
  SAT.setVarPolarity solver x9 False

  SAT.setVarPolarity solver x1 True

  SAT.modifyConfig solver $ \config -> config{ SAT.configLearningStrategy = SAT.LearningHybrid }
  ret <- SAT.solve solver
  ret @?= True

-- from "Pueblo: A Hybrid Pseudo-Boolean SAT Solver"
-- clauseがunitになるレベルで、PB制約が違反状態のままという例。
-- さらに、学習したPB制約はunitにはならない。
case_hybridLearning_2 :: Assertion
case_hybridLearning_2 = do
  solver <- SAT.newSolver
  [x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12] <- replicateM 12 (SAT.newVar solver)

  SAT.addClause solver [x11, x10, x9] -- C1
  SAT.addClause solver [x8, x7, x6]   -- C2
  SAT.addClause solver [x5, x4, x3]   -- C3
  SAT.addAtLeast solver [-x2, -x5, -x8, -x11] 3 -- C4
  SAT.addAtLeast solver [-x1, -x4, -x7, -x10] 3 -- C5

  SAT.addClause solver [x12, -x3]
  SAT.addClause solver [x12, -x6]
  SAT.addClause solver [x12, -x9]

  SAT.varBumpActivity solver x12
  SAT.setVarPolarity solver x12 False

  SAT.modifyConfig solver $ \config -> config{ SAT.configLearningStrategy = SAT.LearningHybrid }
  ret <- SAT.solve solver
  ret @?= True

-- regression test for the bug triggered by normalized-blast-floppy1-8.ucl.opb.bz2
case_addPBAtLeast_regression :: Assertion
case_addPBAtLeast_regression = do
  solver <- SAT.newSolver
  [x1,x2,x3,x4] <- replicateM 4 (SAT.newVar solver)
  SAT.addClause solver [-x1]
  SAT.addClause solver [-x2, -x3]
  SAT.addClause solver [-x2, -x4]
  SAT.addPBAtLeast solver [(1,x1),(2,x2),(1,x3),(1,x4)] 3
  ret <- SAT.solve solver
  ret @?= False

-- https://github.com/msakai/toysolver/issues/22
case_issue22 :: Assertion
case_issue22 = do
  let config = def
        { SAT.configLearningStrategy = SAT.LearningHybrid
        , SAT.configCCMin = 2
        , SAT.configBranchingStrategy = SAT.BranchingLRB
        , SAT.configRandomFreq = 0.2816351099559239
        , SAT.configPBHandlerType = SAT.PBHandlerTypeCounter
        }
  solver <- SAT.newSolverWithConfig config
  _ <- SAT.newVars solver 14
  SAT.addClause solver [-7,-1]
  SAT.addClause solver [-9,-4]
  SAT.addClause solver [-9,1]
  SAT.addClause solver [-10,-1]
  SAT.addClause solver [-11,-1]
  SAT.addClause solver [-12,-4]
  SAT.addClause solver [-12,4]
  SAT.addClause solver [-13,-3]
  SAT.addClause solver [-13,-1]
  SAT.addClause solver [-13,3]
  SAT.addClause solver [-14,-1]
  SAT.addPBAtLeast solver [ (1,-14), (10,13), (7,12), (13,-11), (14,-10), (16,9), (8,8), (9,-7)]   38
  SAT.addPBAtLeast solver [(-1,-14),(-10,13),(-7,12),(-13,-11),(-14,-10),(-16,9),(-8,8),(-9,-7)] (-38)
  SAT.setRandomGen solver =<< Rand.initialize (V.singleton 71)
  SAT.solve solver
  return ()
{-
Scenario:
decide 4@1
deduce -12 by [-12,-4]
deduce -9 by [-9,-4]
decide 1@2
deduce -14 by [-14,-1]
deduce -13 by [-13,-1]
deduce -11 by [-11,-1]
deduce -10 by [-10,-1]
deduce -7 by [-7,-1]
deduce 8 by [(16,9),(14,-10),(13,-11),(10,13),(9,-7),(8,8),(7,12),(1,-14)] >= 38
conflict: [(16,-9),(14,10),(13,11),(10,-13),(9,7),(8,-8),(7,-12),(1,14)] >= 40
conflict analysis yields
  [-1,9,12] @1, and
  [(1,14),(2,-13),(1,12),(8,-9),(17,-1)],17) >= 17 @1 (but it should be @0)
backtrack to @1
deduce -1 by [-1,9,12]
decide 3@3
deduce -13 by [-13,-3]
deduce -10, -11, -7, 8 by [(16,9),(14,-10),(13,-11),(10,13),(9,-7),(8,8),(7,12),(1,-14)] >= 38
conflict [(16,-9),(14,10),(13,11),(10,-13),(9,7),(8,-8),(7,-12),(1,14)] >= 40
conflict analysis yields
  [13,9,12] @1 and
  [(1,14),(7,13),(7,12),(7,9)] >= 7 @1 (but it should be @0)
backtrack to @1
deduce 13 by [13,9,12]
deduce 3 by [3,-13]
conflict [-3,-13]
conflict analysis yields
  -13 @ 0
decide -7@1
decide -14@2
deduce -1 by [(17,-1),(8,-9),(2,-13),(1,14),(1,12)] >= 17
deduce -9 by [-9,1]
deduce 12 by [12,9,13]
deduce 4 by [4,-12]
conflict: [-4,-12]
conflict analysis yields [] and that causes error
-}

------------------------------------------------------------------------

case_addFormula = do
  solver <- SAT.newSolver
  enc <- Tseitin.newEncoder solver

  [x1,x2,x3,x4,x5] <- replicateM 5 $ liftM Atom $ SAT.newVar solver
  Tseitin.addFormula enc $ orB [x1 .=>. x3 .&&. x4, x2 .=>. x3 .&&. x5]
  -- x6 = x3 ∧ x4
  -- x7 = x3 ∧ x5
  Tseitin.addFormula enc $ x1 .||. x2
  Tseitin.addFormula enc $ x4 .=>. notB x5
  ret <- SAT.solve solver
  ret @?= True

  Tseitin.addFormula enc $ x2 .<=>. x4
  ret <- SAT.solve solver
  ret @?= True

  Tseitin.addFormula enc $ x1 .<=>. x5
  ret <- SAT.solve solver
  ret @?= True

  Tseitin.addFormula enc $ notB x1 .=>. x3 .&&. x5
  ret <- SAT.solve solver
  ret @?= True

  Tseitin.addFormula enc $ notB x2 .=>. x3 .&&. x4
  ret <- SAT.solve solver
  ret @?= False

case_addFormula_Peirces_Law = do
  solver <- SAT.newSolver
  enc <- Tseitin.newEncoder solver
  [x1,x2] <- replicateM 2 $ liftM Atom $ SAT.newVar solver
  Tseitin.addFormula enc $ notB $ ((x1 .=>. x2) .=>. x1) .=>. x1
  ret <- SAT.solve solver
  ret @?= False

case_encodeConj = do
  solver <- SAT.newSolver
  enc <- Tseitin.newEncoder solver
  x1 <- SAT.newVar solver
  x2 <- SAT.newVar solver
  x3 <- Tseitin.encodeConj enc [x1,x2]

  ret <- SAT.solveWith solver [x3]
  ret @?= True
  m <- SAT.getModel solver
  SAT.evalLit m x1 @?= True
  SAT.evalLit m x2 @?= True
  SAT.evalLit m x3 @?= True

  ret <- SAT.solveWith solver [-x3]
  ret @?= True
  m <- SAT.getModel solver
  (SAT.evalLit m x1 && SAT.evalLit m x2) @?= False
  SAT.evalLit m x3 @?= False

case_encodeDisj = do
  solver <- SAT.newSolver
  enc <- Tseitin.newEncoder solver
  x1 <- SAT.newVar solver
  x2 <- SAT.newVar solver
  x3 <- Tseitin.encodeDisj enc [x1,x2]

  ret <- SAT.solveWith solver [x3]
  ret @?= True
  m <- SAT.getModel solver
  (SAT.evalLit m x1 || SAT.evalLit m x2) @?= True
  SAT.evalLit m x3 @?= True

  ret <- SAT.solveWith solver [-x3]
  ret @?= True
  m <- SAT.getModel solver
  SAT.evalLit m x1 @?= False
  SAT.evalLit m x2 @?= False
  SAT.evalLit m x3 @?= False

case_evalFormula = do
  solver <- SAT.newSolver
  xs <- SAT.newVars solver 5
  let f = (x1 .=>. x3 .&&. x4) .||. (x2 .=>. x3 .&&. x5)
        where
          [x1,x2,x3,x4,x5] = map Atom xs
      g :: SAT.Model -> Bool
      g m = (not x1 || (x3 && x4)) || (not x2 || (x3 && x5))
        where
          [x1,x2,x3,x4,x5] = elems m
  forM_ (allAssignments 5) $ \m -> do
    Tseitin.evalFormula m f @?= g m

prop_PBEncoder_addPBAtLeast = QM.monadicIO $ do
  let nv = 4
  (lhs,rhs) <- QM.pick $ do
    lhs <- arbitraryPBLinSum nv
    rhs <- arbitrary
    return $ SAT.normalizePBLinAtLeast (lhs, rhs)
  strategy <- QM.pick arbitrary
  (cnf,defs) <- QM.run $ do
    db <- CNFStore.newCNFStore
    SAT.newVars_ db nv
    tseitin <- Tseitin.newEncoder db
    pb <- PB.newEncoderWithStrategy tseitin strategy
    SAT.addPBAtLeast pb lhs rhs
    cnf <- CNFStore.getCNFFormula db
    defs <- Tseitin.getDefinitions tseitin
    return (cnf, defs)
  forM_ (allAssignments 4) $ \m -> do
    let m2 :: Array SAT.Var Bool
        m2 = array (1, CNF.numVars cnf) $ assocs m ++ [(v, Tseitin.evalFormula m2 phi) | (v,phi) <- defs]
        b1 = SAT.evalPBLinAtLeast m (lhs,rhs)
        b2 = evalCNF (array (bounds m2) (assocs m2)) cnf
    QM.assert $ b1 == b2

prop_PBEncoder_Sorter_genSorter :: [Int] -> Bool
prop_PBEncoder_Sorter_genSorter xs =
  V.toList (PBEncSorter.sortVector (V.fromList xs)) == sort xs

prop_PBEncoder_Sorter_decode_encode :: Property
prop_PBEncoder_Sorter_decode_encode =
  forAll arbitrary $ \base' ->
    forAll arbitrary $ \(NonNegative x) ->
      let base = [b | Positive b <- base']
      in PBEncSorter.isRepresentable base x
         ==>
         (PBEncSorter.decode base . PBEncSorter.encode base) x == x

------------------------------------------------------------------------

findMUSAssumptions_case1 :: MUS.Method -> IO ()
findMUSAssumptions_case1 method = do
  solver <- SAT.newSolver
  [x1,x2,x3] <- SAT.newVars solver 3
  sels@[y1,y2,y3,y4,y5,y6] <- SAT.newVars solver 6
  SAT.addClause solver [-y1, x1]
  SAT.addClause solver [-y2, -x1]
  SAT.addClause solver [-y3, -x1, x2]
  SAT.addClause solver [-y4, -x2]
  SAT.addClause solver [-y5, -x1, x3]
  SAT.addClause solver [-y6, -x3]

  ret <- SAT.solveWith solver sels
  ret @?= False

  actual <- MUS.findMUSAssumptions solver def{ MUS.optMethod = method }
  let actual'  = IntSet.map (\x -> x-3) actual
      expected = map IntSet.fromList [[1, 2], [1, 3, 4], [1, 5, 6]]
  actual' `elem` expected @?= True

case_findMUSAssumptions_Deletion = findMUSAssumptions_case1 MUS.Deletion
case_findMUSAssumptions_Insertion = findMUSAssumptions_case1 MUS.Insertion
case_findMUSAssumptions_QuickXplain = findMUSAssumptions_case1 MUS.QuickXplain

------------------------------------------------------------------------

{-
c http://sun.iwu.edu/~mliffito/publications/jar_liffiton_CAMUS.pdf
c φ= (x1) ∧ (¬x1) ∧ (¬x1∨x2) ∧ (¬x2) ∧ (¬x1∨x3) ∧ (¬x3)
c MUSes(φ) = {{C1, C2}, {C1, C3, C4}, {C1, C5, C6}}
c MCSes(φ) = {{C1}, {C2, C3, C5}, {C2, C3, C6}, {C2, C4, C5}, {C2, C4, C6}}
p cnf 3 6
1 0
-1 0
-1 2 0
-2 0
-1 3 0
-3 0
-}

allMUSAssumptions_case1 :: MUSEnum.Method -> IO ()
allMUSAssumptions_case1 method = do
  solver <- SAT.newSolver
  [x1,x2,x3] <- SAT.newVars solver 3
  sels@[y1,y2,y3,y4,y5,y6] <- SAT.newVars solver 6
  SAT.addClause solver [-y1, x1]
  SAT.addClause solver [-y2, -x1]
  SAT.addClause solver [-y3, -x1, x2]
  SAT.addClause solver [-y4, -x2]
  SAT.addClause solver [-y5, -x1, x3]
  SAT.addClause solver [-y6, -x3]
  (muses, mcses) <- MUSEnum.allMUSAssumptions solver sels def{ MUSEnum.optMethod = method }
  Set.fromList muses @?= Set.fromList (map (IntSet.fromList . map (+3)) [[1,2], [1,3,4], [1,5,6]])
  Set.fromList mcses @?= Set.fromList (map (IntSet.fromList . map (+3)) [[1], [2,3,5], [2,3,6], [2,4,5], [2,4,6]])

case_allMUSAssumptions_CAMUS = allMUSAssumptions_case1 MUSEnum.CAMUS
case_allMUSAssumptions_DAA = allMUSAssumptions_case1 MUSEnum.DAA
case_allMUSAssumptions_MARCO = allMUSAssumptions_case1 MUSEnum.MARCO
case_allMUSAssumptions_GurvichKhachiyan1999 = allMUSAssumptions_case1 MUSEnum.GurvichKhachiyan1999

{-
Boosting a Complete Technique to Find MSS and MUS thanks to a Local Search Oracle
http://www.cril.univ-artois.fr/~piette/IJCAI07_HYCAM.pdf
Example 3.
C0  : (d)
C1  : (b ∨ c)
C2  : (a ∨ b)
C3  : (a ∨ ¬c)
C4  : (¬b ∨ ¬e)
C5  : (¬a ∨ ¬b)
C6  : (a ∨ e)
C7  : (¬a ∨ ¬e)
C8  : (b ∨ e)
C9  : (¬a ∨ b ∨ ¬c)
C10 : (¬a ∨ b ∨ ¬d)
C11 : (a ∨ ¬b ∨ c)
C12 : (a ∨ ¬b ∨ ¬d)
-}
allMUSAssumptions_case2 :: MUSEnum.Method -> IO ()
allMUSAssumptions_case2 method = do
  solver <- SAT.newSolver
  [a,b,c,d,e] <- SAT.newVars solver 5
  sels@[y0,y1,y2,y3,y4,y5,y6,y7,y8,y9,y10,y11,y12] <- SAT.newVars solver 13
  SAT.addClause solver [-y0, d]
  SAT.addClause solver [-y1, b, c]
  SAT.addClause solver [-y2, a, b]
  SAT.addClause solver [-y3, a, -c]
  SAT.addClause solver [-y4, -b, -e]
  SAT.addClause solver [-y5, -a, -b]
  SAT.addClause solver [-y6, a, e]
  SAT.addClause solver [-y7, -a, -e]
  SAT.addClause solver [-y8, b, e]
  SAT.addClause solver [-y9, -a, b, -c]
  SAT.addClause solver [-y10, -a, b, -d]
  SAT.addClause solver [-y11, a, -b, c]
  SAT.addClause solver [-y12, a, -b, -d]

  -- Only three of the MUSes (marked with asterisks) are on the paper.
  let cores =
        [ [y0,y1,y2,y5,y9,y12]
        , [y0,y1,y3,y4,y5,y6,y10]
        , [y0,y1,y3,y5,y7,y8,y12]
        , [y0,y1,y3,y5,y9,y12]
        , [y0,y1,y3,y5,y10,y11]
        , [y0,y1,y3,y5,y10,y12]
        , [y0,y2,y3,y5,y10,y11]
        , [y0,y2,y4,y5,y6,y10]
        , [y0,y2,y5,y7,y8,y12]
        , [y0,y2,y5,y10,y12]   -- (*)
        , [y1,y2,y4,y5,y6,y9]
        , [y1,y3,y4,y5,y6,y7,y8]
        , [y1,y3,y4,y5,y6,y9]
        , [y1,y3,y5,y7,y8,y11]
        , [y1,y3,y5,y9,y11]    -- (*)
        , [y2,y3,y5,y7,y8,y11]
        , [y2,y4,y5,y6,y7,y8]  -- (*)
        ]

  let remove1 :: [a] -> [[a]]
      remove1 [] = []
      remove1 (x:xs) = xs : [x : ys | ys <- remove1 xs]
  forM_ cores $ \core -> do
    ret <- SAT.solveWith solver core
    assertBool (show core ++ " should be a core") (not ret)
    forM (remove1 core) $ \xs -> do
      ret <- SAT.solveWith solver xs
      assertBool (show core ++ " should be satisfiable") ret

  (actual,_) <- MUSEnum.allMUSAssumptions solver sels def{ MUSEnum.optMethod = method }
  let actual'   = Set.fromList actual
      expected' = Set.fromList $ map IntSet.fromList $ cores
  actual' @?= expected'

case_allMUSAssumptions_2_CAMUS = allMUSAssumptions_case2 MUSEnum.CAMUS
case_allMUSAssumptions_2_DAA = allMUSAssumptions_case2 MUSEnum.DAA
case_allMUSAssumptions_2_MARCO = allMUSAssumptions_case2 MUSEnum.MARCO
case_allMUSAssumptions_2_GurvichKhachiyan1999 = allMUSAssumptions_case2 MUSEnum.GurvichKhachiyan1999

case_allMUSAssumptions_2_HYCAM = do
  solver <- SAT.newSolver
  [a,b,c,d,e] <- SAT.newVars solver 5
  sels@[y0,y1,y2,y3,y4,y5,y6,y7,y8,y9,y10,y11,y12] <- SAT.newVars solver 13
  SAT.addClause solver [-y0, d]
  SAT.addClause solver [-y1, b, c]
  SAT.addClause solver [-y2, a, b]
  SAT.addClause solver [-y3, a, -c]
  SAT.addClause solver [-y4, -b, -e]
  SAT.addClause solver [-y5, -a, -b]
  SAT.addClause solver [-y6, a, e]
  SAT.addClause solver [-y7, -a, -e]
  SAT.addClause solver [-y8, b, e]
  SAT.addClause solver [-y9, -a, b, -c]
  SAT.addClause solver [-y10, -a, b, -d]
  SAT.addClause solver [-y11, a, -b, c]
  SAT.addClause solver [-y12, a, -b, -d]

  -- Only three of the MUSes (marked with asterisks) are on the paper.
  let cores =
        [ [y0,y1,y2,y5,y9,y12]
        , [y0,y1,y3,y4,y5,y6,y10]
        , [y0,y1,y3,y5,y7,y8,y12]
        , [y0,y1,y3,y5,y9,y12]
        , [y0,y1,y3,y5,y10,y11]
        , [y0,y1,y3,y5,y10,y12]
        , [y0,y2,y3,y5,y10,y11]
        , [y0,y2,y4,y5,y6,y10]
        , [y0,y2,y5,y7,y8,y12]
        , [y0,y2,y5,y10,y12]   -- (*)
        , [y1,y2,y4,y5,y6,y9]
        , [y1,y3,y4,y5,y6,y7,y8]
        , [y1,y3,y4,y5,y6,y9]
        , [y1,y3,y5,y7,y8,y11]
        , [y1,y3,y5,y9,y11]    -- (*)
        , [y2,y3,y5,y7,y8,y11]
        , [y2,y4,y5,y6,y7,y8]  -- (*)
        ]
      mcses =
        [ [y0,y1,y7]
        , [y0,y1,y8]
        , [y0,y3,y4]
        , [y0,y3,y6]
        , [y0,y4,y11]
        , [y0,y6,y11]
        , [y0,y7,y9]
        , [y0,y8,y9]
        , [y1,y2]
        , [y1,y7,y10]
        , [y1,y8,y10]
        , [y2,y3]
        , [y3,y4,y12]
        , [y3,y6,y12]
        , [y4,y11,y12]
        , [y5]
        , [y6,y11,y12]
        , [y7,y9,y10]
        , [y8,y9,y10]
        ]

  -- HYCAM paper wrongly treated {C3,C8,C10} as a candidate MCS (CoMSS).
  -- Its complement {C0,C1,C2,C4,C5,C6,C7,C9,C11,C12} is unsatisfiable
  -- and hence not MSS.
  ret <- SAT.solveWith solver [y0,y1,y2,y4,y5,y6,y7,y9,y11,y12]
  assertBool "failed to prove the bug of HYCAM paper" (not ret)
  
  let cand = map IntSet.fromList [[y5], [y3,y2], [y0,y1,y2]]
  (actual,_) <- MUSEnum.allMUSAssumptions solver sels def{ MUSEnum.optMethod = MUSEnum.CAMUS, MUSEnum.optKnownCSes = cand }
  let actual'   = Set.fromList $ actual
      expected' = Set.fromList $ map IntSet.fromList cores
  actual' @?= expected'

------------------------------------------------------------------------

prop_ExistentialQuantification :: Property
prop_ExistentialQuantification = QM.monadicIO $ do
  phi <- QM.pick arbitraryCNF
  xs <- QM.pick $ liftM IntSet.fromList $ sublistOf [1 .. CNF.numVars phi]
  let ys = IntSet.fromList [1 .. CNF.numVars phi] IntSet.\\ xs
  psi <- QM.run $ ExistentialQuantification.project xs phi
  forM_ (replicateM (IntSet.size ys) [False,True]) $ \bs -> do
    let m :: SAT.Model
        m = array (1, if IntSet.null ys then 0 else IntSet.findMax ys) (zip (IntSet.toList ys) bs)
    b1 <- QM.run $ do
      solver <- SAT.newSolver
      SAT.newVars_ solver (CNF.numVars phi)
      forM_ (CNF.clauses phi) $ \c -> SAT.addClause solver (SAT.unpackClause c)
      SAT.solveWith solver [if SAT.evalLit m y then y else -y | y <- IntSet.toList ys]
    let b2 = evalCNF m psi
    QM.assert $ b1 == b2

brauer11_phi :: CNF.CNF
brauer11_phi =
  CNF.CNF
  { CNF.numVars = 13
  , CNF.numClauses = 23
  , CNF.clauses = fmap SAT.packClause
      [
      -- μ
        [-x2, -y2]
      , [-y2, -y1]
      , [-x4, -x6, y1]
      , [-x3, y4], [x3, -y4]
      , [-x4, y3], [x4, -y3]
      , [-x5, y6], [x5, -y6]
      , [-x6, y5], [x6, -y5]

      -- ξ
      , [-x13, x1]
      , [-x13, -x2]
      , [-x13, x3]
      , [-x13, -x4]
      , [-x13, x5]
      , [-x13, -x6]
      , [x13, x1]
      , [x13, -x2]
      , [x13, -x3]
      , [x13, x4]
      , [x13, -x5]
      , [x13, x6]
      ]
  }
  where
    [y1,y2,y3,y4,y5,y6] = [1..6]
    [x1,x2,x3,x4,x5,x6,x13] = [7..13]

{-
ξ(m'1) = (¬y1 ∧ ¬y3 ∧ y4 ∧ ¬y5 ∧ y6)
ξ(m'2) = (y1 ∧ ¬y2 ∧ ¬y3 ∧ y4 ∧ ¬y5 ∧ y6)
ξ(m'3) = (y1 ∧ ¬y2 ∧ y3 ∧ ¬y4 ∧ y5 ∧ ¬y6)
ω = ¬(ξ(m'1) ∨ ξ(m'2) ∨ ξ(m'3))
-}
brauer11_omega :: CNF.CNF
brauer11_omega =
  CNF.CNF
  { CNF.numVars = 6
  , CNF.numClauses = 3
  , CNF.clauses = map SAT.packClause
      [ [y1, y3, -y4, y5, -y6]
      , [-y1, y2, y3, -y4, y5, -y6]
      , [-y1, y2, -y3, y4, -y5, y6]
      ]
  }
  where
    [y1,y2,y3,y4,y5,y6] = [1..6]

case_ExistentialQuantification_project_phi :: Assertion
case_ExistentialQuantification_project_phi = do
  psi <- ExistentialQuantification.project (IntSet.fromList [7..13]) brauer11_phi
  forM_ (replicateM 6 [False,True]) $ \bs -> do
    let m :: SAT.Model
        m = array (1,13) (zip [1..] bs)    
    b1 <- do
      solver <- SAT.newSolver
      SAT.newVars_ solver (CNF.numVars brauer11_phi)
      forM_ (CNF.clauses brauer11_phi) $ \c -> SAT.addClause solver (SAT.unpackClause c)
      SAT.solveWith solver [if SAT.evalLit m y then y else -y | y <- [1..6]]
    let b2 = all (SAT.evalClause m . SAT.unpackClause) (CNF.clauses psi)
    (b1 == b2) @?= True

case_ExistentialQuantification_project_phi' :: Assertion
case_ExistentialQuantification_project_phi' = do
  let [y1,y2,y3,y4,y5,y6] = [1..6]
      psi = CNF.CNF
            { CNF.numVars = 6
            , CNF.numClauses = 8
            , CNF.clauses = map SAT.packClause
                [ [-y2, y6]
                , [-y3, -y6]
                , [y5, y6]
                , [y3, -y5]
                , [y4, -y6]
                , [y1, y6]
                , [-y1, -y2]
                , [-y4, y6]
                ]
            }
  forM_ (replicateM 6 [False,True]) $ \bs -> do
    let m :: SAT.Model
        m = array (1,13) (zip [1..] bs)
    b1 <- do
      solver <- SAT.newSolver
      SAT.newVars_ solver (CNF.numVars brauer11_phi)
      forM_ (CNF.clauses brauer11_phi) $ \c -> SAT.addClause solver (SAT.unpackClause c)
      SAT.solveWith solver [if SAT.evalLit m y then y else -y | y <- [1..6]]
    let b2 = all (SAT.evalClause m . SAT.unpackClause) (CNF.clauses psi)    
    (b1 == b2) @?= True

case_shortestImplicants_phi :: Assertion
case_shortestImplicants_phi = do
  xss <- ExistentialQuantification.shortestImplicants (IntSet.fromList [1..6]) brauer11_phi
  forM_ (replicateM 6 [False,True]) $ \bs -> do
    let m :: SAT.Model
        m = array (1,6) (zip [1..] bs)
    b1 <- do
      solver <- SAT.newSolver
      SAT.newVars_ solver (CNF.numVars brauer11_phi)
      forM_ (CNF.clauses brauer11_phi) $ \c -> SAT.addClause solver (SAT.unpackClause c)
      SAT.solveWith solver [if SAT.evalLit m y then y else -y | y <- [1..6]]
    let b2 = any (all (SAT.evalLit m) . IntSet.toList) xss
    (b1 == b2) @?= True

case_shortestImplicants_phi' :: Assertion
case_shortestImplicants_phi' = do
  let [y1,y2,y3,y4,y5,y6] = [1..6]
      xss = map IntSet.fromList
            [ [-y1, -y3, y4, -y5, y6]
            , [y1, -y2, -y3, y4, -y5, y6]
            , [y1, -y2, y3, -y4, y5, -y6]
            ]
  forM_ (replicateM 6 [False,True]) $ \bs -> do
    let m :: SAT.Model
        m = array (1,6) (zip [1..] bs)
    b1 <- do
      solver <- SAT.newSolver
      SAT.newVars_ solver (CNF.numVars brauer11_phi)
      forM_ (CNF.clauses brauer11_phi) $ \c -> SAT.addClause solver (SAT.unpackClause c)
      SAT.solveWith solver [if SAT.evalLit m y then y else -y | y <- [1..6]]
    let b2 = any (all (SAT.evalLit m) . IntSet.toList) xss
    (b1 == b2) @?= True

case_shortestImplicants_omega :: Assertion
case_shortestImplicants_omega = do
  xss <- ExistentialQuantification.shortestImplicants (IntSet.fromList [1..6]) brauer11_omega
  forM_ (replicateM 6 [False,True]) $ \bs -> do
    let m :: SAT.Model
        m = array (1,6) (zip [1..] bs)
    b1 <- do
      solver <- SAT.newSolver
      SAT.newVars_ solver (CNF.numVars brauer11_omega)
      forM_ (CNF.clauses brauer11_omega) $ \c -> SAT.addClause solver (SAT.unpackClause c)
      SAT.solveWith solver [if SAT.evalLit m y then y else -y | y <- [1..6]]
    let b2 = any (all (SAT.evalLit m) . IntSet.toList) xss
    unless (b1 == b2) $ print m

case_shortestImplicants_omega' :: Assertion
case_shortestImplicants_omega' = do
  let [y1,y2,y3,y4,y5,y6] = [1..6]
      xss = map IntSet.fromList
              [ [y2, -y6]
              , [y3, y6]
              , [-y5, -y6]
              , [-y3, y5]
              , [-y4, y6]
              , [-y1, -y6]
              , [y1, y2]
              , [y4, -y6]
              ]
  forM_ (replicateM 6 [False,True]) $ \bs -> do
    let m :: SAT.Model
        m = array (1,6) (zip [1..] bs)
    b1 <- do
      solver <- SAT.newSolver
      SAT.newVars_ solver (CNF.numVars brauer11_omega)
      forM_ (CNF.clauses brauer11_omega) $ \c -> SAT.addClause solver (SAT.unpackClause c)
      SAT.solveWith solver [if SAT.evalLit m y then y else -y | y <- [1..6]]
    let b2 = any (all (SAT.evalLit m) . IntSet.toList) xss
    (b1 == b2) @?= True

------------------------------------------------------------------------


prop_pb2sat :: Property
prop_pb2sat = QM.monadicIO $ do
  pb@(nv,cs) <- QM.pick arbitraryPB
  let f (PBRelGE,lhs,rhs) = ([(c,[l]) | (c,l) <- lhs], PBFile.Ge, rhs)
      f (PBRelLE,lhs,rhs) = ([(-c,[l]) | (c,l) <- lhs], PBFile.Ge, -rhs)
      f (PBRelEQ,lhs,rhs) = ([(c,[l]) | (c,l) <- lhs], PBFile.Eq, rhs)
  let opb = PBFile.Formula
            { PBFile.pbObjectiveFunction = Nothing
            , PBFile.pbNumVars = nv
            , PBFile.pbNumConstraints = length cs
            , PBFile.pbConstraints = map f cs
            }
  let (cnf, mforth, mback) = PB2SAT.convert opb

  solver1 <- arbitrarySolver
  solver2 <- arbitrarySolver
  ret1 <- QM.run $ solvePB solver1 pb
  ret2 <- QM.run $ solveCNF solver2 cnf
  QM.assert $ isJust ret1 == isJust ret2
  case ret1 of
    Nothing -> return ()
    Just m1 -> do
      let m2 = mforth m1
      QM.assert $ bounds m2 == (1, CNF.numVars cnf)
      QM.assert $ evalCNF m2 cnf
  case ret2 of
    Nothing -> return ()
    Just m2 -> do
      let m1 = mback m2
      QM.assert $ bounds m1 == (1, nv)
      QM.assert $ evalPB m1 pb

prop_wbo2maxsat :: Property
prop_wbo2maxsat = QM.monadicIO $ do
  wbo1@(nv,cs,top) <- QM.pick arbitraryWBO
  let f (w,(PBRelGE,lhs,rhs)) = (w,([(c,[l]) | (c,l) <- lhs], PBFile.Ge, rhs))
      f (w,(PBRelLE,lhs,rhs)) = (w,([(-c,[l]) | (c,l) <- lhs], PBFile.Ge, -rhs))
      f (w,(PBRelEQ,lhs,rhs)) = (w,([(c,[l]) | (c,l) <- lhs], PBFile.Eq, rhs))
  let wbo1' = PBFile.SoftFormula
            { PBFile.wboNumVars = nv
            , PBFile.wboNumConstraints = length cs
            , PBFile.wboConstraints = map f cs
            , PBFile.wboTopCost = top
            }
  let (wcnf, mforth, mback) = WBO2MaxSAT.convert wbo1'
      wbo2 = ( MaxSAT.numVars wcnf
             , [ ( if w == MaxSAT.topCost wcnf then Nothing else Just w
                 , (PBRelGE, [(1,l) | l <- SAT.unpackClause clause], 1)
                 )
               | (w,clause) <- MaxSAT.clauses wcnf
               ]
             , Nothing
             )

  solver1 <- arbitrarySolver
  solver2 <- arbitrarySolver
  method <- QM.pick arbitrary
  ret1 <- QM.run $ optimizeWBO solver1 method wbo1
  ret2 <- QM.run $ optimizeWBO solver2 method wbo2
  QM.assert $ isJust ret1 == isJust ret2
  case ret1 of
    Nothing -> return ()
    Just (m1,val) -> do
      let m2 = mforth m1
      QM.assert $ bounds m2 == (1, MaxSAT.numVars wcnf)
      QM.assert $ evalWBO m2 wbo2 == Just val
  case ret2 of
    Nothing -> return ()
    Just (m2,val) -> do
      let m1 = mback m2
      QM.assert $ bounds m1 == (1, nv)
      QM.assert $ evalWBO m1 wbo1 == Just val

prop_wbo2pb :: Property
prop_wbo2pb = QM.monadicIO $ do
  wbo@(nv,cs,top) <- QM.pick arbitraryWBO
  let f (w,(PBRelGE,lhs,rhs)) = (w,([(c,[l]) | (c,l) <- lhs], PBFile.Ge, rhs))
      f (w,(PBRelLE,lhs,rhs)) = (w,([(-c,[l]) | (c,l) <- lhs], PBFile.Ge, -rhs))
      f (w,(PBRelEQ,lhs,rhs)) = (w,([(c,[l]) | (c,l) <- lhs], PBFile.Eq, rhs))
  let wbo' = PBFile.SoftFormula
            { PBFile.wboNumVars = nv
            , PBFile.wboNumConstraints = length cs
            , PBFile.wboConstraints = map f cs
            , PBFile.wboTopCost = top
            }
  let (opb, mforth, mback) = WBO2PB.convert wbo'
      obj = fromMaybe [] $ PBFile.pbObjectiveFunction opb
      f (lhs, PBFile.Ge, rhs) = (PBRelGE, lhs, rhs)
      f (lhs, PBFile.Eq, rhs) = (PBRelEQ, lhs, rhs)
      cs2 = map f (PBFile.pbConstraints opb)
      pb = (PBFile.pbNumVars opb, obj, cs2)

  solver1 <- arbitrarySolver
  solver2 <- arbitrarySolver
  method <- QM.pick arbitrary
  ret1 <- QM.run $ optimizeWBO solver1 method wbo
  ret2 <- QM.run $ optimizePBNLC solver2 method pb
  QM.assert $ isJust ret1 == isJust ret2
  case ret1 of
    Nothing -> return ()
    Just (m1,val1) -> do
      let m2 = mforth m1
      QM.assert $ bounds m2 == (1, PBFile.pbNumVars opb)
      QM.assert $ evalPBNLC m2 (PBFile.pbNumVars opb, cs2)
      QM.assert $ SAT.evalPBSum m2 obj == val1
  case ret2 of
    Nothing -> return ()
    Just (m2,val2) -> do
      let m1 = mback m2
      QM.assert $ bounds m1 == (1,nv)
      QM.assert $ evalWBO m1 wbo == Just val2

prop_sat2ksat :: Property
prop_sat2ksat = QM.monadicIO $ do
  k <- QM.pick $ choose (3,10)

  cnf1 <- QM.pick arbitraryCNF
  let (cnf2, mforth, mback) = SAT2KSAT.convert k cnf1

  solver1 <- arbitrarySolver
  solver2 <- arbitrarySolver
  ret1 <- QM.run $ solveCNF solver1 cnf1
  ret2 <- QM.run $ solveCNF solver2 cnf2
  QM.assert $ isJust ret1 == isJust ret2
  case ret1 of
    Nothing -> return ()
    Just m1 -> do
      let m2 = mforth m1
      QM.assert $ bounds m2 == (1, CNF.numVars cnf2)
      QM.assert $ evalCNF m2 cnf2
  case ret2 of
    Nothing -> return ()
    Just m2 -> do
      let m1 = mback m2
      QM.assert $ bounds m1 == (1, CNF.numVars cnf1)
      QM.assert $ evalCNF m1 cnf1

------------------------------------------------------------------------

instance Arbitrary SAT.LearningStrategy where
  arbitrary = arbitraryBoundedEnum

instance Arbitrary SAT.RestartStrategy where
  arbitrary = arbitraryBoundedEnum

instance Arbitrary SAT.BranchingStrategy where
  arbitrary = arbitraryBoundedEnum

instance Arbitrary SAT.PBHandlerType where
  arbitrary = arbitraryBoundedEnum

instance Arbitrary SAT.Config where
  arbitrary = do
    restartStrategy <- arbitrary
    restartFirst <- arbitrary
    restartInc <- liftM ((1.01 +) . abs) arbitrary
    learningStrategy <- arbitrary
    learntSizeFirst <- arbitrary
    learntSizeInc <- liftM ((1.01 +) . abs) arbitrary
    branchingStrategy <- arbitrary
    erwaStepSizeFirst <- choose (0, 1)
    erwaStepSizeMin   <- choose (0, 1)
    erwaStepSizeDec   <- choose (0, 1)
    pbhandler <- arbitrary
    ccmin <- choose (0,2)
    phaseSaving <- arbitrary
    forwardSubsumptionRemoval <- arbitrary
    backwardSubsumptionRemoval <- arbitrary
    randomFreq <- choose (0,1)
    splitClausePart <- arbitrary
    return $ def
      { SAT.configRestartStrategy = restartStrategy
      , SAT.configRestartFirst = restartFirst
      , SAT.configRestartInc = restartInc
      , SAT.configLearningStrategy = learningStrategy
      , SAT.configLearntSizeFirst = learntSizeFirst
      , SAT.configLearntSizeInc = learntSizeInc
      , SAT.configPBHandlerType = pbhandler
      , SAT.configCCMin = ccmin
      , SAT.configBranchingStrategy = branchingStrategy
      , SAT.configERWAStepSizeFirst = erwaStepSizeFirst
      , SAT.configERWAStepSizeDec   = erwaStepSizeDec
      , SAT.configERWAStepSizeMin   = erwaStepSizeMin
      , SAT.configEnablePhaseSaving = phaseSaving
      , SAT.configEnableForwardSubsumptionRemoval = forwardSubsumptionRemoval
      , SAT.configEnableBackwardSubsumptionRemoval = backwardSubsumptionRemoval
      , SAT.configRandomFreq = randomFreq
      , SAT.configEnablePBSplitClausePart = splitClausePart
      }

arbitrarySolver :: QM.PropertyM IO SAT.Solver
arbitrarySolver = do
  seed <- QM.pick arbitrary
  config <- QM.pick arbitrary
  QM.run $ do
    solver <- SAT.newSolverWithConfig config{ SAT.configCheckModel = True }
    SAT.setRandomGen solver =<< Rand.initialize (V.singleton seed)
    return solver

arbitraryOptimizer :: SAT.Solver -> SAT.PBLinSum -> QM.PropertyM IO PBO.Optimizer
arbitraryOptimizer solver obj = do
  method <- QM.pick arbitrary
  QM.run $ do
    opt <- PBO.newOptimizer solver obj
    PBO.setMethod opt method
    return opt

instance Arbitrary PBO.Method where
  arbitrary = arbitraryBoundedEnum

instance Arbitrary PB.Strategy where
  arbitrary = arbitraryBoundedEnum

-- ---------------------------------------------------------------------

#if !MIN_VERSION_QuickCheck(2,8,0)
sublistOf :: [a] -> Gen [a]
sublistOf xs = filterM (\_ -> choose (False, True)) xs
#endif

------------------------------------------------------------------------
-- Test harness

satTestGroup :: TestTree
satTestGroup = $(testGroupGenerator)
