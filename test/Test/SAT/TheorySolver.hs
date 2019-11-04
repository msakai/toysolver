{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
module Test.SAT.TheorySolver (satTheorySolverTestGroup) where

import Control.Monad
import Data.IORef
import Data.Map (Map)
import qualified Data.Map as Map
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import qualified Data.IntSet as IntSet
import qualified Data.Traversable as Traversable

import Test.Tasty
import Test.Tasty.QuickCheck hiding ((.&&.), (.||.))
import Test.Tasty.HUnit
import Test.Tasty.TH
import qualified Test.QuickCheck.Monadic as QM

import ToySolver.Data.BoolExpr
import ToySolver.Data.Boolean
import qualified ToySolver.SAT as SAT
import ToySolver.SAT.TheorySolver
import qualified ToySolver.SAT.Encoder.Tseitin as Tseitin
import qualified ToySolver.FileFormat.CNF as CNF
import ToySolver.Data.OrdRel
import qualified ToySolver.Data.LA as LA
import qualified ToySolver.Arith.Simplex as Simplex
import qualified ToySolver.EUF.EUFSolver as EUF

import Test.SAT.Utils


newTheorySolver :: CNF.CNF -> IO TheorySolver
newTheorySolver cnf = do
  let nv = CNF.cnfNumVars cnf
      cs = CNF.cnfClauses cnf
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
  let nv = CNF.cnfNumVars cnf
      nc = CNF.cnfNumClauses cnf
      cs = CNF.cnfClauses cnf
      cnf1 = cnf{ CNF.cnfClauses = [c | (i,c) <- zip [(0::Int)..] cs, i `mod` 2 == 0], CNF.cnfNumClauses = nc - (nc `div` 2) }
      cnf2 = cnf{ CNF.cnfClauses = [c | (i,c) <- zip [(0::Int)..] cs, i `mod` 2 /= 0], CNF.cnfNumClauses = nc `div` 2 }

  solver <- arbitrarySolver

  ret <- QM.run $ do
    SAT.newVars_ solver nv

    tsolver <- newTheorySolver cnf1
    SAT.setTheory solver tsolver

    forM_ (CNF.cnfClauses cnf2) $ \c -> SAT.addClause solver (SAT.unpackClause c)
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
                  _ <- callback v
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

  cTrue  <- EUF.newConst eufSolver
  cFalse <- EUF.newConst eufSolver
  EUF.assertNotEqual eufSolver cTrue cFalse
  boolToTermRef <- newIORef (IntMap.empty :: IntMap EUF.Term)
  termToBoolRef <- newIORef (Map.empty :: Map EUF.Term SAT.Lit)

  let connectBoolTerm :: SAT.Lit -> EUF.Term -> IO ()
      connectBoolTerm lit t = do
        lit1 <- abstractEUFAtom (t, cTrue)
        lit2 <- abstractEUFAtom (t, cFalse)
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
    ftt <- abstractEUFAtom (f cTrue, cTrue)
    ret <- SAT.solveWith satSolver [-fx, ftt]
    ret @?= True

    m1 <- SAT.getModel satSolver
    m2 <- readIORef eufModelRef
    let e (Left lit) = SAT.evalLit m1 lit
        e (Right (lhs,rhs)) = EUF.eval m2 lhs == EUF.eval m2 rhs
    fold e (notB (Atom (Left fx)) .||. (Atom (Right (f cTrue, cTrue)))) @?= True
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


satTheorySolverTestGroup :: TestTree
satTheorySolverTestGroup = $(testGroupGenerator)
