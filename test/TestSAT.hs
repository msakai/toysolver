{-# LANGUAGE TemplateHaskell #-}
module Main (main) where

import Control.Monad
import Data.Array.IArray
import Data.IORef
import Data.List
import Data.Set (Set)
import qualified Data.Set as Set
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import qualified System.Random as Rand

import Test.Tasty
import Test.Tasty.QuickCheck hiding ((.&&.), (.||.))
import Test.Tasty.HUnit
import Test.Tasty.TH
import qualified Test.QuickCheck.Monadic as QM

import ToySolver.Data.LBool
import ToySolver.Data.BoolExpr
import ToySolver.Data.Boolean
import ToySolver.SAT
import ToySolver.SAT.Types
import ToySolver.SAT.TheorySolver
import qualified ToySolver.SAT.TseitinEncoder as Tseitin
import qualified ToySolver.SAT.MUS as MUS
import qualified ToySolver.SAT.MUS.QuickXplain as QuickXplain
import qualified ToySolver.SAT.MUS.CAMUS as CAMUS
import qualified ToySolver.SAT.MUS.DAA as DAA
import qualified ToySolver.SAT.PBO as PBO
import qualified ToySolver.SAT.PBNLC as PBNLC

prop_solveCNF :: Property
prop_solveCNF = QM.monadicIO $ do
  cnf@(nv,_) <- QM.pick arbitraryCNF
  solver <- arbitrarySolver
  ret <- QM.run $ solveCNF solver cnf
  case ret of
    Just m -> QM.assert $ evalCNF m cnf == True
    Nothing -> do
      forM_ [array (1,nv) (zip [1..nv] xs) | xs <- replicateM nv [True,False]] $ \m -> do
        QM.assert $ evalCNF m cnf == False

solveCNF :: Solver -> (Int,[Clause]) -> IO (Maybe Model)
solveCNF solver (nv,cs) = do
  newVars_ solver nv
  forM_ cs $ \c -> addClause solver c
  ret <- solve solver
  if ret then do
    m <- getModel solver
    return (Just m)
  else do
    return Nothing

arbitraryCNF :: Gen (Int,[Clause])
arbitraryCNF = do
  nv <- choose (0,10)
  nc <- choose (0,50)
  cs <- replicateM nc $ do
    len <- choose (0,10)
    if nv == 0 then
      return []
    else
      replicateM len $ choose (-nv, nv) `suchThat` (/= 0)
  return (nv, cs)

evalCNF :: Model -> (Int,[Clause]) -> Bool
evalCNF m (_,cs) = all (evalClause m) cs


prop_solvePB :: Property
prop_solvePB = QM.monadicIO $ do
  prob@(nv,_) <- QM.pick arbitraryPB
  solver <- arbitrarySolver
  ret <- QM.run $ solvePB solver prob
  case ret of
    Just m -> QM.assert $ evalPB m prob == True
    Nothing -> do
      forM_ [array (1,nv) (zip [1..nv] xs) | xs <- replicateM nv [True,False]] $ \m -> do
        QM.assert $ evalPB m prob == False

data PBRel = PBRelGE | PBRelEQ | PBRelLE deriving (Eq, Ord, Enum, Bounded, Show)

instance Arbitrary PBRel where
  arbitrary = arbitraryBoundedEnum  

evalPBRel :: Ord a => PBRel -> a -> a -> Bool
evalPBRel PBRelGE = (>=)
evalPBRel PBRelLE = (<=)
evalPBRel PBRelEQ = (==)

solvePB :: Solver -> (Int,[(PBRel,PBLinSum,Integer)]) -> IO (Maybe Model)
solvePB solver (nv,cs) = do
  newVars_ solver nv
  forM_ cs $ \(o,lhs,rhs) -> do
    case o of
      PBRelGE -> addPBAtLeast solver lhs rhs
      PBRelLE -> addPBAtMost solver lhs rhs
      PBRelEQ -> addPBExactly solver lhs rhs
  ret <- solve solver
  if ret then do
    m <- getModel solver
    return (Just m)
  else do
    return Nothing

arbitraryPB :: Gen (Int,[(PBRel,PBLinSum,Integer)])
arbitraryPB = do
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
          l <- choose (-nv, nv) `suchThat` (/= 0)
          c <- arbitrary
          return (c,l)
    rhs <- arbitrary
    return $ (rel,lhs,rhs)
  return (nv, cs)

evalPB :: Model -> (Int,[(PBRel,PBLinSum,Integer)]) -> Bool
evalPB m (_,cs) = all (\(o,lhs,rhs) -> evalPBRel o (evalPBLinSum m lhs) rhs) cs


prop_solvePBNLC :: Property
prop_solvePBNLC = QM.monadicIO $ do
  prob@(nv,_) <- QM.pick arbitraryPBNLC
  solver <- arbitrarySolver
  ret <- QM.run $ solvePBNLC solver prob
  case ret of
    Just m -> QM.assert $ evalPBNLC m prob == True
    Nothing -> do
      forM_ [array (1,nv) (zip [1..nv] xs) | xs <- replicateM nv [True,False]] $ \m -> do
        QM.assert $ evalPBNLC m prob == False

solvePBNLC :: Solver -> (Int,[(PBRel,PBNLC.PBSum,Integer)]) -> IO (Maybe Model)
solvePBNLC solver (nv,cs) = do
  newVars_ solver nv
  enc <- Tseitin.newEncoder solver
  forM_ cs $ \(o,lhs,rhs) -> do
    case o of
      PBRelGE -> PBNLC.addPBAtLeast enc lhs rhs
      PBRelLE -> PBNLC.addPBAtMost enc lhs rhs
      PBRelEQ -> PBNLC.addPBExactly enc lhs rhs
  ret <- solve solver
  if ret then do
    m <- getModel solver
    return (Just m)
  else do
    return Nothing

arbitraryPBNLC :: Gen (Int,[(PBRel,PBNLC.PBSum,Integer)])
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

evalPBNLC :: Model -> (Int,[(PBRel,PBNLC.PBSum,Integer)]) -> Bool
evalPBNLC m (_,cs) = all (\(o,lhs,rhs) -> evalPBRel o (PBNLC.evalPBSum m lhs) rhs) cs


prop_solveXOR :: Property
prop_solveXOR = QM.monadicIO $ do
  prob@(nv,_) <- QM.pick arbitraryXOR
  solver <- arbitrarySolver
  ret <- QM.run $ solveXOR solver prob
  case ret of
    Just m -> QM.assert $ evalXOR m prob == True
    Nothing -> do
      forM_ [array (1,nv) (zip [1..nv] xs) | xs <- replicateM nv [True,False]] $ \m -> do
        QM.assert $ evalXOR m prob == False

solveXOR :: Solver -> (Int,[XORClause]) -> IO (Maybe Model)
solveXOR solver (nv,cs) = do
  setCheckModel solver True
  newVars_ solver nv
  forM_ cs $ \c -> addXORClause solver (fst c) (snd c)
  ret <- solve solver
  if ret then do
    m <- getModel solver
    return (Just m)
  else do
    return Nothing

arbitraryXOR :: Gen (Int,[XORClause])
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

evalXOR :: Model -> (Int,[XORClause]) -> Bool
evalXOR m (_,cs) = all (evalXORClause m) cs


newTheorySolver :: (Int, [Clause]) -> IO TheorySolver
newTheorySolver cnf@(nv,cs) = do
  solver <- newSolver
  newVars_ solver nv
  forM_ cs $ \c -> addClause solver c
  
  ref <- newIORef []
  let tsolver =
        TheorySolver
        { thAssertLit = \_ l -> do
            if abs l > nv then
              return True
            else do
              m <- readIORef ref
              case m of
                [] -> addClause solver [l]
                xs : xss -> writeIORef ref ((l : xs) : xss)
              return True
        , thCheck = \_ -> do
            xs <- liftM concat $ readIORef ref
            solveWith solver xs
        , thExplain = \m -> do
            case m of
              Nothing -> do
                ls <- getFailedAssumptions solver
                return [-l | l <- ls]
              Just _ -> return []
        , thPushBacktrackPoint = modifyIORef ref ([] :)
        , thPopBacktrackPoint = modifyIORef ref tail
        }
  return tsolver

prop_solveCNF_using_BooleanTheory :: Property
prop_solveCNF_using_BooleanTheory = QM.monadicIO $ do
  cnf@(nv,cs) <- QM.pick arbitraryCNF
  let cnf1 = (nv, [c | (i,c) <- zip [0..] cs, i `mod` 2 == 0])
      cnf2 = (nv, [c | (i,c) <- zip [0..] cs, i `mod` 2 /= 0])

  solver <- arbitrarySolver

  ret <- QM.run $ do
    newVars_ solver nv

    tsolver <- newTheorySolver cnf1
    setTheory solver tsolver

    forM_ (snd cnf2) $ \c -> addClause solver c
    ret <- solve solver
    if ret then do
      m <- getModel solver
      return (Just m)
    else do
      return Nothing

  case ret of
    Just m -> QM.assert $ evalCNF m cnf == True
    Nothing -> do
      forM_ [array (1,nv) (zip [1..nv] xs) | xs <- replicateM nv [True,False]] $ \m -> do
        QM.assert $ evalCNF m cnf == False

-- should be SAT
case_solve_SAT :: IO ()
case_solve_SAT = do
  solver <- newSolver
  x1 <- newVar solver
  x2 <- newVar solver
  addClause solver [literal x1 True,  literal x2 True]  -- x1 or x2
  addClause solver [literal x1 True,  literal x2 False] -- x1 or not x2
  addClause solver [literal x1 False, literal x2 False] -- not x1 or not x2
  ret <- solve solver
  ret @?= True

-- shuld be UNSAT
case_solve_UNSAT :: IO ()
case_solve_UNSAT = do
  solver <- newSolver
  x1 <- newVar solver
  x2 <- newVar solver
  addClause solver [literal x1 True,  literal x2 True]  -- x1 or x2
  addClause solver [literal x1 False, literal x2 True]  -- not x1 or x2
  addClause solver [literal x1 True,  literal x2 False] -- x1 or not x2
  addClause solver [literal x1 False, literal x2 False] -- not x2 or not x2
  ret <- solve solver
  ret @?= False

-- top level でいきなり矛盾
case_root_inconsistent :: IO ()
case_root_inconsistent = do
  solver <- newSolver
  x1 <- newVar solver
  addClause solver [literal x1 True]
  addClause solver [literal x1 False]
  ret <- solve solver -- unsat
  ret @?= False

-- incremental に制約を追加
case_incremental_solving :: IO ()
case_incremental_solving = do
  solver <- newSolver
  x1 <- newVar solver
  x2 <- newVar solver
  addClause solver [literal x1 True,  literal x2 True]  -- x1 or x2
  addClause solver [literal x1 True,  literal x2 False] -- x1 or not x2
  addClause solver [literal x1 False, literal x2 False] -- not x1 or not x2
  ret <- solve solver -- sat
  ret @?= True

  addClause solver [literal x1 False, literal x2 True]  -- not x1 or x2
  ret <- solve solver -- unsat
  ret @?= False

-- 制約なし
case_empty_constraint :: IO ()
case_empty_constraint = do
  solver <- newSolver
  ret <- solve solver
  ret @?= True

-- 空の節
case_empty_claue :: IO ()
case_empty_claue = do
  solver <- newSolver
  addClause solver []
  ret <- solve solver
  ret @?= False

-- 自明に真な節
case_excluded_middle_claue :: IO ()
case_excluded_middle_claue = do
  solver <- newSolver
  x1 <- newVar solver
  addClause solver [x1, -x1] -- x1 or not x1
  ret <- solve solver
  ret @?= True

-- 冗長な節
case_redundant_clause :: IO ()
case_redundant_clause = do
  solver <- newSolver
  x1 <- newVar solver
  addClause solver [x1,x1] -- x1 or x1
  ret <- solve solver
  ret @?= True

case_instantiateClause :: IO ()
case_instantiateClause = do
  solver <- newSolver
  x1 <- newVar solver
  x2 <- newVar solver
  addClause solver [x1]
  addClause solver [x1,x2]
  addClause solver [-x1,x2]
  ret <- solve solver
  ret @?= True

case_instantiateAtLeast :: IO ()
case_instantiateAtLeast = do
  solver <- newSolver
  x1 <- newVar solver
  x2 <- newVar solver
  x3 <- newVar solver
  x4 <- newVar solver
  addClause solver [x1]

  addAtLeast solver [x1,x2,x3,x4] 2
  ret <- solve solver
  ret @?= True

  addAtLeast solver [-x1,-x2,-x3,-x4] 2
  ret <- solve solver
  ret @?= True

case_inconsistent_AtLeast :: IO ()
case_inconsistent_AtLeast = do
  solver <- newSolver
  x1 <- newVar solver
  x2 <- newVar solver
  addAtLeast solver [x1,x2] 3
  ret <- solve solver -- unsat
  ret @?= False

case_trivial_AtLeast :: IO ()
case_trivial_AtLeast = do
  solver <- newSolver
  x1 <- newVar solver
  x2 <- newVar solver
  addAtLeast solver [x1,x2] 0
  ret <- solve solver
  ret @?= True

  solver <- newSolver
  x1 <- newVar solver
  x2 <- newVar solver
  addAtLeast solver [x1,x2] (-1)
  ret <- solve solver
  ret @?= True

case_AtLeast_1 :: IO ()
case_AtLeast_1 = do
  solver <- newSolver
  x1 <- newVar solver
  x2 <- newVar solver
  x3 <- newVar solver
  addAtLeast solver [x1,x2,x3] 2
  addAtLeast solver [-x1,-x2,-x3] 2
  ret <- solve solver -- unsat
  ret @?= False

case_AtLeast_2 :: IO ()
case_AtLeast_2 = do
  solver <- newSolver
  x1 <- newVar solver
  x2 <- newVar solver
  x3 <- newVar solver
  x4 <- newVar solver
  addAtLeast solver [x1,x2,x3,x4] 2
  addClause solver [-x1,-x2]
  addClause solver [-x1,-x3]
  ret <- solve solver
  ret @?= True

case_AtLeast_3 :: IO ()
case_AtLeast_3 = do
  forM_ [(-1) .. 3] $ \n -> do
    solver <- newSolver
    x1 <- newVar solver
    x2 <- newVar solver
    addAtLeast solver [x1,x2] n
    ret <- solve solver
    assertEqual ("case_AtLeast3_" ++ show n) (n <= 2) ret

-- from http://www.cril.univ-artois.fr/PB11/format.pdf
case_PB_sample1 :: IO ()
case_PB_sample1 = do
  solver <- newSolver

  x1 <- newVar solver
  x2 <- newVar solver
  x3 <- newVar solver
  x4 <- newVar solver
  x5 <- newVar solver

  addPBAtLeast solver [(1,x1),(4,x2),(-2,x5)] 2
  addPBAtLeast solver [(-1,x1),(4,x2),(-2,x5)] 3
  addPBAtLeast solver [(12345678901234567890,x4),(4,x3)] 10
  addPBExactly solver [(2,x2),(3,x4),(2,x1),(3,x5)] 5

  ret <- solve solver
  ret @?= True

-- 一部の変数を否定に置き換えたもの
case_PB_sample1' :: IO ()
case_PB_sample1' = do
  solver <- newSolver

  x1 <- newVar solver
  x2 <- newVar solver
  x3 <- newVar solver
  x4 <- newVar solver
  x5 <- newVar solver

  addPBAtLeast solver [(1,x1),(4,-x2),(-2,x5)] 2
  addPBAtLeast solver [(-1,x1),(4,-x2),(-2,x5)] 3
  addPBAtLeast solver [(12345678901234567890,-x4),(4,x3)] 10
  addPBExactly solver [(2,-x2),(3,-x4),(2,x1),(3,x5)] 5

  ret <- solve solver
  ret @?= True

-- いきなり矛盾したPB制約
case_root_inconsistent_PB :: IO ()
case_root_inconsistent_PB = do
  solver <- newSolver
  x1 <- newVar solver
  x2 <- newVar solver
  addPBAtLeast solver [(2,x1),(3,x2)] 6
  ret <- solve solver
  ret @?= False

case_pb_propagate :: IO ()
case_pb_propagate = do
  solver <- newSolver
  x1 <- newVar solver
  x2 <- newVar solver
  addPBAtLeast solver [(1,x1),(3,x2)] 3
  addClause solver [-x1]
  ret <- solve solver
  ret @?= True

case_solveWith_1 :: IO ()
case_solveWith_1 = do
  solver <- newSolver
  x1 <- newVar solver
  x2 <- newVar solver
  x3 <- newVar solver
  addClause solver [x1, x2]       -- x1 or x2
  addClause solver [x1, -x2]      -- x1 or not x2
  addClause solver [-x1, -x2]     -- not x1 or not x2
  addClause solver [-x3, -x1, x2] -- not x3 or not x1 or x2

  ret <- solve solver -- sat
  ret @?= True

  ret <- solveWith solver [x3] -- unsat
  ret @?= False

  ret <- solve solver -- sat
  ret @?= True

case_solveWith_2 :: IO ()
case_solveWith_2 = do
  solver <- newSolver
  x1 <- newVar solver
  x2 <- newVar solver
  addClause solver [-x1, x2] -- -x1 or x2
  addClause solver [x1]      -- x1

  ret <- solveWith solver [x2]
  ret @?= True

  ret <- solveWith solver [-x2]
  ret @?= False

case_getVarFixed :: IO ()
case_getVarFixed = do
  solver <- newSolver
  x1 <- newVar solver
  x2 <- newVar solver
  addClause solver [x1,x2]

  ret <- getVarFixed solver x1
  ret @?= lUndef

  addClause solver [-x1]
  
  ret <- getVarFixed solver x1
  ret @?= lFalse

  ret <- getLitFixed solver (-x1)
  ret @?= lTrue

  ret <- getLitFixed solver x2
  ret @?= lTrue

case_getAssumptionsImplications_case1 :: IO ()
case_getAssumptionsImplications_case1 = do
  solver <- newSolver
  x1 <- newVar solver
  x2 <- newVar solver
  x3 <- newVar solver
  addClause solver [x1,x2,x3]

  addClause solver [-x1]
  ret <- solveWith solver [-x2]
  ret @?= True
  xs <- getAssumptionsImplications solver
  xs @?= [x3]

prop_getAssumptionsImplications :: Property
prop_getAssumptionsImplications = QM.monadicIO $ do
  cnf@(nv,cs) <- QM.pick arbitraryCNF
  solver <- arbitrarySolver
  ls <- QM.pick $ liftM concat $ mapM (\v -> elements [[],[-v],[v]]) [1..nv]
  ret <- QM.run $ do
    newVars_ solver nv
    forM_ cs $ \c -> addClause solver c
    solveWith solver ls
  when ret $ do
    xs <- QM.run $ getAssumptionsImplications solver
    forM_ xs $ \x -> do
      ret2 <- QM.run $ solveWith solver (-x : ls)
      QM.assert $ ret2 == False

------------------------------------------------------------------------

-- -4*(not x1) + 3*x1 + 10*(not x2)
-- = -4*(1 - x1) + 3*x1 + 10*(not x2)
-- = -4 + 4*x1 + 3*x1 + 10*(not x2)
-- = 7*x1 + 10*(not x2) - 4
case_normalizePBLinSum :: Assertion
case_normalizePBLinSum = do
  sort e @?= sort [(7,x1),(10,-x2)]
  c @?= -4
  where
    x1 = 1
    x2 = 2
    (e,c) = normalizePBLinSum ([(-4,-x1),(3,x1),(10,-x2)], 0)

-- -4*(not x1) + 3*x1 + 10*(not x2) >= 3
-- ⇔ -4*(1 - x1) + 3*x1 + 10*(not x2) >= 3
-- ⇔ -4 + 4*x1 + 3*x1 + 10*(not x2) >= 3
-- ⇔ 7*x1 + 10*(not x2) >= 7
-- ⇔ 7*x1 + 7*(not x2) >= 7
-- ⇔ x1 + (not x2) >= 1
case_normalizePBLinAtLeast :: Assertion
case_normalizePBLinAtLeast = (sort lhs, rhs) @?= (sort [(1,x1),(1,-x2)], 1)
  where
    x1 = 1
    x2 = 2
    (lhs,rhs) = normalizePBLinAtLeast ([(-4,-x1),(3,x1),(10,-x2)], 3)

case_normalizePBLinExactly_1 :: Assertion
case_normalizePBLinExactly_1 = (sort lhs, rhs) @?= (sort [(3,x1),(2,x2)], 1)
  where
    x1 = 1
    x2 = 2
    (lhs,rhs) = normalizePBLinExactly ([(6,x1),(4,x2)], 2)

case_normalizePBLinExactly_2 :: Assertion
case_normalizePBLinExactly_2 = (sort lhs, rhs) @?= ([], 1)
  where
    x1 = 1
    x2 = 2
    x3 = 3
    (lhs,rhs) = normalizePBLinExactly ([(2,x1),(2,x2),(2,x3)], 3)

case_cutResolve_1 :: Assertion
case_cutResolve_1 = (sort lhs, rhs) @?= (sort [(1,x3),(1,x4)], 1)
  where
    x1 = 1
    x2 = 2
    x3 = 3
    x4 = 4
    pb1 = ([(1,x1), (1,x2), (1,x3)], 1)
    pb2 = ([(2,-x1), (2,-x2), (1,x4)], 3)
    (lhs,rhs) = cutResolve pb1 pb2 x1

case_cutResolve_2 :: Assertion
case_cutResolve_2 = (sort lhs, rhs) @?= (sort [(3,x1),(2,-x2),(2,x4)], 3)
  where
    x1 = 1
    x2 = 2
    x3 = 3
    x4 = 4
    pb1 = ([(3,x1), (2,-x2), (1,x3), (1,x4)], 3)
    pb2 = ([(1,-x3), (1,x4)], 1)
    (lhs,rhs) = cutResolve pb1 pb2 x3

case_cardinalityReduction :: Assertion
case_cardinalityReduction = (sort lhs, rhs) @?= ([1,2,3,4,5],4)
  where
    (lhs, rhs) = cardinalityReduction ([(6,1),(5,2),(4,3),(3,4),(2,5),(1,6)], 17)

case_pbSubsume_clause :: Assertion
case_pbSubsume_clause = pbSubsume ([(1,1),(1,-3)],1) ([(1,1),(1,2),(1,-3),(1,4)],1) @?= True

case_pbSubsume_1 :: Assertion
case_pbSubsume_1 = pbSubsume ([(1,1),(1,2),(1,-3)],2) ([(1,1),(2,2),(1,-3),(1,4)],1) @?= True

case_pbSubsume_2 :: Assertion
case_pbSubsume_2 = pbSubsume ([(1,1),(1,2),(1,-3)],2) ([(1,1),(2,2),(1,-3),(1,4)],3) @?= False

------------------------------------------------------------------------

case_normalizeXORClause_False =
  normalizeXORClause ([],True) @?= ([],True)

case_normalizeXORClause_True =
  normalizeXORClause ([],False) @?= ([],False)

-- x ⊕ y ⊕ x = y
case_normalizeXORClause_case1 =
  normalizeXORClause ([1,2,1],True) @?= ([2],True)

-- x ⊕ ¬x = x ⊕ x ⊕ 1 = 1
case_normalizeXORClause_case2 =
  normalizeXORClause ([1,-1],True) @?= ([],False)

case_evalXORClause_case1 =
  evalXORClause (array (1,2) [(1,True),(2,True)] :: Array Int Bool) ([1,2], True) @?= False

case_evalXORClause_case2 =
  evalXORClause (array (1,2) [(1,False),(2,True)] :: Array Int Bool) ([1,2], True) @?= True

case_xor_case1 = do
  solver <- newSolver
  setCheckModel solver True
  x1 <- newVar solver
  x2 <- newVar solver
  x3 <- newVar solver
  addXORClause solver [x1, x2] True -- x1 ⊕ x2 = True
  addXORClause solver [x2, x3] True -- x2 ⊕ x3 = True
  addXORClause solver [x3, x1] True -- x3 ⊕ x1 = True
  ret <- solve solver
  ret @?= False

case_xor_case2 = do
  solver <- newSolver
  setCheckModel solver True
  x1 <- newVar solver
  x2 <- newVar solver
  x3 <- newVar solver
  addXORClause solver [x1, x2] True -- x1 ⊕ x2 = True
  addXORClause solver [x1, x3] True -- x1 ⊕ x3 = True
  addClause solver [x2]

  ret <- solve solver
  ret @?= True
  m <- getModel solver
  m ! x1 @?= False
  m ! x2 @?= True
  m ! x3 @?= True

case_xor_case3 = do
  solver <- newSolver
  setCheckModel solver True
  x1 <- newVar solver
  x2 <- newVar solver
  x3 <- newVar solver
  x4 <- newVar solver
  addXORClause solver [x1,x2,x3,x4] True
  addAtLeast solver [x1,x2,x3,x4] 2
  ret <- solve solver
  ret @?= True

------------------------------------------------------------------------

-- from "Pueblo: A Hybrid Pseudo-Boolean SAT Solver"
-- clauseがunitになるレベルで、PB制約が違反状態のままという例。
case_hybridLearning_1 :: IO ()
case_hybridLearning_1 = do
  solver <- newSolver
  [x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11] <- replicateM 11 (newVar solver)

  addClause solver [x11, x10, x9] -- C1
  addClause solver [x8, x7, x6]   -- C2
  addClause solver [x5, x4, x3]   -- C3
  addAtLeast solver [-x2, -x5, -x8, -x11] 3 -- C4
  addAtLeast solver [-x1, -x4, -x7, -x10] 3 -- C5

  replicateM 3 (varBumpActivity solver x3)
  setVarPolarity solver x3 False

  replicateM 2 (varBumpActivity solver x6)
  setVarPolarity solver x6 False

  replicateM 1 (varBumpActivity solver x9)
  setVarPolarity solver x9 False

  setVarPolarity solver x1 True

  setLearningStrategy solver LearningHybrid
  ret <- solve solver
  ret @?= True

-- from "Pueblo: A Hybrid Pseudo-Boolean SAT Solver"
-- clauseがunitになるレベルで、PB制約が違反状態のままという例。
-- さらに、学習したPB制約はunitにはならない。
case_hybridLearning_2 :: IO ()
case_hybridLearning_2 = do
  solver <- newSolver
  [x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12] <- replicateM 12 (newVar solver)

  addClause solver [x11, x10, x9] -- C1
  addClause solver [x8, x7, x6]   -- C2
  addClause solver [x5, x4, x3]   -- C3
  addAtLeast solver [-x2, -x5, -x8, -x11] 3 -- C4
  addAtLeast solver [-x1, -x4, -x7, -x10] 3 -- C5

  addClause solver [x12, -x3]
  addClause solver [x12, -x6]
  addClause solver [x12, -x9]

  varBumpActivity solver x12
  setVarPolarity solver x12 False

  setLearningStrategy solver LearningHybrid
  ret <- solve solver
  ret @?= True

-- regression test for the bug triggered by normalized-blast-floppy1-8.ucl.opb.bz2
case_addPBAtLeast_regression :: IO ()
case_addPBAtLeast_regression = do
  solver <- newSolver
  [x1,x2,x3,x4] <- replicateM 4 (newVar solver)
  addClause solver [-x1]
  addClause solver [-x2, -x3]
  addClause solver [-x2, -x4]
  addPBAtLeast solver [(1,x1),(2,x2),(1,x3),(1,x4)] 3
  ret <- solve solver
  ret @?= False

------------------------------------------------------------------------

case_addFormula = do
  solver <- newSolver
  enc <- Tseitin.newEncoder solver

  [x1,x2,x3,x4,x5] <- replicateM 5 $ liftM Atom $ newVar solver
  Tseitin.addFormula enc $ orB [x1 .=>. x3 .&&. x4, x2 .=>. x3 .&&. x5]
  -- x6 = x3 ∧ x4
  -- x7 = x3 ∧ x5
  Tseitin.addFormula enc $ x1 .||. x2
  Tseitin.addFormula enc $ x4 .=>. notB x5
  ret <- solve solver
  ret @?= True

  Tseitin.addFormula enc $ x2 .<=>. x4
  ret <- solve solver
  ret @?= True

  Tseitin.addFormula enc $ x1 .<=>. x5
  ret <- solve solver
  ret @?= True

  Tseitin.addFormula enc $ notB x1 .=>. x3 .&&. x5
  ret <- solve solver
  ret @?= True

  Tseitin.addFormula enc $ notB x2 .=>. x3 .&&. x4
  ret <- solve solver
  ret @?= False

case_addFormula_Peirces_Law = do
  solver <- newSolver
  enc <- Tseitin.newEncoder solver
  [x1,x2] <- replicateM 2 $ liftM Atom $ newVar solver
  Tseitin.addFormula enc $ notB $ ((x1 .=>. x2) .=>. x1) .=>. x1
  ret <- solve solver
  ret @?= False

case_encodeConj = do
  solver <- newSolver
  enc <- Tseitin.newEncoder solver
  x1 <- newVar solver
  x2 <- newVar solver
  x3 <- Tseitin.encodeConj enc [x1,x2]

  ret <- solveWith solver [x3]
  ret @?= True
  m <- getModel solver
  evalLit m x1 @?= True
  evalLit m x2 @?= True
  evalLit m x3 @?= True

  ret <- solveWith solver [-x3]
  ret @?= True
  m <- getModel solver
  (evalLit m x1 && evalLit m x2) @?= False
  evalLit m x3 @?= False

case_encodeDisj = do
  solver <- newSolver
  enc <- Tseitin.newEncoder solver
  x1 <- newVar solver
  x2 <- newVar solver
  x3 <- Tseitin.encodeDisj enc [x1,x2]

  ret <- solveWith solver [x3]
  ret @?= True
  m <- getModel solver
  (evalLit m x1 || evalLit m x2) @?= True
  evalLit m x3 @?= True

  ret <- solveWith solver [-x3]
  ret @?= True
  m <- getModel solver
  evalLit m x1 @?= False
  evalLit m x2 @?= False
  evalLit m x3 @?= False

case_evalFormula = do
  solver <- newSolver
  xs <- newVars solver 5
  let f = (x1 .=>. x3 .&&. x4) .||. (x2 .=>. x3 .&&. x5)
        where
          [x1,x2,x3,x4,x5] = map Atom xs
      g :: Model -> Bool
      g m = (not x1 || (x3 && x4)) || (not x2 || (x3 && x5))
        where
          [x1,x2,x3,x4,x5] = elems m
  let ms :: [Model]
      ms = liftM (array (1,5)) $ sequence [[(x,val) | val <- [False,True]] | x <- xs]
  forM_ ms $ \m -> do
    Tseitin.evalFormula m f @?= g m

------------------------------------------------------------------------

case_MUS = do
  solver <- newSolver
  [x1,x2,x3] <- newVars solver 3
  sels@[y1,y2,y3,y4,y5,y6] <- newVars solver 6
  addClause solver [-y1, x1]
  addClause solver [-y2, -x1]
  addClause solver [-y3, -x1, x2]
  addClause solver [-y4, -x2]
  addClause solver [-y5, -x1, x3]
  addClause solver [-y6, -x3]

  ret <- solveWith solver sels
  ret @?= False

  actual <- MUS.findMUSAssumptions solver MUS.defaultOptions
  let actual'  = IntSet.map (\x -> x-3) actual
      expected = map IntSet.fromList [[1, 2], [1, 3, 4], [1, 5, 6]]
  actual' `elem` expected @?= True

case_MUS_QuickXplain = do
  solver <- newSolver
  [x1,x2,x3] <- newVars solver 3
  sels@[y1,y2,y3,y4,y5,y6] <- newVars solver 6
  addClause solver [-y1, x1]
  addClause solver [-y2, -x1]
  addClause solver [-y3, -x1, x2]
  addClause solver [-y4, -x2]
  addClause solver [-y5, -x1, x3]
  addClause solver [-y6, -x3]

  ret <- solveWith solver sels
  ret @?= False

  actual <- QuickXplain.findMUSAssumptions solver QuickXplain.defaultOptions
  let actual'  = IntSet.map (\x -> x-3) actual
      expected = map IntSet.fromList [[1, 2], [1, 3, 4], [1, 5, 6]]
  actual' `elem` expected @?= True

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

case_camus_allMCSAssumptions = do
  solver <- newSolver
  [x1,x2,x3] <- newVars solver 3
  sels@[y1,y2,y3,y4,y5,y6] <- newVars solver 6
  addClause solver [-y1, x1]
  addClause solver [-y2, -x1]
  addClause solver [-y3, -x1, x2]
  addClause solver [-y4, -x2]
  addClause solver [-y5, -x1, x3]
  addClause solver [-y6, -x3]
  actual <- CAMUS.allMCSAssumptions solver sels CAMUS.defaultOptions
  let actual'   = Set.fromList actual
      expected  = map (IntSet.fromList . map (+3)) [[1], [2,3,5], [2,3,6], [2,4,5], [2,4,6]]
      expected' = Set.fromList expected
  actual' @?= expected'

case_DAA_allMCSAssumptions = do
  solver <- newSolver
  [x1,x2,x3] <- newVars solver 3
  sels@[y1,y2,y3,y4,y5,y6] <- newVars solver 6
  addClause solver [-y1, x1]
  addClause solver [-y2, -x1]
  addClause solver [-y3, -x1, x2]
  addClause solver [-y4, -x2]
  addClause solver [-y5, -x1, x3]
  addClause solver [-y6, -x3]
  actual <- DAA.allMCSAssumptions solver sels DAA.defaultOptions
  let actual'   = Set.fromList $ actual
      expected  = map (IntSet.fromList . map (+3)) [[1], [2,3,5], [2,3,6], [2,4,5], [2,4,6]]
      expected' = Set.fromList $ expected
  actual' @?= expected'

case_camus_allMUSAssumptions = do
  solver <- newSolver
  [x1,x2,x3] <- newVars solver 3
  sels@[y1,y2,y3,y4,y5,y6] <- newVars solver 6
  addClause solver [-y1, x1]
  addClause solver [-y2, -x1]
  addClause solver [-y3, -x1, x2]
  addClause solver [-y4, -x2]
  addClause solver [-y5, -x1, x3]
  addClause solver [-y6, -x3]
  actual <- CAMUS.allMUSAssumptions solver sels CAMUS.defaultOptions
  let actual'   = Set.fromList $ actual
      expected  = map (IntSet.fromList . map (+3)) [[1,2], [1,3,4], [1,5,6]]
      expected' = Set.fromList $ expected
  actual' @?= expected'

case_DAA_allMUSAssumptions = do
  solver <- newSolver
  [x1,x2,x3] <- newVars solver 3
  sels@[y1,y2,y3,y4,y5,y6] <- newVars solver 6
  addClause solver [-y1, x1]
  addClause solver [-y2, -x1]
  addClause solver [-y3, -x1, x2]
  addClause solver [-y4, -x2]
  addClause solver [-y5, -x1, x3]
  addClause solver [-y6, -x3]
  actual <- DAA.allMUSAssumptions solver sels DAA.defaultOptions
  let actual'   = Set.fromList $ actual
      expected  = map (IntSet.fromList . map (+3)) [[1,2], [1,3,4], [1,5,6]]
      expected' = Set.fromList $ expected
  actual' @?= expected'

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
case_camus_allMUSAssumptions_2 = do
  solver <- newSolver
  [a,b,c,d,e] <- newVars solver 5
  sels@[y0,y1,y2,y3,y4,y5,y6,y7,y8,y9,y10,y11,y12] <- newVars solver 13
  addClause solver [-y0, d]
  addClause solver [-y1, b, c]
  addClause solver [-y2, a, b]
  addClause solver [-y3, a, -c]
  addClause solver [-y4, -b, -e]
  addClause solver [-y5, -a, -b]
  addClause solver [-y6, a, e]
  addClause solver [-y7, -a, -e]
  addClause solver [-y8, b, e]
  addClause solver [-y9, -a, b, -c]
  addClause solver [-y10, -a, b, -d]
  addClause solver [-y11, a, -b, c]
  addClause solver [-y12, a, -b, -d]

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
    ret <- solveWith solver core
    assertBool (show core ++ " should be a core") (not ret)
    forM (remove1 core) $ \xs -> do
      ret <- solveWith solver xs
      assertBool (show core ++ " should be satisfiable") ret

  actual <- CAMUS.allMUSAssumptions solver sels CAMUS.defaultOptions
  let actual'   = Set.fromList actual
      expected' = Set.fromList $ map IntSet.fromList $ cores
  actual' @?= expected'

case_HYCAM_allMUSAssumptions = do
  solver <- newSolver
  [a,b,c,d,e] <- newVars solver 5
  sels@[y0,y1,y2,y3,y4,y5,y6,y7,y8,y9,y10,y11,y12] <- newVars solver 13
  addClause solver [-y0, d]
  addClause solver [-y1, b, c]
  addClause solver [-y2, a, b]
  addClause solver [-y3, a, -c]
  addClause solver [-y4, -b, -e]
  addClause solver [-y5, -a, -b]
  addClause solver [-y6, a, e]
  addClause solver [-y7, -a, -e]
  addClause solver [-y8, b, e]
  addClause solver [-y9, -a, b, -c]
  addClause solver [-y10, -a, b, -d]
  addClause solver [-y11, a, -b, c]
  addClause solver [-y12, a, -b, -d]

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
  ret <- solveWith solver [y0,y1,y2,y4,y5,y6,y7,y9,y11,y12]
  assertBool "failed to prove the bug of HYCAM paper" (not ret)
  
  let cand = map IntSet.fromList [[y5], [y3,y2], [y0,y1,y2]]
  actual <- CAMUS.allMUSAssumptions solver sels CAMUS.defaultOptions{ CAMUS.optKnownCSes = cand }
  let actual'   = Set.fromList $ actual
      expected' = Set.fromList $ map IntSet.fromList cores
  actual' @?= expected'

case_DAA_allMUSAssumptions_2 = do
  solver <- newSolver
  [a,b,c,d,e] <- newVars solver 5
  sels@[y0,y1,y2,y3,y4,y5,y6,y7,y8,y9,y10,y11,y12] <- newVars solver 13
  addClause solver [-y0, d]
  addClause solver [-y1, b, c]
  addClause solver [-y2, a, b]
  addClause solver [-y3, a, -c]
  addClause solver [-y4, -b, -e]
  addClause solver [-y5, -a, -b]
  addClause solver [-y6, a, e]
  addClause solver [-y7, -a, -e]
  addClause solver [-y8, b, e]
  addClause solver [-y9, -a, b, -c]
  addClause solver [-y10, -a, b, -d]
  addClause solver [-y11, a, -b, c]
  addClause solver [-y12, a, -b, -d]

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
    ret <- solveWith solver core
    assertBool (show core ++ " should be a core") (not ret)
    forM (remove1 core) $ \xs -> do
      ret <- solveWith solver xs
      assertBool (show core ++ " should be satisfiable") ret

  actual <- DAA.allMUSAssumptions solver sels DAA.defaultOptions
  let actual'   = Set.fromList actual
      expected' = Set.fromList $ map IntSet.fromList cores
  actual' @?= expected'

------------------------------------------------------------------------

instance Arbitrary LearningStrategy where
  arbitrary = arbitraryBoundedEnum

instance Arbitrary RestartStrategy where
  arbitrary = arbitraryBoundedEnum

instance Arbitrary PBHandlerType where
  arbitrary = arbitraryBoundedEnum

arbitrarySolver :: QM.PropertyM IO Solver
arbitrarySolver = do
  seed <- QM.pick arbitrary
  learningStrategy <- QM.pick arbitrary
  restartStrategy <- QM.pick arbitrary
  restartFirst <- QM.pick arbitrary
  restartInc <- QM.pick $ liftM ((1.01 +) . abs) arbitrary
  learntSizeFirst <- QM.pick arbitrary
  learntSizeInc <- QM.pick $ liftM ((1.01 +) . abs) arbitrary
  pbhandler <- QM.pick arbitrary
  ccmin <- QM.pick $ choose (0,2)
  phaseSaving <- QM.pick arbitrary
  forwardSubsumptionRemoval <- QM.pick arbitrary
  backwardSubsumptionRemoval <- QM.pick arbitrary
  randomFreq <- QM.pick $ choose (0,1)
  splitClausePart <- QM.pick arbitrary
  QM.run $ do
    solver <- newSolver
    setRandomGen solver (Rand.mkStdGen seed)
    setCheckModel solver True
    setLearningStrategy solver learningStrategy
    setRestartStrategy solver restartStrategy
    setRestartFirst solver restartFirst
    setRestartInc solver restartInc
    setLearntSizeFirst solver learntSizeFirst
    setLearntSizeInc solver learntSizeInc
    setPBHandlerType solver pbhandler
    setCCMin solver ccmin
    setEnablePhaseSaving solver phaseSaving
    setEnableForwardSubsumptionRemoval solver forwardSubsumptionRemoval
    setEnableBackwardSubsumptionRemoval solver backwardSubsumptionRemoval
    setRandomFreq solver randomFreq
    setPBSplitClausePart solver splitClausePart
    return solver

------------------------------------------------------------------------
-- Test harness

main :: IO ()
main = $(defaultMainGenerator)
