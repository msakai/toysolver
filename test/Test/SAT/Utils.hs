{-# LANGUAGE CPP #-}
{-# LANGUAGE TemplateHaskell, ScopedTypeVariables, FlexibleContexts #-}

#if __GLASGOW_HASKELL__ >= 800
{-# OPTIONS_GHC -Wall -Wno-orphans #-}
#else 
{-# OPTIONS_GHC -Wall -fno-warn-orphans #-}
#endif

module Test.SAT.Utils where

import Control.Applicative
import Control.Monad
import Data.Array.IArray
import Data.Default.Class
import Data.List
import qualified Data.Vector as V
import qualified System.Random.MWC as Rand

import Test.Tasty.QuickCheck
import qualified Test.QuickCheck.Monadic as QM

import qualified ToySolver.SAT as SAT
import qualified ToySolver.SAT.Types as SAT
import qualified ToySolver.SAT.Encoder.PB as PB
import qualified ToySolver.SAT.PBO as PBO

import qualified Data.PseudoBoolean as PBFile
import ToySolver.Converter
import qualified ToySolver.FileFormat.CNF as CNF

-- ---------------------------------------------------------------------

allAssignments :: Int -> [SAT.Model]
allAssignments nv = [array (1,nv) (zip [1..nv] xs) | xs <- replicateM nv [True,False]]


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
    { CNF.cnfNumVars = nv
    , CNF.cnfNumClauses = nc
    , CNF.cnfClauses = cs
    }


evalCNF :: SAT.Model -> CNF.CNF -> Bool
evalCNF m cnf = all (SAT.evalClause m . SAT.unpackClause) (CNF.cnfClauses cnf)


evalWCNF :: SAT.Model -> CNF.WCNF -> Maybe Integer
evalWCNF m wcnf = foldl' (liftM2 (+)) (Just 0)
  [ if SAT.evalClause m (SAT.unpackClause c) then
      Just 0
    else if w == CNF.wcnfTopCost wcnf then
      Nothing
    else
      Just w
  | (w,c) <- CNF.wcnfClauses wcnf
  ]


data PBRel = PBRelGE | PBRelEQ | PBRelLE deriving (Eq, Ord, Enum, Bounded, Show)

instance Arbitrary PBRel where
  arbitrary = arbitraryBoundedEnum

evalPBRel :: Ord a => PBRel -> a -> a -> Bool
evalPBRel PBRelGE = (>=)
evalPBRel PBRelLE = (<=)
evalPBRel PBRelEQ = (==)


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


evalWBO :: SAT.Model -> (Int, [(Maybe Integer, (PBRel,SAT.PBLinSum,Integer))], Maybe Integer) -> Maybe Integer
evalWBO m (_nv,cs,top) = do
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


arbitraryNAESAT :: Gen NAESAT
arbitraryNAESAT = do
  cnf <- arbitraryCNF
  return (CNF.cnfNumVars cnf, CNF.cnfClauses cnf)


arbitraryMaxSAT2 :: Gen (CNF.WCNF, Integer)
arbitraryMaxSAT2 = do
  nv <- choose (0,5)
  nc <- choose (0,10)
  cs <- replicateM nc $ do
    len <- choose (0,2)
    c <- if nv == 0 then
           return $ SAT.packClause []
         else
           SAT.packClause <$> (replicateM len $ choose (-nv, nv) `suchThat` (/= 0))
    return (1,c)
  th <- choose (0,nc)
  return $
    ( CNF.WCNF
      { CNF.wcnfNumVars = nv
      , CNF.wcnfNumClauses = nc
      , CNF.wcnfClauses = cs
      , CNF.wcnfTopCost = fromIntegral nc + 1
      }
    , fromIntegral th
    )

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

arbitraryPBSum :: Int -> Gen SAT.PBSum
arbitraryPBSum nv = do
  nt <- choose (0,10)
  replicateM nt $ do
    ls <-
      if nv==0
      then return []
      else do
        m <- choose (0,nv)
        replicateM m $ do
          x <- choose (1,m)
          b <- arbitrary
          return $ if b then x else -x
    c <- arbitrary
    return (c,ls)

arbitraryModel :: Int -> Gen SAT.Model
arbitraryModel nv = do
  bs <- replicateM nv arbitrary
  return $ array (1,nv) (zip [1..] bs)

arbitraryPBFormula :: Gen PBFile.Formula
arbitraryPBFormula = do
  nv <- choose (0,10)
  obj <- do
    b <- arbitrary
    if b then
      liftM Just $ arbitraryPBSum nv
    else
      return Nothing
  nc <- choose (0,10)
  cs <- replicateM nc $ do
    lhs <- arbitraryPBSum nv
    op <- arbitrary
    rhs <- arbitrary
    return (lhs,op,rhs)
  return $
    PBFile.Formula
    { PBFile.pbObjectiveFunction = obj
    , PBFile.pbNumVars = nv
    , PBFile.pbNumConstraints = nc
    , PBFile.pbConstraints = cs
    }

instance Arbitrary PBFile.Op where
  arbitrary = arbitraryBoundedEnum

-- ---------------------------------------------------------------------

#if !MIN_VERSION_QuickCheck(2,8,0)
sublistOf :: [a] -> Gen [a]
sublistOf xs = filterM (\_ -> choose (False, True)) xs
#endif
