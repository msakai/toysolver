{-# OPTIONS_GHC -Wall -fno-warn-orphans #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
module Test.SAT.Utils where

import Control.Monad
import Data.Array.IArray
import Data.Default.Class
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import Data.List
import Data.Maybe
import qualified Data.Vector as V
import qualified System.Random.MWC as Rand

import Test.Tasty.QuickCheck
import qualified Test.QuickCheck.Monadic as QM

import qualified ToySolver.SAT as SAT
import qualified ToySolver.SAT.Types as SAT
import qualified ToySolver.SAT.Encoder.Cardinality as Cardinality
import qualified ToySolver.SAT.Encoder.PB as PB
import qualified ToySolver.SAT.Encoder.PBNLC as PBNLC
import qualified ToySolver.SAT.Encoder.Tseitin as Tseitin
import qualified ToySolver.SAT.PBO as PBO

import qualified Data.PseudoBoolean as PBFile
import ToySolver.Converter
import qualified ToySolver.FileFormat.CNF as CNF

-- ---------------------------------------------------------------------

allAssignments :: Int -> [SAT.Model]
allAssignments nv = [array (1,nv) (zip [1..nv] xs) | xs <- replicateM nv [True,False]]

forAllAssignments :: Testable prop => Int -> (SAT.Model -> prop) ->  Property
forAllAssignments nv p = conjoin [counterexample (show m) (p m) | m <- allAssignments nv]

arbitraryAssignment :: Int -> Gen SAT.Model
arbitraryAssignment nv = do
  bs <- replicateM nv arbitrary
  return $ array (1,nv) (zip [1..] bs)

arbitraryLit :: Int -> Gen SAT.Lit
arbitraryLit nv = choose (-nv, nv) `suchThat` (/= 0)

-- ---------------------------------------------------------------------

arbitraryCNF :: Gen CNF.CNF
arbitraryCNF = do
  nv <- choose (0,10)
  nc <- choose (0,50)
  cs <- replicateM nc $ do
    len <- choose (0,10)
    if nv == 0 then
      return $ SAT.packClause []
    else
      SAT.packClause <$> replicateM len (arbitraryLit nv)
  return $
    CNF.CNF
    { CNF.cnfNumVars = nv
    , CNF.cnfNumClauses = nc
    , CNF.cnfClauses = cs
    }


evalCNF :: SAT.Model -> CNF.CNF -> Bool
evalCNF m cnf = all (SAT.evalClause m . SAT.unpackClause) (CNF.cnfClauses cnf)

evalCNFCost :: SAT.Model -> CNF.CNF -> Int
evalCNFCost m cnf = sum $ map f (CNF.cnfClauses cnf)
  where
    f c = if SAT.evalClause m (SAT.unpackClause c) then 0 else 1


arbitraryGCNF :: Gen CNF.GCNF
arbitraryGCNF = do
  nv <- choose (0,10)
  nc <- choose (0,50)
  ng <- choose (0,10)
  cs <- replicateM nc $ do
    g <- choose (0,ng) -- inclusive range
    c <-
      if nv == 0 then do
        return $ SAT.packClause []
      else do
        len <- choose (0,10)
        SAT.packClause <$> replicateM len (arbitraryLit nv)
    return (g,c)
  return $
    CNF.GCNF
    { CNF.gcnfNumVars = nv
    , CNF.gcnfNumClauses = nc
    , CNF.gcnfLastGroupIndex = ng
    , CNF.gcnfClauses = cs
    }


arbitraryWCNF :: Gen CNF.WCNF
arbitraryWCNF = do
  nv <- choose (0,10)
  nc <- choose (0,50)
  cs <- replicateM nc $ do
    w <- arbitrary
    c <- do
      if nv == 0 then do
        return $ SAT.packClause []
      else do
        len <- choose (0,10)
        SAT.packClause <$> replicateM len (arbitraryLit nv)
    return (fmap getPositive w, c)
  let topCost = sum [w | (Just w, _) <- cs] + 1
  return $
    CNF.WCNF
    { CNF.wcnfNumVars = nv
    , CNF.wcnfNumClauses = nc
    , CNF.wcnfTopCost = topCost
    , CNF.wcnfClauses = [(fromMaybe topCost w, c) | (w,c) <- cs]
    }


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


evalWCNFCost :: SAT.Model -> CNF.WCNF -> Integer
evalWCNFCost m wcnf = sum $ do
  (w,c) <- CNF.wcnfClauses wcnf
  guard $ not $ SAT.evalClause m (SAT.unpackClause c)
  return w


arbitraryNewWCNF :: Gen CNF.NewWCNF
arbitraryNewWCNF = do
  wcnf <- arbitraryWCNF
  return $ CNF.NewWCNF [(if w >= CNF.wcnfTopCost wcnf then Nothing else Just w, c) | (w, c) <- CNF.wcnfClauses wcnf]


arbitraryQDimacs :: Gen CNF.QDimacs
arbitraryQDimacs = do
  nv <- choose (0,10)
  nc <- choose (0,50)
  prefix <- arbitraryPrefix $ IntSet.fromList [1..nv]

  cs <- replicateM nc $ do
    if nv == 0 then
      return $ SAT.packClause []
    else do
      len <- choose (0,10)
      SAT.packClause <$> replicateM len (arbitraryLit nv)
  return $
    CNF.QDimacs
    { CNF.qdimacsNumVars = nv
    , CNF.qdimacsNumClauses = nc
    , CNF.qdimacsPrefix = prefix
    , CNF.qdimacsMatrix = cs
    }

arbitraryPrefix :: IntSet -> Gen [CNF.QuantSet]
arbitraryPrefix xs = do
  if IntSet.null xs then
    return []
  else do
    b <- arbitrary
    if b then
      return []
    else do
      xs1 <- subsetof xs `suchThat` (not . IntSet.null)
      let xs2 = xs IntSet.\\ xs1
      q <- elements [CNF.E, CNF.A]
      ((q, IntSet.toList xs1) :) <$> arbitraryPrefix xs2

subsetof :: IntSet -> Gen IntSet
subsetof xs = (IntSet.fromList . catMaybes) <$> sequence [elements [Just x, Nothing] | x <- IntSet.toList xs]


data PBRel = PBRelGE | PBRelEQ | PBRelLE deriving (Eq, Ord, Enum, Bounded, Show)

instance Arbitrary PBRel where
  arbitrary = arbitraryBoundedEnum

evalPBRel :: Ord a => PBRel -> a -> a -> Bool
evalPBRel PBRelGE = (>=)
evalPBRel PBRelLE = (<=)
evalPBRel PBRelEQ = (==)


type PBLin = (Int,[(PBRel,SAT.PBLinSum,Integer)])

arbitraryPB :: Gen PBLin
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
      l <- arbitraryLit nv
      c <- arbitrary
      return (c,l)

evalPB :: SAT.Model -> PBLin -> Bool
evalPB m (_,cs) = all (\(o,lhs,rhs) -> evalPBRel o (SAT.evalPBLinSum m lhs) rhs) cs


type WBOLin = (Int, [(Maybe Integer, (PBRel,SAT.PBLinSum,Integer))], Maybe Integer)

evalWBO :: SAT.Model -> WBOLin -> Maybe Integer
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

arbitraryWBO :: Gen WBOLin
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
          ls <- listOf (arbitraryLit nv)
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
        replicateM len $ arbitraryLit nv
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
           SAT.packClause <$> replicateM len (arbitraryLit nv)
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

solveCNF :: SAT.Solver -> CNF.CNF -> IO (Maybe SAT.Model)
solveCNF solver cnf = do
  SAT.newVars_ solver (CNF.cnfNumVars cnf)
  forM_ (CNF.cnfClauses cnf) $ \c -> SAT.addClause solver (SAT.unpackClause c)
  ret <- SAT.solve solver
  if ret then do
    m <- SAT.getModel solver
    return (Just m)
  else do
    return Nothing


solvePB :: SAT.Solver -> PBLin -> IO (Maybe SAT.Model)
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


optimizePBO :: SAT.Solver -> PBO.Optimizer -> PBLin -> IO (Maybe (SAT.Model, Integer))
optimizePBO solver opt (nv,cs) = do
  SAT.newVars_ solver nv
  forM_ cs $ \(o,lhs,rhs) -> do
    case o of
      PBRelGE -> SAT.addPBAtLeast solver lhs rhs
      PBRelLE -> SAT.addPBAtMost solver lhs rhs
      PBRelEQ -> SAT.addPBExactly solver lhs rhs
  PBO.optimize opt
  PBO.getBestSolution opt


optimizeWBO
  :: SAT.Solver
  -> PBO.Method
  -> WBOLin
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
  PBO.setMethod opt method
  PBO.optimize opt
  liftM (fmap (\(m, val) -> (SAT.restrictModel nv m, val))) $ PBO.getBestSolution opt


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


solvePBFormula :: SAT.Solver -> PBFile.Formula -> IO (Maybe SAT.Model)
solvePBFormula solver opb = do
  SAT.newVars_ solver (PBFile.pbNumVars opb)
  enc <- PBNLC.newEncoder solver =<< Tseitin.newEncoder solver
  forM_ (PBFile.pbConstraints opb) $ \(lhs, op, rhs) -> do
    case op of
      PBFile.Ge -> PBNLC.addPBNLAtLeast enc lhs rhs
      PBFile.Eq -> PBNLC.addPBNLExactly enc lhs rhs
  ret <- SAT.solve solver
  if ret then do
    m <- SAT.getModel solver
    return $ Just $ SAT.restrictModel (PBFile.pbNumVars opb) m
  else do
    return Nothing


optimizePBFormula
  :: SAT.Solver
  -> PBO.Method
  -> PBFile.Formula
  -> IO (Maybe (SAT.Model, Integer))
optimizePBFormula solver method opb = do
  SAT.newVars_ solver (PBFile.pbNumVars opb)
  enc <- PBNLC.newEncoder solver =<< Tseitin.newEncoder solver
  forM_ (PBFile.pbConstraints opb) $ \(lhs, op, rhs) -> do
    case op of
      PBFile.Ge -> PBNLC.addPBNLAtLeast enc lhs rhs
      PBFile.Eq -> PBNLC.addPBNLExactly enc lhs rhs
  let obj = fromMaybe [] $ PBFile.pbObjectiveFunction opb
  obj2 <- PBNLC.linearizePBSumWithPolarity enc Tseitin.polarityNeg obj
  opt <- PBO.newOptimizer2 solver obj2 (\m -> SAT.evalPBSum m obj)
  PBO.setMethod opt method
  PBO.optimize opt
  liftM (fmap (\(m, val) -> (SAT.restrictModel (PBFile.pbNumVars opb) m, val))) $ PBO.getBestSolution opt


optimizePBSoftFormula
  :: SAT.Solver
  -> PBO.Method
  -> PBFile.SoftFormula
  -> IO (Maybe (SAT.Model, Integer))
optimizePBSoftFormula solver method wbo = do
  SAT.newVars_ solver (PBFile.wboNumVars wbo)
  enc <- PBNLC.newEncoder solver =<< Tseitin.newEncoder solver
  obj <- liftM catMaybes $ forM (PBFile.wboConstraints wbo) $ \(cost, (lhs,op,rhs)) -> do
    case cost of
      Nothing -> do
        case op of
          PBFile.Ge -> PBNLC.addPBNLAtLeast enc lhs rhs
          PBFile.Eq -> PBNLC.addPBNLExactly enc lhs rhs
        return Nothing
      Just w -> do
        sel <- SAT.newVar solver
        case op of
          PBFile.Ge -> PBNLC.addPBNLAtLeastSoft enc sel lhs rhs
          PBFile.Eq -> PBNLC.addPBNLExactlySoft enc sel lhs rhs
        return $ Just (w,-sel)
  case PBFile.wboTopCost wbo of
    Nothing -> return ()
    Just c -> SAT.addPBAtMost solver obj (c-1)
  opt <- PBO.newOptimizer solver obj
  PBO.setMethod opt method
  PBO.optimize opt
  liftM (fmap (\(m, val) -> (SAT.restrictModel (PBFile.wboNumVars wbo) m, val))) $ PBO.getBestSolution opt


optimizeWCNF
  :: SAT.Solver
  -> PBO.Method
  -> CNF.WCNF
  -> IO (Maybe (SAT.Model, Integer))
optimizeWCNF solver method wcnf = do
  let (wbo, info) = maxsat2wbo wcnf
  ret <- optimizePBSoftFormula solver method wbo
  case ret of
    Nothing -> return Nothing
    Just (m, obj) -> do
      let m' = transformBackward info m
          obj' = transformObjValueBackward info obj
      return $ Just (m', obj')

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

instance Arbitrary Cardinality.Strategy where
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

arbitraryPBSoftFormula :: Gen PBFile.SoftFormula
arbitraryPBSoftFormula = do
  nv <- choose (0,10)
  nc <- choose (0,10)
  cs <- replicateM nc $ do
    cost <- fmap getPositive <$> arbitrary
    lhs <- arbitraryPBSum nv
    op <- arbitrary
    rhs <- arbitrary
    return (cost, (lhs,op,rhs))
  top <- fmap getPositive <$> arbitrary
  return $
    PBFile.SoftFormula
    { PBFile.wboNumVars = nv
    , PBFile.wboNumConstraints = nc
    , PBFile.wboConstraints = cs
    , PBFile.wboTopCost = top
    }

instance Arbitrary PBFile.Op where
  arbitrary = arbitraryBoundedEnum

instance Arbitrary Tseitin.Polarity where
  arbitrary = elements
    [ Tseitin.polarityPos
    , Tseitin.polarityNeg
    , Tseitin.polarityBoth
    , Tseitin.polarityNone
    ]

-- ---------------------------------------------------------------------
