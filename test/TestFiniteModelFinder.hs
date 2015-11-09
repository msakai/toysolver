{-# LANGUAGE TemplateHaskell, ScopedTypeVariables #-}
module Main (main) where

import Control.Monad
import Control.Monad.State
import Control.Monad.Trans
import Data.Map (Map)
import qualified Data.Map as Map

import Test.Tasty
import Test.Tasty.QuickCheck hiding ((.&&.), (.||.))
import Test.Tasty.HUnit
import Test.Tasty.TH
import qualified Test.QuickCheck.Monadic as QM

import qualified ToySolver.EUF.FiniteModelFinder as MF

type Sig = (Map MF.FSym Int, Map MF.PSym Int)

genTerm' :: Sig -> [MF.Var] -> StateT Int Gen MF.Term
genTerm' (fsyms, _) vs = m
  where
    m = do
      budget <- get
      f <- lift $ elements $ map Left vs ++ [Right (f, arity) | (f, arity) <- Map.toList fsyms, arity == 0 || budget >= arity+1]
      modify (subtract 1)
      case f of
        Left v -> return (MF.TmVar v)
        Right (f', arity) -> do
          args <- replicateM arity m
          return $ MF.TmApp f' args

genAtom' :: Sig -> [MF.Var] -> StateT Int Gen MF.Atom
genAtom' sig@(fsyms, psyms) vs = do
  budget <- get
  (p, arity) <- lift $ elements $ ("=",2) : [(p, arity) | (p, arity) <- Map.toList psyms, arity == 0 || budget >= arity+1]
  modify (subtract 1)
  args <- replicateM arity (genTerm' sig vs)
  return $ MF.PApp p args

genLit' :: Sig -> [MF.Var] -> StateT Int Gen MF.Lit
genLit' sig vs = do
  atom <- genAtom' sig vs
  lift $ elements [MF.Pos atom, MF.Neg atom]  

genClause' :: Sig -> [MF.Var] -> StateT Int Gen MF.Clause
genClause' sig vs = do
  n <- lift $ choose (1,4)
  replicateM n $ genLit' sig vs

genClause :: Sig -> [MF.Var] -> Gen MF.Clause
--genClause sig vs = sized (evalStateT (genClause' sig vs))
genClause sig vs = evalStateT (genClause' sig vs) 8

genSmallSig :: Gen Sig
genSmallSig = do
  nFun <- choose (1::Int, 5)
  nPred <- choose (0::Int, 3)
  fsyms <- liftM Map.fromList $ forM [0..nFun-1] $ \i -> do
    arity <- if i == 0 then return 0 else choose (0, 3)
    return ("f" ++ show i, arity)
  psyms <- liftM Map.fromList $ forM [0..nPred-1] $ \i -> do
    arity <- choose (0, 3)
    return ("p" ++ show i, arity)
  return (fsyms, psyms)

prop_findModel_soundness = QM.monadicIO $ do
  sig <- QM.pick genSmallSig
  nv <- QM.pick $ choose (0::Int, 2)
  let vs = ["v" ++ show i | i <- [0..nv-1]]
  nc <- QM.pick $ choose (0::Int, 3)
  cs <- QM.pick $ replicateM nc $ genClause sig vs
  size <- QM.pick $ choose (1::Int, 5)
  ret <- QM.run $ MF.findModel size cs
  case ret of
    Nothing -> return ()
    Just m -> QM.assert (MF.evalClausesU m cs)

case_example_1 = do
  ret <- MF.findModel 2 cs
  case ret of
    Nothing -> assertFailure (show cs ++ " should be satisfiable")
    Just m -> assertBool (show cs ++ " should be evaluated to true on " ++ unlines (MF.showModel m)) (MF.evalClausesU m cs)
  where
    cs = [[f b .=. c], [f c .=. a], [g a .=. h a a], [g b ./=. h c b]]
    (.=.) x y  = MF.Pos $ MF.PApp "=" [x, y]
    (./=.) x y = MF.Neg $ MF.PApp "=" [x, y]
    a = MF.TmApp "a" []
    b = MF.TmApp "b" []
    c = MF.TmApp "c" []
    f x = MF.TmApp "f" [x]
    g x = MF.TmApp "g" [x]
    h x y = MF.TmApp "h" [x, y]

case_example_2 = do
  ret <- MF.findModel 5 cs
  case ret of
    Nothing -> return ()
    Just _ -> assertFailure (show cs ++ " should be unsatisfiable")
  where
    cs = [[f b .=. c], [f c .=. a], [g a .=. h a a], [g b ./=. h c b], [b .=. c]]
    (.=.) x y  = MF.Pos $ MF.PApp "=" [x, y]
    (./=.) x y = MF.Neg $ MF.PApp "=" [x, y]
    a = MF.TmApp "a" []
    b = MF.TmApp "b" []
    c = MF.TmApp "c" []
    f x = MF.TmApp "f" [x]
    g x = MF.TmApp "g" [x]
    h x y = MF.TmApp "h" [x, y]

-- ---------------------------------------------------------------------
--  Test harness

main :: IO ()
main = $(defaultMainGenerator)

