{-# OPTIONS_GHC -Wall #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.SAT.TseitinEncoder
-- Copyright   :  (c) Masahiro Sakai 2012
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  portable
-- 
-- Tseitin encoding
--
-- TODO:
-- 
-- * reduce variables.
--
-- References:
--
-- * [Tse83] G. Tseitin. On the complexity of derivation in propositional
--   calculus. Automation of Reasoning: Classical Papers in Computational
--   Logic, 2:466-483, 1983. Springer-Verlag. 
--
-- * [For60] R. Fortet. Application de l'algèbre de Boole en rechercheop
--   opérationelle. Revue Française de Recherche Opérationelle, 4:17-26,
--   1960. 
--
-- * [BM84a] E. Balas and J. B. Mazzola. Nonlinear 0-1 programming:
--   I. Linearization techniques. Mathematical Programming, 30(1):1-21,
--   1984.
-- 
-- * [BM84b] E. Balas and J. B. Mazzola. Nonlinear 0-1 programming:
--   II. Dominance relations and algorithms. Mathematical Programming,
--   30(1):22-45, 1984.
-----------------------------------------------------------------------------
module ToySolver.SAT.TseitinEncoder
  (
  -- * The @Encoder@ type
    Encoder
  , newEncoder
  , setUsePB
  , encSolver

  -- * Encoding of boolean formula
  , Formula (..)
  , evalFormula
  , addFormula
  , encodeConj
  , encodeDisj
  , getDefinitions
  ) where

import Control.Monad
import Data.IORef
import Data.Map (Map)
import qualified Data.Map as Map
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import ToySolver.Data.Boolean
import qualified ToySolver.SAT as SAT
import qualified ToySolver.SAT.Types as SAT

-- | Arbitrary formula not restricted to CNF
data Formula
  = Lit SAT.Lit
  | And [Formula]
  | Or [Formula]
  | Not Formula
  | Imply Formula Formula
  | Equiv Formula Formula
  deriving (Show, Eq, Ord)

instance MonotoneBoolean Formula where
  andB = And
  orB = Or

instance Complement Formula where
  notB = Not

instance Boolean Formula where
  (.=>.) = Imply
  (.<=>.) = Equiv

evalFormula :: SAT.IModel m => m -> Formula -> Bool
evalFormula m = e
  where
    e (Lit l)  = SAT.evalLit m l
    e (And fs) = and (map e fs)
    e (Or fs)  = or (map e fs)
    e (Not f)  = not (e f)
    e (Imply f1 f2) = not (e f1) || e f2
    e (Equiv f1 f2) = e f1 == e f2

-- | Encoder instance
data Encoder =
  Encoder
  { encSolver    :: SAT.Solver
  , encUsePB     :: IORef Bool
  , encConjTable :: !(IORef (Map SAT.LitSet SAT.Lit))
  }

-- | Create a @Encoder@ instance.
newEncoder :: SAT.Solver -> IO Encoder
newEncoder solver = do
  usePBRef <- newIORef False
  table <- newIORef Map.empty
  return $
    Encoder
    { encSolver = solver
    , encUsePB  = usePBRef
    , encConjTable = table
    }

-- | Use /pseudo boolean constraints/ or use only /clauses/.
setUsePB :: Encoder -> Bool -> IO ()
setUsePB encoder usePB = writeIORef (encUsePB encoder) usePB

-- | Assert a given formula to underlying SAT solver by using
-- Tseitin encoding.
addFormula :: Encoder -> Formula -> IO ()
addFormula encoder formula = do
  let solver = encSolver encoder
  case formula of
    And xs -> mapM_ (addFormula encoder) xs
    Equiv a b -> do
      lit1 <- encodeToLit encoder a
      lit2 <- encodeToLit encoder b
      SAT.addClause solver [SAT.litNot lit1, lit2] -- a→b
      SAT.addClause solver [SAT.litNot lit2, lit1] -- b→a
    Not (Not a)     -> addFormula encoder a
    Not (Or xs)     -> addFormula encoder (andB (map notB xs))
    Not (Imply a b) -> addFormula encoder (a .&&. notB b)
    Not (Equiv a b) -> do
      lit1 <- encodeToLit encoder a
      lit2 <- encodeToLit encoder b
      SAT.addClause solver [lit1, lit2] -- a ∨ b
      SAT.addClause solver [SAT.litNot lit1, SAT.litNot lit2] -- ¬a ∨ ¬b
    _ -> do
      c <- encodeToClause encoder formula
      SAT.addClause solver c

encodeToClause :: Encoder -> Formula -> IO SAT.Clause
encodeToClause encoder formula =
  case formula of
    And [x] -> encodeToClause encoder x
    Or xs -> do
      cs <- mapM (encodeToClause encoder) xs
      return $ concat cs
    Not (Not x)  -> encodeToClause encoder x
    Not (And xs) -> do
      encodeToClause encoder (orB (map notB xs))
    Imply a b -> do
      encodeToClause encoder (notB a .||. b)
    _ -> do
      l <- encodeToLit encoder formula
      return [l]

encodeToLit :: Encoder -> Formula -> IO SAT.Lit
encodeToLit encoder formula = do
  case formula of
    Lit l -> return l
    And xs -> encodeConj encoder =<< mapM (encodeToLit encoder) xs
    Or xs  -> encodeDisj encoder =<< mapM (encodeToLit encoder) xs
    Not x -> liftM SAT.litNot $ encodeToLit encoder x
    Imply x y -> do
      encodeToLit encoder (notB x .||. y)
    Equiv x y -> do
      lit1 <- encodeToLit encoder x
      lit2 <- encodeToLit encoder y
      encodeToLit encoder $
        (Lit lit1 .=>. Lit lit2) .&&. (Lit lit2 .=>. Lit lit1)

-- | Return an literal which is equivalent to a given conjunction.
encodeConj :: Encoder -> [SAT.Lit] -> IO SAT.Lit
encodeConj _ [l] =  return l
encodeConj encoder ls =  do
  let ls2 = IntSet.fromList ls
  table <- readIORef (encConjTable encoder)
  case Map.lookup ls2 table of
    Just l -> return l
    Nothing -> do
      let sat = encSolver encoder
      v <- SAT.newVar sat
      addIsConjOf encoder v ls
      return v

-- | Return an literal which is equivalent to a given disjunction.
encodeDisj :: Encoder -> [SAT.Lit] -> IO SAT.Lit
encodeDisj _ [l] =  return l
encodeDisj encoder ls = do
  -- ¬l ⇔ ¬(¬l1 ∧ … ∧ ¬ln) ⇔ (l1 ∨ … ∨ ln)
  l <- encodeConj encoder [SAT.litNot li | li <- ls]
  return $ SAT.litNot l

addIsConjOf :: Encoder -> SAT.Lit -> [SAT.Lit] -> IO ()
addIsConjOf encoder l ls = do
  let solver = encSolver encoder
  usePB <- readIORef (encUsePB encoder)
  if usePB
   then do
     -- ∀i.(l → li) ⇔ Σli >= n*l ⇔ Σli - n*l >= 0
     let n = length ls
     SAT.addPBAtLeast solver ((- fromIntegral n, l) : [(1,li) | li <- ls]) 0
   else do
     forM_ ls $ \li -> do
       -- (l → li)  ⇔  (¬l ∨ li)
       SAT.addClause solver [SAT.litNot l, li]
  -- ((l1 ∧ l2 ∧ … ∧ ln) → l)  ⇔  (¬l1 ∨ ¬l2 ∨ … ∨ ¬ln ∨ l)
  SAT.addClause solver (l : map SAT.litNot ls)
  modifyIORef (encConjTable encoder) (Map.insert (IntSet.fromList ls) l)

getDefinitions :: Encoder -> IO [(SAT.Lit, Formula)]
getDefinitions encoder = do
  t <- readIORef (encConjTable encoder)
  return $ [(l, andB [Lit l1 | l1 <- IntSet.toList ls]) | (ls, l) <- Map.toList t]
