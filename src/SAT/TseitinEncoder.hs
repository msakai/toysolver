{-# OPTIONS_GHC -Wall #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  SAT.TseitinEncoder
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
module SAT.TseitinEncoder
  (
  -- * The @Encoder@ type
    Encoder
  , newEncoder
  , setUsePB
  , encSolver

  -- * Encoding of boolean formula
  , Formula (..)
  , addFormula
  , encodeConj
  , encodeDisj
  ) where

import Control.Monad
import Data.IORef
import Data.Map (Map)
import qualified Data.Map as Map
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import qualified SAT as SAT

-- | Arbitrary formula not restricted to CNF
data Formula
  = Var SAT.Var
  | And [Formula]
  | Or [Formula]
  | Not Formula
  | Imply Formula Formula
  | Equiv Formula Formula
  deriving (Show, Eq, Ord)

-- | Encoder instance
data Encoder =
  Encoder
  { encSolver    :: SAT.Solver
  , encUsePB     :: IORef Bool
  , encConjTable :: !(IORef (Map IntSet SAT.Lit))
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
    Not (Or xs)     -> addFormula encoder (And (map Not xs))
    Not (Imply a b) -> addFormula encoder (And [a, Not b])
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
      encodeToClause encoder (Or (map Not xs))
    Imply a b -> do
      encodeToClause encoder (Or [Not a, b])
    _ -> do
      l <- encodeToLit encoder formula
      return [l]

encodeToLit :: Encoder -> Formula -> IO SAT.Lit
encodeToLit encoder formula = do
  let solver = encSolver encoder
  case formula of
    Var v -> return v
    And xs -> do
      v <- SAT.newVar solver
      ls <- mapM (encodeToLit encoder) xs
      addIsConjOf encoder v ls
      return v
    Or xs -> do
      v <- SAT.newVar solver
      ls <- mapM (encodeToLit encoder) xs
      addIsDisjOf encoder v ls
      return v
    Not x -> do
      lit <- encodeToLit encoder x
      return $ SAT.litNot lit
    Imply x y -> do
      encodeToLit encoder (Or [Not x, y])
    Equiv x y -> do
      lit1 <- encodeToLit encoder x
      lit2 <- encodeToLit encoder y
      encodeToLit encoder $
        And [ Imply (Var lit1) (Var lit2)
            , Imply (Var lit2) (Var lit1)
            ]
        -- Varにリテラルを渡しているのは少し気持ち悪い

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
      writeIORef (encConjTable encoder) (Map.insert ls2 v table)
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

addIsDisjOf :: Encoder -> SAT.Lit -> [SAT.Lit] -> IO ()
addIsDisjOf encoder l ls =
  addIsConjOf encoder (SAT.litNot l) [SAT.litNot li | li <- ls]
