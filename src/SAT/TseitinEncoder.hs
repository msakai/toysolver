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
-----------------------------------------------------------------------------
module SAT.TseitinEncoder
  (
  -- * The @Encoder@ type
    Encoder
  , newEncoder
  , setUsePB

  -- * Encoding of boolean formula
  , Formula (..)
  , addFormula
  ) where

import Control.Monad
import Data.IORef
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
  { encSolver :: SAT.Solver
  , encUsePB  :: IORef Bool
  }

-- | Create a @Encoder@ instance.
newEncoder :: SAT.Solver -> IO Encoder
newEncoder solver = do
  usePBRef <- newIORef False
  return $
    Encoder
    { encSolver = solver
    , encUsePB  = usePBRef
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
  usePB <- readIORef (encUsePB encoder)
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

addIsDisjOf :: Encoder -> SAT.Lit -> [SAT.Lit] -> IO ()
addIsDisjOf encoder l ls = do
  let solver = encSolver encoder
  usePB <- readIORef (encUsePB encoder)
  if usePB
   then do
     -- ∀i.(li → l) ⇔ Σli <= n*l ⇔ Σli - n*l <= 0
     let n = length ls
     SAT.addPBAtMost solver ((- fromIntegral n, l) : [(1,l) | l <- ls]) 0
   else do
     forM_ ls $ \li -> do
       -- (li → l)  ⇔  (¬li ∨ l)
       SAT.addClause solver [SAT.litNot li, l]
  -- (l → (l1 ∨ l2 ∨ … ∨ ln))  ⇔  (¬l ∨ l1 ∨ l2 ∨ … ∨ ln)
  SAT.addClause solver (SAT.litNot l : ls)

addIsConjOf :: Encoder -> SAT.Lit -> [SAT.Lit] -> IO ()
addIsConjOf encoder l ls = do
  let solver = encSolver encoder
  usePB <- readIORef (encUsePB encoder)
  if usePB
   then do
     -- ∀i.(l → li) ⇔ Σli >= n*l ⇔ Σli - n*l >= 0
     let n = length ls
     SAT.addPBAtLeast solver ((- fromIntegral n, l) : [(1,l) | l <- ls]) 0
   else do
     forM_ ls $ \li -> do
       -- (l → li)  ⇔  (¬l ∨ li)
       SAT.addClause solver [SAT.litNot l, li]
  -- ((l1 ∧ l2 ∧ … ∧ ln) → l)  ⇔  (¬l1 ∨ ¬l2 ∨ … ∨ ¬ln ∨ l)
  SAT.addClause solver (l : map SAT.litNot ls)
