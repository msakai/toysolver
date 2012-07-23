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
  ( Formula (..)
  , addFormula
  ) where

import Control.Monad
import qualified SAT as SAT

data Formula
  = Var SAT.Var
  | And [Formula]
  | Or [Formula]
  | Not Formula
  | Imply Formula Formula
  | Equiv Formula Formula
  deriving (Show, Eq, Ord)

addFormula :: SAT.Solver -> Formula -> IO ()
addFormula solver formula =
  case formula of
    And xs -> mapM_ (addFormula solver) xs
    Equiv a b -> do
      lit1 <- encodeToLit solver a
      lit2 <- encodeToLit solver b
      SAT.addClause solver [SAT.litNot lit1, lit2] -- a→b
      SAT.addClause solver [SAT.litNot lit2, lit1] -- b→a
    Not (Not a)     -> addFormula solver a
    Not (Or xs)     -> addFormula solver (And (map Not xs))
    Not (Imply a b) -> addFormula solver (And [a, Not b])
    Not (Equiv a b) -> do
      lit1 <- encodeToLit solver a
      lit2 <- encodeToLit solver b
      SAT.addClause solver [lit1, lit2] -- a ∨ b
      SAT.addClause solver [SAT.litNot lit1, SAT.litNot lit2] -- ¬a ∨ ¬b
    _ -> do
      c <- encodeToClause solver formula
      SAT.addClause solver c

encodeToClause :: SAT.Solver -> Formula -> IO SAT.Clause
encodeToClause solver formula =
  case formula of
    And [x] -> encodeToClause solver x
    Or xs -> do
      cs <- mapM (encodeToClause solver) xs
      return $ concat cs
    Not (Not x)  -> encodeToClause solver x
    Not (And xs) -> do
      encodeToClause solver (Or (map Not xs))
    Imply a b -> do
      encodeToClause solver (Or [Not a, b])
    _ -> do
      l <- encodeToLit solver formula
      return [l]

encodeToLit :: SAT.Solver -> Formula -> IO SAT.Lit
encodeToLit solver formula =
  case formula of
    Var v -> return v
    And xs -> do
      v <- SAT.newVar solver
      ls <- mapM (encodeToLit solver) xs
      -- (v → li)  ⇔  (¬v ∨ li)
      forM_ ls $ \l -> do
        SAT.addClause solver [SAT.litNot v, l]
      -- ((l1 ∧ l2 ∧ … ∧ ln) → v)  ⇔  (¬l1 ∨ ¬l2 ∨ … ∨ ¬ln ∨ v)
      SAT.addClause solver (v : map SAT.litNot ls)
      return v
    Or xs -> do
      v <- SAT.newVar solver
      ls <- mapM (encodeToLit solver) xs
      -- (li → v)  ⇔  (¬li ∨ v)
      forM_ ls $ \l -> do
        SAT.addClause solver [SAT.litNot l, v]
      -- (v → (l1 ∨ l2 ∨ … ∨ ln))  ⇔  (¬v ∨ l1 ∨ l2 ∨ … ∨ ln)
      SAT.addClause solver (SAT.litNot v : ls)
      return v
    Not x -> do
      lit <- encodeToLit solver x
      return $ SAT.litNot lit
    Imply x y -> do
      encodeToLit solver (Or [Not x, y])
    Equiv x y -> do
      lit1 <- encodeToLit solver x
      lit2 <- encodeToLit solver y
      encodeToLit solver $
        And [ Imply (Var lit1) (Var lit2)
            , Imply (Var lit2) (Var lit1)
            ]
        -- Varにリテラルを渡しているのは少し気持ち悪い
