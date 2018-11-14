{-# OPTIONS_GHC -Wall #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.Converter.QBF2IPC
-- Copyright   :  (c) Masahiro Sakai 2018
-- License     :  BSD-style
--
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  experimental
-- Portability :  non-portable
--
-- References:
--
-- * Morten Heine B. Sørensen, and Pawel Urzyczyn. Lectures on the Curry-Howard
--   Isomorphism. http://disi.unitn.it/~bernardi/RSISE11/Papers/curry-howard.pdf
--
-----------------------------------------------------------------------------
module ToySolver.Converter.QBF2IPC
  ( qbf2ipc
  ) where

import qualified Data.IntSet as IntSet

import ToySolver.Data.Boolean
import ToySolver.Data.BoolExpr (BoolExpr)
import qualified ToySolver.Data.BoolExpr as BoolExpr
import qualified ToySolver.FileFormat.CNF as CNF
import qualified ToySolver.QBF as QBF
import qualified ToySolver.SAT.Types as SAT


qbf2ipc :: CNF.QDimacs -> (Int, [BoolExpr SAT.Var], BoolExpr SAT.Var)
qbf2ipc qdimacs = (nv2, lhs, rhs)
  where
    nv = CNF.qdimacsNumVars qdimacs
    nc = CNF.qdimacsNumClauses qdimacs

    prefix = [(q,a) | (q,as) <- qs, a <- IntSet.toList as]
      where
        qs = QBF.quantifyFreeVariables nv [(q, IntSet.fromList as) | (q,as) <- CNF.qdimacsPrefix qdimacs]        

    nv2 = nv -- positive literal
        + nv -- negative literal
        + nc -- clause
        + 1  -- conjunction
        + nv -- quantified formula
    alpha_xp x = x
    alpha_xn x = nv + x
    alpha_l l  = BoolExpr.Atom $ if l > 0 then alpha_xp l else alpha_xn (- l)
    alpha_c i  = BoolExpr.Atom $ nv + nv + (1 + i)
    alpha_mat  = BoolExpr.Atom $ nv + nv + nc + 1
    alpha_qf i = BoolExpr.Atom $ nv + nv + nc + 1 + (1 + i)

    lhs =
      snd (f (zip [0..] prefix)) ++
      [foldr (.=>.) alpha_mat [alpha_c i | (i,_) <- zip [0..] (CNF.qdimacsMatrix qdimacs)]] ++
      concat [[alpha_l l .=>. alpha_c i | l <- SAT.unpackClause c] | (i, c) <- zip [0..] (CNF.qdimacsMatrix qdimacs)]
      where
        f [] = (alpha_mat, [])
        f ((i,(QBF.E,x)) : qs) =
         case f qs of
           (alpha_body, ret) -> (alpha_qf i, [(alpha_l x .=>. alpha_body) .=>. alpha_qf i, (alpha_l (- x) .=>. alpha_body) .=>. alpha_qf i] ++ ret)
        f ((i,(QBF.A,x)) : qs) =
         case f qs of
           (alpha_body, ret) -> (alpha_qf i, [(alpha_l x .=>. alpha_body) .=>. (alpha_l (- x) .=>. alpha_body) .=>. alpha_qf i] ++ ret)

    rhs = alpha_qf 0
