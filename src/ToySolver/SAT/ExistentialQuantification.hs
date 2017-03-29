{-# Language BangPatterns #-}
{-# OPTIONS_GHC -Wall #-}
-- -------------------------------------------------------------------
-- |
-- Module      :  ToySolver.SAT.ExistentialQuantification
-- Copyright   :  (c) Masahiro Sakai 2017
-- License     :  BSD-style
--
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  non-portable
--
-- References:
--
-- * [BrauerKingKriener2011] Jörg Brauer, Andy King, and Jael Kriener,
--   "Existential quantification as incremental SAT," in Computer Aided
--   Verification (CAV 2011), G. Gopalakrishnan and S. Qadeer, Eds.
--   pp. 191-207.
--   <https://www.embedded.rwth-aachen.de/lib/exe/fetch.php?media=bib:bkk11a.pdf>
--
-- -------------------------------------------------------------------

module ToySolver.SAT.ExistentialQuantification
  ( project
  , shortestImplicants
  ) where

import Control.Monad
import qualified Data.IntMap as IntMap
import qualified Data.IntSet as IntSet
import Data.IORef
import ToySolver.SAT as SAT
import ToySolver.SAT.Types as SAT
import ToySolver.Text.CNF as CNF

-- -------------------------------------------------------------------

data Info
  = Info
  { forwardMap :: SAT.VarMap (SAT.Var, SAT.Var)
  , backwardMap :: SAT.VarMap SAT.Lit
  }

dualRailEncoding :: SAT.VarSet -> CNF.CNF -> (CNF.CNF, Info)
dualRailEncoding vs cnf =
  ( cnf'
  , Info
    { forwardMap = forward
    , backwardMap = backward
    }
  )
  where
    cnf' =
      CNF.CNF
      { CNF.numVars = CNF.numVars cnf + IntSet.size vs
      , CNF.numClauses = CNF.numClauses cnf + IntSet.size vs
      , CNF.clauses = [ fmap f c | c <- CNF.clauses cnf ] ++ [[-xp,-xn] | (xp,xn) <- IntMap.elems forward]
      }
    f x =
      case IntMap.lookup (abs x) forward of
        Nothing -> x
        Just (xp,xn) -> if x > 0 then xp else xn
    forward =
      IntMap.fromList
      [ (x, (x,x'))
      | (x,x') <- zip (IntSet.toList vs) [CNF.numVars cnf + 1 ..]
      ]
    backward = IntMap.fromList $ concat $
      [ [(xp,x), (xn,-x)]
      | (x, (xp,xn)) <- IntMap.toList forward
      ]

{-
forwardLit :: Info -> Lit -> Lit
forwardLit info l =
  case IntMap.lookup (abs l) (forwardMap info) of
    Nothing -> l
    Just (xp,xn) -> if l > 0 then xp else xn
-}

-- -------------------------------------------------------------------

cube :: Info -> SAT.Model -> LitSet
cube info m = IntSet.fromList $ concat $
  [ if SAT.evalLit m xp then [x]
    else if SAT.evalLit m xn then [-x]
    else []
  | (x, (xp,xn)) <- IntMap.toList (forwardMap info)
  ]

blockingClause :: Info -> SAT.Model -> Clause
blockingClause info m = [-y | y <- IntMap.keys (backwardMap info), SAT.evalLit m y]

shortestImplicants :: SAT.VarSet -> CNF.CNF -> IO [LitSet]
shortestImplicants vs formula = do
  let (tau_formula, info) = dualRailEncoding vs formula
  solver <- SAT.newSolver
  SAT.newVars_ solver (CNF.numVars tau_formula)
  forM_ (CNF.clauses tau_formula) (addClause solver)

  ref <- newIORef []

  let lim = IntMap.size (forwardMap info)

      loop !n | n > lim = return ()
      loop !n = do
        sel <- SAT.newVar solver
        SAT.addPBAtMostSoft solver sel [(1,l) | l <- IntMap.keys (backwardMap info)] (fromIntegral n)
        let loop2 = do
              b <- SAT.solveWith solver [sel]
              when b $ do
                m <- SAT.getModel solver
                let c = cube info m
                modifyIORef ref (c:)
                SAT.addClause solver (blockingClause info m)
                loop2
        loop2
        SAT.addClause solver [-sel]
        loop (n+1)

  loop 0
  reverse <$> readIORef ref

project :: SAT.VarSet -> CNF.CNF -> IO CNF.CNF
project xs cnf = do
  let ys = IntSet.fromList [1 .. CNF.numVars cnf] IntSet.\\ xs
      nv = if IntSet.null ys then 0 else IntSet.findMax ys
  implicants <- shortestImplicants ys cnf
  let cnf' =
        CNF.CNF
        { CNF.numVars = nv
        , CNF.numClauses = length implicants
        , CNF.clauses = map (map negate . IntSet.toList) implicants
        }
  negated_implicates <- shortestImplicants ys cnf'
  let implicates = map (map negate . IntSet.toList) negated_implicates
  return $
    CNF.CNF
    { CNF.numVars = nv
    , CNF.numClauses = length implicates
    , CNF.clauses = implicates
    }
