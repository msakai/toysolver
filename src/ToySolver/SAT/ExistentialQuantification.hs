{-# Language BangPatterns #-}
{-# OPTIONS_GHC -Wall #-}
----------------------------------------------------------------------
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
----------------------------------------------------------------------
module ToySolver.SAT.ExistentialQuantification
  ( project
  , shortestImplicants
  , shortestImplicantsE
  , negateCNF
  ) where

import Control.Monad
import qualified Data.IntMap as IntMap
import qualified Data.IntSet as IntSet
import Data.IORef
import qualified Data.Vector.Generic as VG
import ToySolver.FileFormat.CNF as CNF
import ToySolver.SAT as SAT
import ToySolver.SAT.Types as SAT

-- -------------------------------------------------------------------

data Info
  = Info
  { forwardMap :: SAT.VarMap (SAT.Var, SAT.Var)
  , backwardMap :: SAT.VarMap SAT.Lit
  }

-- | Given a set of variables \(X = \{x_1, \ldots, x_k\}\) and CNF formula \(\phi\), this function
--
-- * duplicates \(X\) with \(X^+ = \{x^+_1,\ldots,x^+_k\}\) and \(X^- = \{x^-_1,\ldots,x^-_k\}\),
--
-- * replaces positive literals \(x_i\) with \(x^+_i\), and negative literals \(\neg x_i\) with \(x^-_i\), and
--
-- * adds constraints \(\neg x^+_i \vee \neg x^-_i\).
dualRailEncoding
  :: SAT.VarSet -- ^ \(X\)
  -> CNF.CNF    -- ^ \(\phi\)
  -> (CNF.CNF, Info)
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
      { CNF.cnfNumVars = CNF.cnfNumVars cnf + IntSet.size vs
      , CNF.cnfNumClauses = CNF.cnfNumClauses cnf + IntSet.size vs
      , CNF.cnfClauses = [ VG.map f c | c <- CNF.cnfClauses cnf ] ++ [SAT.packClause [-xp,-xn] | (xp,xn) <- IntMap.elems forward]
      }
    f x =
      case IntMap.lookup (abs x) forward of
        Nothing -> x
        Just (xp,xn) -> if x > 0 then xp else xn
    forward =
      IntMap.fromList
      [ (x, (x,x'))
      | (x,x') <- zip (IntSet.toList vs) [CNF.cnfNumVars cnf + 1 ..]
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

{-# DEPRECATED shortestImplicants "Use shortestImplicantsE instead" #-} 
-- | Given a set of variables \(X = \{x_1, \ldots, x_k\}\) and CNF formula \(\phi\),
-- this function computes shortest implicants of \(\phi\) in terms of \(X\).
-- Variables except \(X\) are treated as if they are existentially quantified.
--
-- Resulting shortest implicants form a DNF (disjunctive normal form) formula that is
-- equivalent to the original (existentially quantified) formula.
shortestImplicants
  :: SAT.VarSet  -- ^ \(X\)
  -> CNF.CNF     -- ^ \(\phi\)
  -> IO [LitSet]
shortestImplicants xs formula =
  shortestImplicantsE (IntSet.fromList [1 .. CNF.cnfNumVars formula] IntSet.\\ xs) formula

-- | Given a set of variables \(X = \{x_1, \ldots, x_k\}\) and CNF formula \(\phi\),
-- this function computes shortest implicants of \(\exists X. \phi\).
--
-- Resulting shortest implicants form a DNF (disjunctive normal form) formula that is
-- equivalent to the original formula \(\exists X. \phi\).
shortestImplicantsE
  :: SAT.VarSet  -- ^ \(X\)
  -> CNF.CNF     -- ^ \(\phi\)
  -> IO [LitSet]
shortestImplicantsE xs formula = do
  let (tau_formula, info) = dualRailEncoding (IntSet.fromList [1 .. CNF.cnfNumVars formula] IntSet.\\ xs) formula
  solver <- SAT.newSolver
  SAT.newVars_ solver (CNF.cnfNumVars tau_formula)
  forM_ (CNF.cnfClauses tau_formula) $ \c -> do
    SAT.addClause solver (SAT.unpackClause c)

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

-- | Given a CNF formula \(\phi\), this function returns another CNF formula \(\psi\)
-- that is equivalent to \(\neg\phi\).
negateCNF
  :: CNF.CNF    -- ^ \(\phi\)
  -> IO CNF.CNF -- ^ \(\psi \equiv \neg\phi\)
negateCNF formula = do
  implicants <- shortestImplicantsE IntSet.empty formula
  return $
    CNF.CNF
    { CNF.cnfNumVars = CNF.cnfNumVars formula
    , CNF.cnfNumClauses = length implicants
    , CNF.cnfClauses = map (SAT.packClause . map negate . IntSet.toList) implicants
    }

-- | Given a set of variables \(X = \{x_1, \ldots, x_k\}\) and CNF formula \(\phi\),
-- this function computes a CNF formula \(\psi\) that is equivalent to \(\exists X. \phi\)
-- (i.e. \((\exists X. \phi) \leftrightarrow \psi\)).
project
  :: SAT.VarSet  -- ^ \(X\)
  -> CNF.CNF     -- ^ \(\phi\)
  -> IO CNF.CNF  -- ^ \(\psi\)
project xs cnf = do
  let ys = IntSet.fromList [1 .. CNF.cnfNumVars cnf] IntSet.\\ xs
      nv = if IntSet.null ys then 0 else IntSet.findMax ys
  implicants <- shortestImplicantsE xs cnf
  let cnf' =
        CNF.CNF
        { CNF.cnfNumVars = nv
        , CNF.cnfNumClauses = length implicants
        , CNF.cnfClauses = map (SAT.packClause . map negate . IntSet.toList) implicants
        }
  negated_implicates <- shortestImplicantsE xs cnf'
  let implicates = map (SAT.packClause . map negate . IntSet.toList) negated_implicates
  return $
    CNF.CNF
    { CNF.cnfNumVars = nv
    , CNF.cnfNumClauses = length implicates
    , CNF.cnfClauses = implicates
    }
