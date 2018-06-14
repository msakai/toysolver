{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE TypeFamilies #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.Converter.PB
-- Copyright   :  (c) Masahiro Sakai 2013,2016-2018
-- License     :  BSD-style
--
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  experimental
-- Portability :  non-portable
--
-----------------------------------------------------------------------------
module ToySolver.Converter.PB
  ( module ToySolver.Converter.Base
  , module ToySolver.Converter.Tseitin

  -- * Normalization of PB/WBO problems
  , normalizePB
  , normalizeWBO

  -- * Linealization of PB/WBO problems
  , linearizePB
  , linearizeWBO
  , PBLinearizeInfo

  -- * PB↔WBO conversion
  , pb2wbo
  , PB2WBOInfo
  , wbo2pb
  , WBO2PBInfo (..)
  , addWBO

  -- * SAT↔PB conversion
  , sat2pb
  , SAT2PBInfo
  , pb2sat
  , PB2SATInfo

  -- * MaxSAT↔WBO conversion
  , maxsat2wbo
  , MaxSAT2WBOInfo
  , wbo2maxsat
  , WBO2MaxSATInfo
  ) where

import Control.Applicative
import Control.Monad
import Control.Monad.Primitive
import Control.Monad.ST
import Data.Array.IArray
import qualified Data.Foldable as F
import Data.List
import Data.Monoid
import Data.Primitive.MutVar
import qualified Data.Sequence as Seq
import qualified Data.PseudoBoolean as PBFile

import ToySolver.Converter.Base
import ToySolver.Converter.Tseitin
import qualified ToySolver.SAT.Types as SAT
import qualified ToySolver.SAT.Encoder.Tseitin as Tseitin
import qualified ToySolver.SAT.Encoder.PB as PB
import qualified ToySolver.SAT.Encoder.PBNLC as PBNLC
import ToySolver.SAT.Store.CNF
import ToySolver.SAT.Store.PB
import qualified ToySolver.Text.CNF as CNF

-- -----------------------------------------------------------------------------

-- XXX: we do not normalize objective function, because normalization might
-- introduce constant terms, but OPB file format does not allow constant terms.
--
-- Options:
-- (1) not normalize objective function (current implementation),
-- (2) normalize and simply delete constant terms (in pseudo-boolean package?),
-- (3) normalize and introduce dummy variable to make constant terms
--     into non-constant terms (in pseudo-boolean package?).
normalizePB :: PBFile.Formula -> PBFile.Formula
normalizePB formula =
  formula
  { PBFile.pbConstraints =
      map normalizePBConstraint (PBFile.pbConstraints formula)
  }

normalizeWBO :: PBFile.SoftFormula -> PBFile.SoftFormula
normalizeWBO formula =
  formula
  { PBFile.wboConstraints =
      map (\(w,constr) -> (w, normalizePBConstraint constr)) (PBFile.wboConstraints formula)
  }

normalizePBConstraint :: PBFile.Constraint -> PBFile.Constraint
normalizePBConstraint (lhs,op,rhs) =
  case mapAccumL h 0 lhs of
    (offset, lhs') -> (lhs', op, rhs - offset)
  where
    h s (w,[x]) | x < 0 = (s+w, (-w,[-x]))
    h s t = (s,t)

-- -----------------------------------------------------------------------------

type PBLinearizeInfo = TseitinInfo

linearizePB :: PBFile.Formula -> Bool -> (PBFile.Formula, PBLinearizeInfo)
linearizePB formula usePB = runST $ do
  db <- newPBStore
  SAT.newVars_ db (PBFile.pbNumVars formula)
  tseitin <-  Tseitin.newEncoderWithPBLin db
  Tseitin.setUsePB tseitin usePB
  pbnlc <- PBNLC.newEncoder db tseitin
  cs' <- forM (PBFile.pbConstraints formula) $ \(lhs,op,rhs) -> do
    let p = case op of
              PBFile.Ge -> Tseitin.polarityPos
              PBFile.Eq -> Tseitin.polarityBoth
    lhs' <- PBNLC.linearizePBSumWithPolarity pbnlc p lhs
    return ([(c,[l]) | (c,l) <- lhs'],op,rhs)
  obj' <-
    case PBFile.pbObjectiveFunction formula of
      Nothing -> return Nothing
      Just obj -> do
        obj' <- PBNLC.linearizePBSumWithPolarity pbnlc Tseitin.polarityNeg obj
        return $ Just [(c, [l]) | (c,l) <- obj']
  formula' <- getPBFormula db
  defs <- Tseitin.getDefinitions tseitin
  return $
    ( formula'
      { PBFile.pbObjectiveFunction = obj'
      , PBFile.pbConstraints = cs' ++ PBFile.pbConstraints formula'
      , PBFile.pbNumConstraints = PBFile.pbNumConstraints formula + PBFile.pbNumConstraints formula'
      }
    , TseitinInfo (PBFile.pbNumVars formula) (PBFile.pbNumVars formula') defs
    )

-- -----------------------------------------------------------------------------

linearizeWBO :: PBFile.SoftFormula -> Bool -> (PBFile.SoftFormula, PBLinearizeInfo)
linearizeWBO formula usePB = runST $ do
  db <- newPBStore
  SAT.newVars_ db (PBFile.wboNumVars formula)
  tseitin <-  Tseitin.newEncoderWithPBLin db
  Tseitin.setUsePB tseitin usePB
  pbnlc <- PBNLC.newEncoder db tseitin
  cs' <- forM (PBFile.wboConstraints formula) $ \(cost,(lhs,op,rhs)) -> do
    let p = case op of
              PBFile.Ge -> Tseitin.polarityPos
              PBFile.Eq -> Tseitin.polarityBoth
    lhs' <- PBNLC.linearizePBSumWithPolarity pbnlc p lhs
    return (cost,([(c,[l]) | (c,l) <- lhs'],op,rhs))
  formula' <- getPBFormula db
  defs <- Tseitin.getDefinitions tseitin
  return $
    ( PBFile.SoftFormula
      { PBFile.wboTopCost = PBFile.wboTopCost formula
      , PBFile.wboConstraints = cs' ++ [(Nothing, constr) | constr <- PBFile.pbConstraints formula']
      , PBFile.wboNumVars = PBFile.pbNumVars formula'
      , PBFile.wboNumConstraints = PBFile.wboNumConstraints formula + PBFile.pbNumConstraints formula'
      }
    , TseitinInfo (PBFile.wboNumVars formula) (PBFile.pbNumVars formula') defs
    )

-- -----------------------------------------------------------------------------

type PB2WBOInfo = IdentityTransformer SAT.Model

pb2wbo :: PBFile.Formula -> (PBFile.SoftFormula, PB2WBOInfo)
pb2wbo formula
  = ( PBFile.SoftFormula
      { PBFile.wboTopCost = Nothing
      , PBFile.wboConstraints = cs1 ++ cs2
      , PBFile.wboNumVars = PBFile.pbNumVars formula
      , PBFile.wboNumConstraints = PBFile.pbNumConstraints formula + length cs2
      }
    , IdentityTransformer
    )
  where
    cs1 = [(Nothing, c) | c <- PBFile.pbConstraints formula]
    cs2 = case PBFile.pbObjectiveFunction formula of
            Nothing -> []
            Just e  ->
              [ if w >= 0
                then (Just w,       ([(-1,ls)], PBFile.Ge, 0))
                else (Just (abs w), ([(1,ls)],  PBFile.Ge, 1))
              | (w,ls) <- e
              ]

wbo2pb :: PBFile.SoftFormula -> (PBFile.Formula, WBO2PBInfo)
wbo2pb wbo = runST $ do
  let nv = PBFile.wboNumVars wbo
  db <- newPBStore
  (obj, defs) <- addWBO db wbo 
  formula <- getPBFormula db
  return
    ( formula{ PBFile.pbObjectiveFunction = Just obj }
    , WBO2PBInfo nv (PBFile.pbNumVars formula) defs
    )

data WBO2PBInfo = WBO2PBInfo !Int !Int [(SAT.Var, PBFile.Constraint)]

instance Transformer WBO2PBInfo where
  type Source WBO2PBInfo = SAT.Model
  type Target WBO2PBInfo = SAT.Model

instance ForwardTransformer WBO2PBInfo where
  transformForward (WBO2PBInfo _nv1 nv2 defs) m =
    array (1, nv2) $ assocs m ++ [(v, SAT.evalPBConstraint m constr) | (v, constr) <- defs]

instance BackwardTransformer WBO2PBInfo where
  transformBackward (WBO2PBInfo nv1 _nv2 _defs) = SAT.restrictModel nv1

addWBO :: (PrimMonad m, SAT.AddPBNL m enc) => enc -> PBFile.SoftFormula -> m (SAT.PBSum, [(SAT.Var, PBFile.Constraint)])
addWBO db wbo = do
  SAT.newVars_ db $ PBFile.wboNumVars wbo

  objRef <- newMutVar []
  defsRef <- newMutVar []
  forM_ (PBFile.wboConstraints wbo) $ \(cost, constr@(lhs,op,rhs)) -> do
    case cost of
      Nothing -> do
        case op of
          PBFile.Ge -> SAT.addPBNLAtLeast db lhs rhs
          PBFile.Eq -> SAT.addPBNLExactly db lhs rhs
      Just w -> do
        case op of
          PBFile.Ge -> do
            case lhs of
              [(1,ls)] | rhs == 1 -> do
                -- ∧L ≥ 1 ⇔ ∧L
                -- obj += w * (1 - ∧L)
                modifyMutVar objRef (\obj -> (w,[]) : (-w,ls) : obj)
              [(-1,ls)] | rhs == 0 -> do
                -- -1*∧L ≥ 0 ⇔ (1 - ∧L) ≥ 1 ⇔ ￢∧L
                -- obj += w * ∧L
                modifyMutVar objRef ((w,ls) :)
              _ | and [c==1 && length ls == 1 | (c,ls) <- lhs] && rhs == 1 -> do
                -- ∑L ≥ 1 ⇔ ∨L ⇔ ￢∧￢L
                -- obj += w * ∧￢L
                modifyMutVar objRef ((w, [-l | (_,[l]) <- lhs]) :)
              _ -> do
                sel <- SAT.newVar db
                SAT.addPBNLAtLeastSoft db sel lhs rhs
                modifyMutVar objRef ((w,[-sel]) :)
                modifyMutVar defsRef ((sel,constr) :)
          PBFile.Eq -> do
            sel <- SAT.newVar db
            SAT.addPBNLExactlySoft db sel lhs rhs
            modifyMutVar objRef ((w,[-sel]) :)
            modifyMutVar defsRef ((sel,constr) :)
  obj <- liftM reverse $ readMutVar objRef
  defs <- liftM reverse $ readMutVar defsRef

  case PBFile.wboTopCost wbo of
    Nothing -> return ()
    Just t -> SAT.addPBNLAtMost db obj (t - 1)

  return (obj, defs)

-- -----------------------------------------------------------------------------

type SAT2PBInfo = IdentityTransformer SAT.Model

sat2pb :: CNF.CNF -> (PBFile.Formula, SAT2PBInfo)
sat2pb cnf
  = ( PBFile.Formula
      { PBFile.pbObjectiveFunction = Nothing
      , PBFile.pbConstraints = map f (CNF.cnfClauses cnf)
      , PBFile.pbNumVars = CNF.cnfNumVars cnf
      , PBFile.pbNumConstraints = CNF.cnfNumClauses cnf
      }
    , IdentityTransformer
    )
  where
    f clause = ([(1,[l]) | l <- SAT.unpackClause clause], PBFile.Ge, 1)

type PB2SATInfo = TseitinInfo

-- | Convert a pseudo boolean formula φ to a equisatisfiable CNF formula ψ
-- together with two functions f and g such that:
--
-- * if M ⊨ φ then f(M) ⊨ ψ
--
-- * if M ⊨ ψ then g(M) ⊨ φ
-- 
pb2sat :: PBFile.Formula -> (CNF.CNF, PB2SATInfo)
pb2sat formula = runST $ do
  db <- newCNFStore
  let nv1 = PBFile.pbNumVars formula
  SAT.newVars_ db nv1
  tseitin <-  Tseitin.newEncoder db
  pb <- PB.newEncoder tseitin
  pbnlc <- PBNLC.newEncoder pb tseitin
  forM_ (PBFile.pbConstraints formula) $ \(lhs,op,rhs) -> do
    case op of
      PBFile.Ge -> SAT.addPBNLAtLeast pbnlc lhs rhs
      PBFile.Eq -> SAT.addPBNLExactly pbnlc lhs rhs
  cnf <- getCNFFormula db
  defs <- Tseitin.getDefinitions tseitin
  return (cnf, TseitinInfo nv1 (CNF.cnfNumVars cnf) defs)

-- -----------------------------------------------------------------------------

type MaxSAT2WBOInfo = IdentityTransformer SAT.Model

maxsat2wbo :: CNF.WCNF -> (PBFile.SoftFormula, MaxSAT2WBOInfo)
maxsat2wbo
  CNF.WCNF
  { CNF.wcnfTopCost = top
  , CNF.wcnfClauses = cs
  , CNF.wcnfNumVars = nv
  , CNF.wcnfNumClauses = nc
  } =
  ( PBFile.SoftFormula
    { PBFile.wboTopCost = Nothing
    , PBFile.wboConstraints = map f cs
    , PBFile.wboNumVars = nv
    , PBFile.wboNumConstraints = nc
    }
  , IdentityTransformer
  )
  where
    f (w,c)
     | w>=top    = (Nothing, p) -- hard constraint
     | otherwise = (Just w, p)  -- soft constraint
     where
       p = ([(1,[l]) | l <- SAT.unpackClause c], PBFile.Ge, 1)

type WBO2MaxSATInfo = TseitinInfo

wbo2maxsat :: PBFile.SoftFormula -> (CNF.WCNF, WBO2MaxSATInfo)
wbo2maxsat formula = runST $ do
  db <- newCNFStore
  SAT.newVars_ db (PBFile.wboNumVars formula)
  tseitin <-  Tseitin.newEncoder db
  pb <- PB.newEncoder tseitin
  pbnlc <- PBNLC.newEncoder pb tseitin

  softClauses <- liftM mconcat $ forM (PBFile.wboConstraints formula) $ \(cost, (lhs,op,rhs)) -> do
    case cost of
      Nothing ->
        case op of
          PBFile.Ge -> SAT.addPBNLAtLeast pbnlc lhs rhs >> return mempty
          PBFile.Eq -> SAT.addPBNLExactly pbnlc lhs rhs >> return mempty
      Just c -> do
        case op of
          PBFile.Ge -> do
            lhs2 <- PBNLC.linearizePBSumWithPolarity pbnlc Tseitin.polarityPos lhs
            let (lhs3,rhs3) = SAT.normalizePBLinAtLeast (lhs2,rhs)
            if rhs3==1 && and [c==1 | (c,_) <- lhs3] then
              return $ Seq.singleton (c, SAT.packClause [l | (_,l) <- lhs3])
            else do
              lit <- PB.encodePBLinAtLeast pb (lhs3,rhs3)
              return $ Seq.singleton (c, SAT.packClause [lit])
          PBFile.Eq -> do
            lhs2 <- PBNLC.linearizePBSumWithPolarity pbnlc Tseitin.polarityBoth lhs
            lit1 <- PB.encodePBLinAtLeast pb (lhs2, rhs)
            lit2 <- PB.encodePBLinAtLeast pb ([(-c, l) | (c,l) <- lhs2], negate rhs)
            lit <- Tseitin.encodeConjWithPolarity tseitin Tseitin.polarityPos [lit1,lit2]
            return $ Seq.singleton (c, SAT.packClause [lit])

  case PBFile.wboTopCost formula of
    Nothing -> return ()
    Just top -> SAT.addPBNLAtMost pbnlc [(c, [-l | l <- SAT.unpackClause clause]) | (c,clause) <- F.toList softClauses] (top - 1)

  let top = F.sum (fst <$> softClauses) + 1
  cnf <- getCNFFormula db
  let cs = softClauses <> Seq.fromList [(top, clause) | clause <- CNF.cnfClauses cnf]
  let wcnf = CNF.WCNF
             { CNF.wcnfNumVars = CNF.cnfNumVars cnf
             , CNF.wcnfNumClauses = Seq.length cs
             , CNF.wcnfTopCost = top
             , CNF.wcnfClauses = F.toList cs
             }
  defs <- Tseitin.getDefinitions tseitin
  return (wcnf, TseitinInfo (PBFile.wboNumVars formula) (CNF.cnfNumVars cnf) defs)

-- -----------------------------------------------------------------------------
