{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE CPP #-}
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

  -- * Quadratization of PB problems
  , quadratizePB
  , PBQuadratizeInfo

  -- * Converting inequality constraints into equality constraints
  , inequalitiesToEqualitiesPB
  , PBInequalitiesToEqualitiesInfo

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

import Control.Monad
import Control.Monad.Primitive
import Control.Monad.ST
import Data.Array.IArray
import Data.Bits
import qualified Data.Foldable as F
import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IntMap
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import Data.List
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Maybe
#if !MIN_VERSION_base(4,11,0)
import Data.Monoid
#endif
import Data.Primitive.MutVar
import qualified Data.Sequence as Seq
import Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.PseudoBoolean as PBFile

import ToySolver.Converter.Base
import qualified ToySolver.Converter.PB.Internal.Product as Product
import ToySolver.Converter.Tseitin
import ToySolver.Data.BoolExpr
import qualified ToySolver.FileFormat.CNF as CNF
import qualified ToySolver.SAT.Types as SAT
import qualified ToySolver.SAT.Encoder.Tseitin as Tseitin
import qualified ToySolver.SAT.Encoder.PB as PB
import qualified ToySolver.SAT.Encoder.PBNLC as PBNLC
import ToySolver.SAT.Store.CNF
import ToySolver.SAT.Store.PB

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

-- | Quandratize PBO/PBS problem without introducing additional constraints.
quadratizePB :: PBFile.Formula -> ((PBFile.Formula, Integer), PBQuadratizeInfo)
quadratizePB formula = 
  ( ( PBFile.Formula
      { PBFile.pbObjectiveFunction = Just $
          conv (fromMaybe [] (PBFile.pbObjectiveFunction formula)) ++ penalty
      , PBFile.pbConstraints = [(conv lhs, op, rhs) | (lhs,op,rhs) <- PBFile.pbConstraints formula]
      , PBFile.pbNumVars = nv2
      , PBFile.pbNumConstraints = PBFile.pbNumConstraints formula
      }
    , maxObj
    )
  , TseitinInfo nv1 nv2 [(v, And [Atom l1, Atom l2]) | (v, (l1,l2)) <- prodDefs]
  )
  where
    nv1 = PBFile.pbNumVars formula
    nv2 = PBFile.pbNumVars formula + Set.size termsToReplace

    degGe3Terms :: Set IntSet
    degGe3Terms = collectDegGe3Terms formula
 
    m :: Map IntSet (IntSet,IntSet)
    m = Product.decomposeToBinaryProducts degGe3Terms

    termsToReplace :: Set IntSet
    termsToReplace = go ts0 Set.empty
      where
        ts0 = concat [[t1,t2] | t <- Set.toList degGe3Terms, let (t1,t2) = m Map.! t]
        go [] !ret = ret
        go (t : ts) !ret
          | IntSet.size t < 2  = go ts ret
          | t `Set.member` ret = go ts ret
          | otherwise =
              case Map.lookup t m of
                Nothing -> error "quadratizePB.termsToReplace: should not happen"
                Just (t1,t2) -> go (t1 : t2 : ts) (Set.insert t ret)

    fromV :: IntMap IntSet
    toV :: Map IntSet Int
    (fromV, toV) = (IntMap.fromList l, Map.fromList [(s,v) | (v,s) <- l])
      where
        l = zip [PBFile.pbNumVars formula + 1 ..] (Set.toList termsToReplace)

    prodDefs :: [(SAT.Var, (SAT.Var, SAT.Var))]
    prodDefs = [(v, (f t1, f t2)) | (v,t) <- IntMap.toList fromV, let (t1,t2) = m Map.! t]
      where
        f t
          | IntSet.size t == 1 = head (IntSet.toList t)
          | otherwise = 
               case Map.lookup t toV of
                 Nothing -> error "quadratizePB.prodDefs: should not happen"
                 Just v -> v

    maxObj :: Integer
    maxObj = sum [max 0 w | (w,_) <- fromMaybe [] (PBFile.pbObjectiveFunction formula)]

    minObj :: Integer
    minObj = sum [min 0 w | (w,_) <- fromMaybe [] (PBFile.pbObjectiveFunction formula)]

    penalty :: PBFile.Sum
    penalty = [(w * w2, ts) | (w,ts) <- concat [p x y z | (z,(x,y)) <- prodDefs]]
      where
        -- The penalty function P(x,y,z) = xy − 2xz − 2yz + 3z is such that
        -- P(x,y,z)=0 when z⇔xy and P(x,y,z)>0 when z⇎xy.
        p x y z = [(1,[x,y]), (-2,[x,z]), (-2,[y,z]), (3,[z])]
        w2 = maxObj - minObj + 1

    conv :: PBFile.Sum -> PBFile.Sum
    conv s = [(w, f t) | (w,t) <- s]
      where
        f t =
          case Map.lookup t' toV of
            Just v  -> [v]
            Nothing
              | IntSet.size t' >= 3 -> map g [t1, t2]
              | otherwise -> t
          where
            t' = IntSet.fromList t
            (t1, t2) = m Map.! t'
        g t
          | IntSet.size t == 1 = head $ IntSet.toList t
          | otherwise = toV Map.! t


collectDegGe3Terms :: PBFile.Formula -> Set IntSet
collectDegGe3Terms formula = Set.fromList [t' | t <- terms, let t' = IntSet.fromList t, IntSet.size t' >= 3]
  where
    sums = maybeToList (PBFile.pbObjectiveFunction formula) ++
           [lhs | (lhs,_,_) <- PBFile.pbConstraints formula]
    terms = [t | s <- sums, (_,t) <- s]

type PBQuadratizeInfo = TseitinInfo

-- -----------------------------------------------------------------------------

-- | Convert inequality constraints into equality constraints by introducing surpass variables.
inequalitiesToEqualitiesPB :: PBFile.Formula -> (PBFile.Formula, PBInequalitiesToEqualitiesInfo)
inequalitiesToEqualitiesPB formula = runST $ do
  db <- newPBStore
  SAT.newVars_ db (PBFile.pbNumVars formula)

  defs <- liftM catMaybes $ forM (PBFile.pbConstraints formula) $ \constr -> do
    case constr of
      (lhs, PBFile.Eq, rhs) -> do
        SAT.addPBNLExactly db lhs rhs
        return Nothing
      (lhs, PBFile.Ge, rhs) -> do
        let ub = sum [c | (c, _) <- lhs, c >= 0]
            maxSurpass = max (ub - rhs) 0
            maxSurpassNBits = head [i | i <- [0..], maxSurpass < bit i]
        vs <- SAT.newVars db maxSurpassNBits
        SAT.addPBNLExactly db (lhs ++ [(-c,[x]) | (c,x) <- zip (iterate (*2) 1) vs]) rhs
        if maxSurpassNBits > 0 then do
          return $ Just (lhs, rhs, vs)
        else
          return Nothing

  formula' <- getPBFormula db
  return
    ( formula'{ PBFile.pbObjectiveFunction = PBFile.pbObjectiveFunction formula }
    , PBInequalitiesToEqualitiesInfo (PBFile.pbNumVars formula) (PBFile.pbNumVars formula') defs
    )

data PBInequalitiesToEqualitiesInfo
  = PBInequalitiesToEqualitiesInfo !Int !Int [(PBFile.Sum, Integer, [SAT.Var])]
  deriving (Eq, Show)

instance Transformer PBInequalitiesToEqualitiesInfo where
  type Source PBInequalitiesToEqualitiesInfo = SAT.Model
  type Target PBInequalitiesToEqualitiesInfo = SAT.Model

instance ForwardTransformer PBInequalitiesToEqualitiesInfo where
  transformForward (PBInequalitiesToEqualitiesInfo _nv1 nv2 defs) m =
    array (1, nv2) $ assocs m ++ [(v, testBit n i) | (lhs, rhs, vs) <- defs, let n = SAT.evalPBSum m lhs - rhs, (i,v) <- zip [0..] vs]

instance BackwardTransformer PBInequalitiesToEqualitiesInfo where
  transformBackward (PBInequalitiesToEqualitiesInfo nv1 _nv2 _defs) = SAT.restrictModel nv1

instance ObjValueTransformer PBInequalitiesToEqualitiesInfo where
  type SourceObjValue PBInequalitiesToEqualitiesInfo = Integer
  type TargetObjValue PBInequalitiesToEqualitiesInfo = Integer

instance ObjValueForwardTransformer PBInequalitiesToEqualitiesInfo where
  transformObjValueForward _ = id

instance ObjValueBackwardTransformer PBInequalitiesToEqualitiesInfo where
  transformObjValueBackward _ = id

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
  deriving (Eq, Show)

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
