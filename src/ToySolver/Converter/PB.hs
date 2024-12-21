{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_HADDOCK show-extensions #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE OverloadedStrings #-}
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
  , quadratizePB'
  , PBQuadratizeInfo

  -- * Converting inequality constraints into equality constraints
  , inequalitiesToEqualitiesPB
  , PBInequalitiesToEqualitiesInfo

  -- * Converting constraints into penalty terms in objective function
  , unconstrainPB
  , PBUnconstrainInfo

  -- * PB↔WBO conversion
  , pb2wbo
  , PB2WBOInfo (..)
  , wbo2pb
  , WBO2PBInfo (..)
  , addWBO

  -- * SAT↔PB conversion
  , sat2pb
  , SAT2PBInfo
  , pb2sat
  , pb2satWith
  , PB2SATInfo

  -- * MaxSAT↔WBO conversion
  , maxsat2wbo
  , MaxSAT2WBOInfo (..)
  , wbo2maxsat
  , wbo2maxsatWith
  , WBO2MaxSATInfo

  -- * PB→QUBO conversion
  , pb2qubo'
  , PB2QUBOInfo'
  ) where

import Control.Monad
import Control.Monad.Primitive
import Control.Monad.ST
import qualified Data.Aeson as J
import Data.Aeson ((.=), (.:))
import Data.Array.IArray
import Data.Bits hiding (And (..))
import Data.Default.Class
import qualified Data.Foldable as F
import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IntMap
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import Data.List
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Maybe
import Data.Primitive.MutVar
import qualified Data.Sequence as Seq
import Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.PseudoBoolean as PBFile

import ToySolver.Converter.Base
import qualified ToySolver.Converter.PB.Internal.Product as Product
import ToySolver.Converter.Tseitin
import qualified ToySolver.FileFormat.CNF as CNF
import ToySolver.Internal.JSON
import qualified ToySolver.SAT.Types as SAT
import qualified ToySolver.SAT.Encoder.Tseitin as Tseitin
import ToySolver.SAT.Encoder.Tseitin (Formula (..))
import qualified ToySolver.SAT.Encoder.PB as PB
import qualified ToySolver.SAT.Encoder.PBNLC as PBNLC
import ToySolver.SAT.Internal.JSON
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
quadratizePB formula = quadratizePB' (formula, SAT.pbUpperBound obj)
  where
    obj = fromMaybe [] $ PBFile.pbObjectiveFunction formula

-- | Quandratize PBO/PBS problem without introducing additional constraints.
quadratizePB' :: (PBFile.Formula, Integer) -> ((PBFile.Formula, Integer), PBQuadratizeInfo)
quadratizePB' (formula, maxObj) =
  ( ( PBFile.Formula
      { PBFile.pbObjectiveFunction = Just $ conv obj ++ penalty
      , PBFile.pbConstraints = [(conv lhs, op, rhs) | (lhs,op,rhs) <- PBFile.pbConstraints formula]
      , PBFile.pbNumVars = nv2
      , PBFile.pbNumConstraints = PBFile.pbNumConstraints formula
      }
    , maxObj
    )
  , PBQuadratizeInfo $ TseitinInfo nv1 nv2 (IntMap.fromList [(v, And [atom l1, atom l2]) | (v, (l1,l2)) <- prodDefs])
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

    obj :: PBFile.Sum
    obj = fromMaybe [] $ PBFile.pbObjectiveFunction formula

    minObj :: Integer
    minObj = SAT.pbLowerBound obj

    penalty :: PBFile.Sum
    penalty = [(w * w2, ts) | (w,ts) <- concat [p x y z | (z,(x,y)) <- prodDefs]]
      where
        -- The penalty function P(x,y,z) = xy − 2xz − 2yz + 3z is such that
        -- P(x,y,z)=0 when z⇔xy and P(x,y,z)>0 when z⇎xy.
        p x y z = [(1,[x,y]), (-2,[x,z]), (-2,[y,z]), (3,[z])]
        w2 = max (maxObj - minObj) 0 + 1

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

    atom :: SAT.Lit -> Formula
    atom l
      | l < 0 = Not (Atom (- l))
      | otherwise = Atom l


collectDegGe3Terms :: PBFile.Formula -> Set IntSet
collectDegGe3Terms formula = Set.fromList [t' | t <- terms, let t' = IntSet.fromList t, IntSet.size t' >= 3]
  where
    sums = maybeToList (PBFile.pbObjectiveFunction formula) ++
           [lhs | (lhs,_,_) <- PBFile.pbConstraints formula]
    terms = [t | s <- sums, (_,t) <- s]

newtype PBQuadratizeInfo = PBQuadratizeInfo TseitinInfo
  deriving (Eq, Show)

instance Transformer PBQuadratizeInfo where
  type Source PBQuadratizeInfo = SAT.Model
  type Target PBQuadratizeInfo = SAT.Model

instance ForwardTransformer PBQuadratizeInfo where
  transformForward (PBQuadratizeInfo info) = transformForward info

instance BackwardTransformer PBQuadratizeInfo where
  transformBackward (PBQuadratizeInfo info) = transformBackward info

instance ObjValueTransformer PBQuadratizeInfo where
  type SourceObjValue PBQuadratizeInfo = Integer
  type TargetObjValue PBQuadratizeInfo = Integer

instance ObjValueForwardTransformer PBQuadratizeInfo where
  transformObjValueForward _ = id

instance ObjValueBackwardTransformer PBQuadratizeInfo where
  transformObjValueBackward _ = id

instance J.ToJSON PBQuadratizeInfo where
  toJSON (PBQuadratizeInfo info) =
    J.object
    [ "type" .= ("PBQuadratizeInfo" :: J.Value)
    , "base" .= info
    ]

instance J.FromJSON PBQuadratizeInfo where
  parseJSON = withTypedObject "PBQuadratizeInfo" $ \obj ->
    PBQuadratizeInfo <$> obj .: "base"

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
        case asClause (lhs,rhs) of
          Just clause -> do
            SAT.addPBNLExactly db [(1, [- l | l <- clause])] 0
            return Nothing
          Nothing -> do
            let maxSurpass = max (SAT.pbUpperBound lhs - rhs) 0
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
  where
    asLinSum :: SAT.PBSum -> Maybe (SAT.PBLinSum, Integer)
    asLinSum s = do
      ret <- forM s $ \(c, ls) -> do
        case ls of
          [] -> return (Nothing, c)
          [l] -> return (Just (c,l), 0)
          _ -> mzero
      return (catMaybes (map fst ret), sum (map snd ret))

    asClause :: (SAT.PBSum, Integer) -> Maybe SAT.Clause
    asClause (lhs, rhs) = do
      (lhs', off) <- asLinSum lhs
      let rhs' = rhs - off
      case SAT.normalizePBLinAtLeast (lhs', rhs') of
        (lhs'', 1) | all (\(c,_) -> c == 1) lhs'' -> return (map snd lhs'')
        _ -> mzero

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

instance J.ToJSON PBInequalitiesToEqualitiesInfo where
  toJSON (PBInequalitiesToEqualitiesInfo nv1 nv2 defs) =
    J.object
    [ "type" .= ("PBInequalitiesToEqualitiesInfo" :: J.Value)
    , "num_original_variables" .= nv1
    , "num_transformed_variables" .= nv2
    , "slack" .=
        [ J.object
          [ "lhs" .= jPBSum lhs
          , "rhs" .= rhs
          , "slack" .= [jVarName v :: J.Value | v <- vs]
          ]
        | (lhs, rhs, vs) <- defs
        ]
    ]

instance J.FromJSON PBInequalitiesToEqualitiesInfo where
  parseJSON = withTypedObject "PBInequalitiesToEqualitiesInfo" $ \obj -> do
    PBInequalitiesToEqualitiesInfo
      <$> obj .: "num_original_variables"
      <*> obj .: "num_transformed_variables"
      <*> (mapM f =<< obj .: "slack")
    where
      f = J.withObject "slack" $ \obj -> do
        lhs <- parsePBSum =<< obj .: "lhs"
        rhs <- obj .: "rhs"
        vs <- mapM g =<< obj .: "slack"
        return (lhs, rhs, vs)
      g ('x' : rest) = pure $! read rest
      g s = fail ("fail to parse variable: " ++ show s)

-- -----------------------------------------------------------------------------

unconstrainPB :: PBFile.Formula -> ((PBFile.Formula, Integer), PBUnconstrainInfo)
unconstrainPB formula = (unconstrainPB' formula', PBUnconstrainInfo info)
  where
    (formula', info) = inequalitiesToEqualitiesPB formula

newtype PBUnconstrainInfo = PBUnconstrainInfo PBInequalitiesToEqualitiesInfo
  deriving (Eq, Show)

instance Transformer PBUnconstrainInfo where
  -- type Source PBUnconstrainInfo = Source PBInequalitiesToEqualitiesInfo
  type Source PBUnconstrainInfo = SAT.Model
  -- type Target PBUnconstrainInfo = Target PBInequalitiesToEqualitiesInfo
  type Target PBUnconstrainInfo = SAT.Model

instance ForwardTransformer PBUnconstrainInfo where
  transformForward (PBUnconstrainInfo info) = transformForward info

instance BackwardTransformer PBUnconstrainInfo where
  transformBackward (PBUnconstrainInfo info) = transformBackward info

instance ObjValueTransformer PBUnconstrainInfo where
  -- type SourceObjValue PBUnconstrainInfo = SourceObjValue PBInequalitiesToEqualitiesInfo
  type SourceObjValue PBUnconstrainInfo = Integer
  -- type TargetObjValue PBUnconstrainInfo = TargetObjValue PBInequalitiesToEqualitiesInfo
  type TargetObjValue PBUnconstrainInfo = Integer

instance ObjValueForwardTransformer PBUnconstrainInfo where
  transformObjValueForward (PBUnconstrainInfo info) = transformObjValueForward info

instance ObjValueBackwardTransformer PBUnconstrainInfo where
  transformObjValueBackward (PBUnconstrainInfo info) = transformObjValueBackward info

instance J.ToJSON PBUnconstrainInfo where
  toJSON (PBUnconstrainInfo info) =
    J.object
    [ "type" .= ("PBUnconstrainInfo" :: J.Value)
    , "base" .= info
    ]

instance J.FromJSON PBUnconstrainInfo where
  parseJSON = withTypedObject "PBUnconstrainInfo" $ \obj ->
    PBUnconstrainInfo <$> obj .: "base"

unconstrainPB' :: PBFile.Formula -> (PBFile.Formula, Integer)
unconstrainPB' formula =
  ( formula
    { PBFile.pbObjectiveFunction = Just $ obj1 ++ obj2
    , PBFile.pbConstraints = []
    , PBFile.pbNumConstraints = 0
    }
  , obj1ub
  )
  where
    obj1 = fromMaybe [] (PBFile.pbObjectiveFunction formula)
    obj1ub = SAT.pbUpperBound obj1
    obj1lb = SAT.pbLowerBound obj1
    p = obj1ub - obj1lb + 1
    obj2 = [(p*c, IntSet.toList ls) | (ls, c) <- Map.toList obj2', c /= 0]
    obj2' = Map.unionsWith (+) [sq ((-rhs, []) : lhs) | (lhs, PBFile.Eq, rhs) <- PBFile.pbConstraints formula]
    sq ts = Map.fromListWith (+) $ do
              (c1,ls1) <- ts
              (c2,ls2) <- ts
              let ls3 = IntSet.fromList ls1 `IntSet.union` IntSet.fromList ls2
              guard $ not $ isFalse ls3
              return (ls3, c1*c2)
    isFalse ls = not $ IntSet.null $ ls `IntSet.intersection` IntSet.map negate ls

-- -----------------------------------------------------------------------------

pb2qubo' :: PBFile.Formula -> ((PBFile.Formula, Integer), PB2QUBOInfo')
pb2qubo' formula = ((formula2, th2), ComposedTransformer info1 info2)
  where
    ((formula1, th1), info1) = unconstrainPB formula
    ((formula2, th2), info2) = quadratizePB' (formula1, th1)

type PB2QUBOInfo' = ComposedTransformer PBUnconstrainInfo PBQuadratizeInfo

-- -----------------------------------------------------------------------------

pb2wbo :: PBFile.Formula -> (PBFile.SoftFormula, PB2WBOInfo)
pb2wbo formula
  = ( PBFile.SoftFormula
      { PBFile.wboTopCost = Nothing
      , PBFile.wboConstraints = cs1 ++ cs2
      , PBFile.wboNumVars = PBFile.pbNumVars formula
      , PBFile.wboNumConstraints = PBFile.pbNumConstraints formula + length cs2
      }
    , PB2WBOInfo offset
    )
  where
    cs1 = [(Nothing, c) | c <- PBFile.pbConstraints formula]
    (cs2, offset) =
      case PBFile.pbObjectiveFunction formula of
        Nothing -> ([], 0)
        Just e  ->
          ( [ if w >= 0
              then (Just w,       ([(-1,ls)], PBFile.Ge, 0))
              else (Just (abs w), ([(1,ls)],  PBFile.Ge, 1))
            | (w,ls) <- e
            ]
          , sum [if w >= 0 then 0 else - w | (w, _) <- e]
          )

newtype PB2WBOInfo = PB2WBOInfo Integer
  deriving (Eq, Show)

instance Transformer PB2WBOInfo where
  type Source PB2WBOInfo = SAT.Model
  type Target PB2WBOInfo = SAT.Model

instance ForwardTransformer PB2WBOInfo where
  transformForward _ = id

instance BackwardTransformer PB2WBOInfo where
  transformBackward _ = id

instance ObjValueTransformer PB2WBOInfo where
  type SourceObjValue PB2WBOInfo = Integer
  type TargetObjValue PB2WBOInfo = Integer

instance ObjValueForwardTransformer PB2WBOInfo where
  transformObjValueForward (PB2WBOInfo offset) obj = obj + offset

instance ObjValueBackwardTransformer PB2WBOInfo where
  transformObjValueBackward (PB2WBOInfo offset) obj = obj - offset

instance J.ToJSON PB2WBOInfo where
  toJSON (PB2WBOInfo offset) =
    J.object
    [ "type" .= J.String "PB2WBOInfo"
    , "objective_function_offset" .= offset
    ]

instance J.FromJSON PB2WBOInfo where
  parseJSON =
    withTypedObject "PB2WBOInfo" $ \obj -> do
      offset <- obj .: "objective_function_offset"
      pure (PB2WBOInfo offset)

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

data WBO2PBInfo = WBO2PBInfo !Int !Int (SAT.VarMap PBFile.Constraint)
  deriving (Show, Eq)

instance Transformer WBO2PBInfo where
  type Source WBO2PBInfo = SAT.Model
  type Target WBO2PBInfo = SAT.Model

instance ForwardTransformer WBO2PBInfo where
  transformForward (WBO2PBInfo _nv1 nv2 defs) m =
    array (1, nv2) $ assocs m ++ [(v, SAT.evalPBConstraint m constr) | (v, constr) <- IntMap.toList defs]

instance BackwardTransformer WBO2PBInfo where
  transformBackward (WBO2PBInfo nv1 _nv2 _defs) = SAT.restrictModel nv1

instance ObjValueTransformer WBO2PBInfo where
  type SourceObjValue WBO2PBInfo = Integer
  type TargetObjValue WBO2PBInfo = Integer

instance ObjValueForwardTransformer WBO2PBInfo where
  transformObjValueForward _ = id

instance ObjValueBackwardTransformer WBO2PBInfo where
  transformObjValueBackward _ = id

instance J.ToJSON WBO2PBInfo where
  toJSON (WBO2PBInfo nv1 nv2 defs) =
    J.object
    [ "type" .= J.String "WBO2PBInfo"
    , "num_original_variables" .= nv1
    , "num_transformed_variables" .= nv2
    , "definitions" .= J.object
        [ jVarName v .= jPBConstraint constr
        | (v, constr) <- IntMap.toList defs
        ]
    ]

instance J.FromJSON WBO2PBInfo where
  parseJSON = withTypedObject "WBO2PBInfo" $ \obj -> do
    defs <- obj .: "definitions"
    WBO2PBInfo
      <$> obj .: "num_original_variables"
      <*> obj .: "num_transformed_variables"
      <*> (IntMap.fromList <$> mapM f (Map.toList defs))
    where
      f (name, constr) = do
        v <- parseVarNameText name
        constr' <- parsePBConstraint constr
        return (v, constr')

addWBO :: (PrimMonad m, SAT.AddPBNL m enc) => enc -> PBFile.SoftFormula -> m (SAT.PBSum, (SAT.VarMap PBFile.Constraint))
addWBO db wbo = do
  SAT.newVars_ db $ PBFile.wboNumVars wbo

  objRef <- newMutVar []
  objOffsetRef <- newMutVar 0
  defsRef <- newMutVar []
  trueLitRef <- newMutVar SAT.litUndef

  forM_ (PBFile.wboConstraints wbo) $ \(cost, constr@(lhs,op,rhs)) -> do
    case cost of
      Nothing -> do
        case op of
          PBFile.Ge -> SAT.addPBNLAtLeast db lhs rhs
          PBFile.Eq -> SAT.addPBNLExactly db lhs rhs
        trueLit <- readMutVar trueLitRef
        when (trueLit == SAT.litUndef) $ do
          case detectTrueLit constr of
            Nothing -> return ()
            Just l -> writeMutVar trueLitRef l
      Just w -> do
        case op of
          PBFile.Ge -> do
            case lhs of
              [(c,ls)] | c > 0 && (rhs + c - 1) `div` c == 1 -> do
                -- c ∧L ≥ rhs ⇔ ∧L ≥ ⌈rhs / c⌉
                -- ∧L ≥ 1 ⇔ ∧L
                -- obj += w * (1 - ∧L)
                unless (null ls) $ do
                  modifyMutVar objRef (\obj -> (-w,ls) : obj)
                  modifyMutVar objOffsetRef (+ w)
              [(c,ls)] | c < 0 && (rhs + abs c - 1) `div` abs c + 1 == 1 -> do
                -- c*∧L ≥ rhs ⇔ -1*∧L ≥ ⌈rhs / abs c⌉ ⇔ (1 - ∧L) ≥ ⌈rhs / abs c⌉ + 1 ⇔ ¬∧L ≥ ⌈rhs / abs c⌉ + 1
                -- ￢∧L ≥ 1 ⇔ ￢∧L
                -- obj += w * ∧L
                if null ls then do
                  modifyMutVar objOffsetRef (+ w)
                else do
                  modifyMutVar objRef ((w,ls) :)
              _ | rhs > 0 && and [c >= rhs && length ls == 1 | (c,ls) <- lhs] -> do
                -- ∑L ≥ 1 ⇔ ∨L ⇔ ￢∧￢L
                -- obj += w * ∧￢L
                if null lhs then do
                  modifyMutVar objOffsetRef (+ w)
                else do
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

  offset <- readMutVar objOffsetRef
  when (offset /= 0) $ do
    l <- readMutVar trueLitRef
    trueLit <-
      if l /= SAT.litUndef then
        return l
      else do
        v <- SAT.newVar db
        SAT.addClause db [v]
        modifyMutVar defsRef ((v, ([], PBFile.Ge, 0)) :)
        return v
    modifyMutVar objRef ((offset,[trueLit]) :)

  obj <- liftM reverse $ readMutVar objRef
  defs <- liftM IntMap.fromList $ readMutVar defsRef

  case PBFile.wboTopCost wbo of
    Nothing -> return ()
    Just t -> SAT.addPBNLAtMost db obj (t - 1)

  return (obj, defs)


detectTrueLit :: PBFile.Constraint -> Maybe SAT.Lit
detectTrueLit (lhs, op, rhs) =
  case op of
    PBFile.Ge -> f lhs rhs
    PBFile.Eq -> f lhs rhs `mplus` f [(- c, ls) | (c,ls) <- lhs] (- rhs)
  where
    f [(c, [l])] rhs
      | c > 0 && (rhs + c - 1) `div` c == 1 =
          -- c l ≥ rhs ↔ l ≥ ⌈rhs / c⌉
          return l
      | c < 0 && rhs `div` c == 0 =
          -- c l ≥ rhs ↔ l ≤ ⌊rhs / c⌋
          return (- l)
    f _ _ = Nothing

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
pb2sat = pb2satWith def

pb2satWith :: PB.Strategy -> PBFile.Formula -> (CNF.CNF, PB2SATInfo)
pb2satWith strategy formula = runST $ do
  db <- newCNFStore
  let nv1 = PBFile.pbNumVars formula
  SAT.newVars_ db nv1
  tseitin <-  Tseitin.newEncoder db
  pb <- PB.newEncoderWithStrategy tseitin strategy
  pbnlc <- PBNLC.newEncoder pb tseitin
  forM_ (PBFile.pbConstraints formula) $ \(lhs,op,rhs) -> do
    case op of
      PBFile.Ge -> SAT.addPBNLAtLeast pbnlc lhs rhs
      PBFile.Eq -> SAT.addPBNLExactly pbnlc lhs rhs
  cnf <- getCNFFormula db
  defs <- Tseitin.getDefinitions tseitin
  return (cnf, TseitinInfo nv1 (CNF.cnfNumVars cnf) defs)

-- -----------------------------------------------------------------------------

data MaxSAT2WBOInfo = MaxSAT2WBOInfo
  deriving (Show, Eq)

instance Transformer MaxSAT2WBOInfo where
  type Source MaxSAT2WBOInfo = SAT.Model
  type Target MaxSAT2WBOInfo = SAT.Model

instance ForwardTransformer MaxSAT2WBOInfo where
  transformForward _ = id

instance BackwardTransformer MaxSAT2WBOInfo where
  transformBackward _ = id

instance ObjValueTransformer MaxSAT2WBOInfo where
  type SourceObjValue MaxSAT2WBOInfo = Integer
  type TargetObjValue MaxSAT2WBOInfo = Integer

instance ObjValueForwardTransformer MaxSAT2WBOInfo where
  transformObjValueForward _ = id

instance ObjValueBackwardTransformer MaxSAT2WBOInfo where
  transformObjValueBackward _ = id

instance J.ToJSON MaxSAT2WBOInfo where
  toJSON MaxSAT2WBOInfo =
    J.object
    [ "type" .= ("MaxSAT2WBOInfo" :: J.Value)
    ]

instance J.FromJSON MaxSAT2WBOInfo where
  parseJSON = withTypedObject "MaxSAT2WBOInfo" $ \_ -> pure MaxSAT2WBOInfo

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
  , MaxSAT2WBOInfo
  )
  where
    f (w,c)
     | w>=top    = (Nothing, p) -- hard constraint
     | otherwise = (Just w, p)  -- soft constraint
     where
       p = ([(1,[l]) | l <- SAT.unpackClause c], PBFile.Ge, 1)

newtype WBO2MaxSATInfo = WBO2MaxSATInfo TseitinInfo
  deriving (Show, Eq)

instance Transformer WBO2MaxSATInfo where
  type Source WBO2MaxSATInfo = SAT.Model
  type Target WBO2MaxSATInfo = SAT.Model

instance ForwardTransformer WBO2MaxSATInfo where
  transformForward (WBO2MaxSATInfo info) = transformForward info

instance BackwardTransformer WBO2MaxSATInfo where
  transformBackward (WBO2MaxSATInfo info) = transformBackward info

instance ObjValueTransformer WBO2MaxSATInfo where
  type SourceObjValue WBO2MaxSATInfo = Integer
  type TargetObjValue WBO2MaxSATInfo = Integer

instance ObjValueForwardTransformer WBO2MaxSATInfo where
  transformObjValueForward (WBO2MaxSATInfo _) = id

instance ObjValueBackwardTransformer WBO2MaxSATInfo where
  transformObjValueBackward (WBO2MaxSATInfo _) = id

instance J.ToJSON WBO2MaxSATInfo where
  toJSON (WBO2MaxSATInfo info) =
    J.object
    [ "type" .= ("WBO2MaxSATInfo" :: J.Value)
    , "base" .= info
    ]

instance J.FromJSON WBO2MaxSATInfo where
  parseJSON = withTypedObject "WBO2MaxSATInfo" $ \obj ->
    WBO2MaxSATInfo <$> (obj .: "base")

wbo2maxsat :: PBFile.SoftFormula -> (CNF.WCNF, WBO2MaxSATInfo)
wbo2maxsat = wbo2maxsatWith def

wbo2maxsatWith :: PB.Strategy -> PBFile.SoftFormula -> (CNF.WCNF, WBO2MaxSATInfo)
wbo2maxsatWith strategy formula = runST $ do
  db <- newCNFStore
  SAT.newVars_ db (PBFile.wboNumVars formula)
  tseitin <-  Tseitin.newEncoder db
  pb <- PB.newEncoderWithStrategy tseitin strategy
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
  return (wcnf, WBO2MaxSATInfo (TseitinInfo (PBFile.wboNumVars formula) (CNF.cnfNumVars cnf) defs))

-- -----------------------------------------------------------------------------
