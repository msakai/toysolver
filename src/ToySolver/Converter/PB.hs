{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_HADDOCK show-extensions #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeFamilies #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.Converter.PB
-- Copyright   :  (c) Masahiro Sakai 2011-2014,2016-2018
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

  -- * Modify objective function
  , ObjType (..)
  , setObj

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
  , PBInequalitiesToEqualitiesInfo (..)

  -- * Converting constraints into penalty terms in objective function
  , unconstrainPB
  , PBUnconstrainInfo (..)

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
  , MaxSAT2WBOInfo
  , wbo2maxsat
  , wbo2maxsatWith
  , WBO2MaxSATInfo

  -- * PB→QUBO conversion
  , pb2qubo'
  , PB2QUBOInfo'

  -- * General data types
  , PBIdentityInfo (..)
  , PBTseitinInfo (..)

  -- * misc
  , pb2lsp
  , wbo2lsp
  , pb2smp
  ) where

import Control.Monad
import Control.Monad.Primitive
import Control.Monad.ST
import qualified Data.Aeson as J
import Data.Aeson ((.=), (.:))
import Data.Array.IArray
import Data.ByteString.Builder
import Data.Default.Class
import qualified Data.Foldable as F
import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IntMap
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import Data.List (foldl', foldl1', intersperse)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Maybe
import Data.Primitive.MutVar
import qualified Data.Sequence as Seq
import Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.PseudoBoolean as PBFile
import qualified Data.Vector as V
import qualified Data.Vector.Generic as VG

import ToySolver.Data.Boolean (true)
import ToySolver.Converter.Base
import qualified ToySolver.Combinatorial.SubsetSum as SubsetSum
import qualified ToySolver.Converter.PB.Internal.Product as Product
import ToySolver.Converter.Tseitin
import qualified ToySolver.FileFormat.CNF as CNF
import ToySolver.Internal.JSON
import qualified ToySolver.SAT.Types as SAT
import qualified ToySolver.SAT.Encoder.Integer as Integer
import qualified ToySolver.SAT.Encoder.Tseitin as Tseitin
import ToySolver.SAT.Encoder.Tseitin (Formula (..))
import qualified ToySolver.SAT.Encoder.PB as PB
import qualified ToySolver.SAT.Encoder.PBNLC as PBNLC
import ToySolver.SAT.Internal.JSON
import ToySolver.SAT.Store.CNF
import ToySolver.SAT.Store.PB

-- -----------------------------------------------------------------------------

-- | Normalize 'PBFile.Formula' to be suitable for writing as OPB file.
--
-- This may introduce a new variable.
normalizePB :: PBFile.Formula -> (PBFile.Formula, PBTseitinInfo)
normalizePB formula =
  case PBFile.pbObjectiveFunction formula of
    Nothing ->
      ( formula{ PBFile.pbConstraints = cs }
      , PBTseitinInfo (TseitinInfo nv nv IntMap.empty)
      )
    Just obj | (obj', offset) <- normalizePBSum obj ->
      if offset == 0 then
        ( formula
          { PBFile.pbObjectiveFunction = Just obj'
          , PBFile.pbConstraints = cs
          }
        , PBTseitinInfo (TseitinInfo nv nv IntMap.empty)
        )
      else
        case msum [detectTrueVar c | c <- cs] of
          Just v ->
            ( formula
              { PBFile.pbObjectiveFunction = Just (obj' ++ [(offset, [v])])
              , PBFile.pbConstraints = cs
              }
            , PBTseitinInfo (TseitinInfo nv nv IntMap.empty)
            )
          Nothing ->
            let v = nv + 1
             in ( formula
                  { PBFile.pbObjectiveFunction = Just (obj' ++ [(offset, [v])])
                  , PBFile.pbConstraints = cs ++ [([(1, [v])], PBFile.Ge, 1)]
                  , PBFile.pbNumVars = v
                  }
                , PBTseitinInfo (TseitinInfo nv v (IntMap.singleton v true))
                )
  where
    cs = map normalizePBConstraint (PBFile.pbConstraints formula)
    nv = PBFile.pbNumVars formula

detectTrueVar :: PBFile.Constraint -> Maybe SAT.Var
detectTrueVar (lhs, op, rhs) =
  case op of
    PBFile.Ge -> f lhs rhs
    PBFile.Eq -> f lhs rhs `mplus` f [(- c, ls) | (c,ls) <- lhs] (- rhs)
  where
    f [(c, ls)] rhs
      | c > 0 && (rhs + c - 1) `div` c >= 1 =
          -- c L ≥ rhs ↔ L ≥ ⌈rhs / c⌉
          listToMaybe [l | l <- ls, l > 0]
    f _ _ = Nothing

-- | Normalize 'PBFile.SoftFormula' to be suitable for writing as WBO file.
normalizeWBO :: PBFile.SoftFormula -> PBFile.SoftFormula
normalizeWBO formula =
  formula
  { PBFile.wboConstraints =
      map (\(w,constr) -> (w, normalizePBConstraint constr)) (PBFile.wboConstraints formula)
  }

normalizePBConstraint :: PBFile.Constraint -> PBFile.Constraint
normalizePBConstraint (lhs,op,rhs) =
  case normalizePBSum lhs of
    (lhs', offset) -> (lhs', op, rhs - offset)

normalizePBSum :: PBFile.Sum -> (PBFile.Sum, Integer)
normalizePBSum s =
  case foldl' h ([], 0) s of
    (s', offset) -> (reverse s', offset)
  where
    h (s', offset) (0,_) = (s', offset)
    h (s', offset) (w,[x]) | x < 0 = ((-w,[-x]) : s', offset+w)
    h (s', offset) (w,[]) = (s', offset + w)
    h (s', offset) t = (t : s', offset)

-- -----------------------------------------------------------------------------

data ObjType = ObjNone | ObjMaxOne | ObjMaxZero
  deriving (Eq, Ord, Enum, Bounded, Show)

setObj :: ObjType -> PBFile.Formula -> PBFile.Formula
setObj objType formula = formula{ PBFile.pbObjectiveFunction = Just obj2 }
  where
    obj2 = genObj objType formula

genObj :: ObjType -> PBFile.Formula -> PBFile.Sum
genObj objType formula =
  case objType of
    ObjNone    -> []
    ObjMaxOne  -> [(1,[-v]) | v <- [1 .. PBFile.pbNumVars formula]] -- minimize false literals
    ObjMaxZero -> [(1,[ v]) | v <- [1 .. PBFile.pbNumVars formula]] -- minimize true literals

-- -----------------------------------------------------------------------------

data PBIdentityInfo = PBIdentityInfo
  deriving (Show, Eq)

instance Transformer PBIdentityInfo where
  type Source PBIdentityInfo = SAT.Model
  type Target PBIdentityInfo = SAT.Model

instance ForwardTransformer PBIdentityInfo where
  transformForward _ = id

instance BackwardTransformer PBIdentityInfo where
  transformBackward _ = id

instance ObjValueTransformer PBIdentityInfo where
  type SourceObjValue PBIdentityInfo = Integer
  type TargetObjValue PBIdentityInfo = Integer

instance ObjValueForwardTransformer PBIdentityInfo where
  transformObjValueForward _ = id

instance ObjValueBackwardTransformer PBIdentityInfo where
  transformObjValueBackward _ = id

instance J.ToJSON PBIdentityInfo where
  toJSON PBIdentityInfo =
    J.object
    [ "type" .= ("PBIdentityInfo" :: J.Value)
    ]

instance J.FromJSON PBIdentityInfo where
  parseJSON = withTypedObject "PBIdentityInfo" $ \_ -> pure PBIdentityInfo


newtype PBTseitinInfo = PBTseitinInfo TseitinInfo
  deriving (Eq, Show)

instance Transformer PBTseitinInfo where
  type Source PBTseitinInfo = SAT.Model
  type Target PBTseitinInfo = SAT.Model

instance ForwardTransformer PBTseitinInfo where
  transformForward (PBTseitinInfo info) = transformForward info

instance BackwardTransformer PBTseitinInfo where
  transformBackward (PBTseitinInfo info) = transformBackward info

instance ObjValueTransformer PBTseitinInfo where
  type SourceObjValue PBTseitinInfo = Integer
  type TargetObjValue PBTseitinInfo = Integer

instance ObjValueForwardTransformer PBTseitinInfo where
  transformObjValueForward _ = id

instance ObjValueBackwardTransformer PBTseitinInfo where
  transformObjValueBackward _ = id

instance J.ToJSON PBTseitinInfo where
  toJSON (PBTseitinInfo info) =
    J.object
    [ "type" .= ("PBTseitinInfo" :: J.Value)
    , "base" .= info
    ]

instance J.FromJSON PBTseitinInfo where
  parseJSON = withTypedObject "PBTseitinInfo" $ \obj ->
    PBTseitinInfo <$> obj .: "base"

-- -----------------------------------------------------------------------------

type PBLinearizeInfo = PBTseitinInfo

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
    , PBTseitinInfo $ TseitinInfo (PBFile.pbNumVars formula) (PBFile.pbNumVars formula') defs
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
    , PBTseitinInfo $ TseitinInfo (PBFile.wboNumVars formula) (PBFile.pbNumVars formula') defs
    )

-- -----------------------------------------------------------------------------

type PBQuadratizeInfo = PBTseitinInfo

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
  , PBTseitinInfo $ TseitinInfo nv1 nv2 (IntMap.fromList [(v, And [atom l1, atom l2]) | (v, (l1,l2)) <- prodDefs])
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

-- -----------------------------------------------------------------------------

-- | Convert inequality constraints into equality constraints by introducing surplus variables.
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
          Nothing
            | SAT.pbLowerBound lhs > rhs -> return Nothing
            | otherwise -> do
                let (lhs', rhs') = simplifyPBAtLeast (lhs, rhs)
                    maxSurplus = max (SAT.pbUpperBound lhs' - rhs') 0
                surplus <- Integer.newVarPBLinSum db maxSurplus
                SAT.addPBNLExactly db (lhs' ++ [(-c,[l]) | (c,l) <- surplus]) rhs'
                if maxSurplus > 0 then do
                  return $ Just (lhs', rhs', surplus)
                else
                  return Nothing

  formula' <- getPBFormula db
  unless (all (\(_, op, _) -> op == PBFile.Eq) (PBFile.pbConstraints formula')) $ error "should not happen"
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

    simplifyPBAtLeast :: (SAT.PBSum, Integer) -> (SAT.PBSum, Integer)
    simplifyPBAtLeast (lhs, rhs) = 
      case splitConst lhs of
        (lhs', offset) ->
          let rhs' = rhs - offset
              d = case lhs' of
                    [] -> 1
                    _ -> abs $ foldl1' gcd (map fst lhs')
           in ([(c `div` d, ls) | (c,ls) <- lhs'], (rhs' + d - 1) `div` d)

    splitConst :: SAT.PBSum -> (SAT.PBSum, Integer)
    splitConst s = ([t | t@(c, _:_) <- s, c /= 0], sum [c | (c, []) <- s])

data PBInequalitiesToEqualitiesInfo
  = PBInequalitiesToEqualitiesInfo !Int !Int [(PBFile.Sum, Integer, SAT.PBLinSum)]
  deriving (Eq, Show)

instance Transformer PBInequalitiesToEqualitiesInfo where
  type Source PBInequalitiesToEqualitiesInfo = SAT.Model
  type Target PBInequalitiesToEqualitiesInfo = SAT.Model

instance ForwardTransformer PBInequalitiesToEqualitiesInfo where
  transformForward (PBInequalitiesToEqualitiesInfo _nv1 nv2 defs) m =
    array (1, nv2) $ assocs m ++ concat
      [ if lhsVal >= rhs then
          case SubsetSum.subsetSum (V.fromList (map fst surplus)) (lhsVal - rhs) of
            Nothing -> error ("failed to construct surplus assignment")
            Just sol -> [if l > 0 then (l, v) else (- l, not v) | (l, v) <- zip (map snd surplus) (VG.toList sol)]
        else
          [if l > 0 then (l, False) else (-l, True) | (_, l) <- surplus]
      | (lhs, rhs, surplus) <- defs
      , let lhsVal = SAT.evalPBSum m lhs
      ]

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
    , "definitions" .=
        [ J.object
          [ "lhs" .= jPBSum lhs
          , "rhs" .= rhs
          , "surplus" .= jPBLinSum surplus
          ]
        | (lhs, rhs, surplus) <- defs
        ]
    ]

instance J.FromJSON PBInequalitiesToEqualitiesInfo where
  parseJSON = withTypedObject "PBInequalitiesToEqualitiesInfo" $ \obj -> do
    PBInequalitiesToEqualitiesInfo
      <$> obj .: "num_original_variables"
      <*> obj .: "num_transformed_variables"
      <*> (mapM f =<< obj .: "definitions")
    where
      f = J.withObject "definition" $ \obj -> do
        lhs <- parsePBSum =<< obj .: "lhs"
        rhs <- obj .: "rhs"
        surplus <- parsePBLinSum =<< obj .: "surplus"
        return (lhs, rhs, surplus)

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
    sq ts = Map.unionWith (+) sq1 sq2
      where
        ts' = [ (c, ls', neg, pos)
              | (c, ls) <- ts, c /= 0
              , let ls' = IntSet.fromList ls, let (neg, pos) = IntSet.split 0 ls'
              , not (contradict neg pos)
              ]
        sq1 = Map.fromListWith (+) [(ls, c^(2::Int)) | (c, ls, _, _) <- ts']
        sq2 = Map.fromListWith (+) $ do
          ((c1, ls1, neg1, pos1), (c2, ls2, neg2, pos2)) <- pairs ts'
          guard $ not $ contradict neg1 pos2
          guard $ not $ contradict neg2 pos1
          return (ls1 `IntSet.union` ls2, 2*c1*c2)
    contradict ls1 ls2 =
      not $ IntSet.null $ IntSet.fromAscList (map negate (IntSet.toDescList ls1)) `IntSet.intersection` ls2

pairs :: [a] -> [(a, a)]
pairs [] = []
pairs (x:xs) = [(x,y) | y <- xs] ++ pairs xs

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
  when (offset /= 0) $ modifyMutVar objRef ((offset,[]) :)

  obj <- liftM reverse $ readMutVar objRef
  defs <- liftM IntMap.fromList $ readMutVar defsRef

  case PBFile.wboTopCost wbo of
    Just t | t <= sum [w | (Just w, _) <- PBFile.wboConstraints wbo] -> SAT.addPBNLAtMost db obj (t - 1)
    _ -> return ()

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

type MaxSAT2WBOInfo = PBIdentityInfo

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
  , PBIdentityInfo
  )
  where
    f (w,c)
     | w>=top    = (Nothing, p) -- hard constraint
     | otherwise = (Just w, p)  -- soft constraint
     where
       p = ([(1,[l]) | l <- SAT.unpackClause c], PBFile.Ge, 1)

type WBO2MaxSATInfo = PBTseitinInfo

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
  return (wcnf, PBTseitinInfo (TseitinInfo (PBFile.wboNumVars formula) (CNF.cnfNumVars cnf) defs))

-- -----------------------------------------------------------------------------

pb2lsp :: PBFile.Formula -> Builder
pb2lsp formula =
  byteString "function model() {\n" <>
  decls <>
  constrs <>
  obj2 <>
  "}\n"
  where
    nv = PBFile.pbNumVars formula

    decls = byteString "  for [i in 1.." <> intDec nv <> byteString "] x[i] <- bool();\n"

    constrs = mconcat
      [ byteString "  constraint " <>
        showConstrLSP c <>
        ";\n"
      | c <- PBFile.pbConstraints formula
      ]

    obj2 =
      case PBFile.pbObjectiveFunction formula of
        Just obj' -> byteString "  minimize " <> showSumLSP obj' <> ";\n"
        Nothing -> mempty

wbo2lsp :: PBFile.SoftFormula -> Builder
wbo2lsp softFormula =
  byteString "function model() {\n" <>
  decls <>
  constrs <>
  costDef <>
  topConstr <>
  byteString "  minimize cost;\n}\n"
  where
    nv = PBFile.wboNumVars softFormula

    decls = byteString "  for [i in 1.." <> intDec nv <> byteString "] x[i] <- bool();\n"

    constrs = mconcat
      [ byteString "  constraint " <>
        showConstrLSP c <>
        ";\n"
      | (Nothing, c) <- PBFile.wboConstraints softFormula
      ]

    costDef = byteString "  cost <- sum(\n" <> s <> ");\n"
      where
        s = mconcat . intersperse (",\n") $ xs
        xs = ["    " <> integerDec w <> "*!(" <> showConstrLSP c <> ")"
             | (Just w, c) <- PBFile.wboConstraints softFormula]

    topConstr =
      case PBFile.wboTopCost softFormula of
        Nothing -> mempty
        Just t -> byteString "  constraint cost <= " <> integerDec t <> ";\n"

showConstrLSP :: PBFile.Constraint -> Builder
showConstrLSP (lhs, PBFile.Ge, 1) | and [c==1 | (c,_) <- lhs] =
  "or(" <> mconcat (intersperse "," (map (f . snd) lhs)) <> ")"
  where
    f [l] = showLitLSP l
    f ls  = "and(" <> mconcat (intersperse "," (map showLitLSP ls)) <> ")"
showConstrLSP (lhs, op, rhs) = showSumLSP lhs  <> op2 <> integerDec rhs
  where
    op2 = case op of
            PBFile.Ge -> " >= "
            PBFile.Eq -> " == "

sum' :: [Builder] -> Builder
sum' xs = "sum(" <> mconcat (intersperse ", " xs) <> ")"

showSumLSP :: PBFile.Sum -> Builder
showSumLSP = sum' . map showTermLSP

showTermLSP :: PBFile.WeightedTerm -> Builder
showTermLSP (n,ls) = mconcat $ intersperse "*" $ [integerDec n | n /= 1] ++ [showLitLSP l | l<-ls]

showLitLSP :: PBFile.Lit -> Builder
showLitLSP l =
  if l < 0
  then "!x[" <> intDec (abs l) <> "]"
  else "x[" <> intDec l <> "]"

-- -----------------------------------------------------------------------------

pb2smp :: Bool -> PBFile.Formula -> Builder
pb2smp isUnix formula =
  header <>
  decls <>
  char7 '\n' <>
  obj2 <>
  char7 '\n' <>
  constrs <>
  char7 '\n' <>
  actions <>
  footer
  where
    nv = PBFile.pbNumVars formula

    header =
      if isUnix
      then byteString "#include \"simple.h\"\nvoid ufun()\n{\n\n"
      else mempty

    footer =
      if isUnix
      then "\n}\n"
      else mempty

    actions = byteString $
      "solve();\n" <>
      "x[i].val.print();\n" <>
      "cost.val.print();\n"

    decls =
      byteString "Element i(set=\"1 .. " <> intDec nv <>
      byteString "\");\nIntegerVariable x(type=binary, index=i);\n"

    constrs = mconcat
      [ showSum lhs <>
        op2 <>
        integerDec rhs <>
        ";\n"
      | (lhs, op, rhs) <- PBFile.pbConstraints formula
      , let op2 = case op of
                    PBFile.Ge -> " >= "
                    PBFile.Eq -> " == "
      ]

    showSum :: PBFile.Sum -> Builder
    showSum [] = char7 '0'
    showSum xs = mconcat $ intersperse " + " $ map showTerm xs

    showTerm (n,ls) = mconcat $ intersperse (char7 '*') $ showCoeff n ++ [showLit l | l<-ls]

    showCoeff n
      | n == 1    = []
      | n < 0     = [char7 '(' <> integerDec n <> char7 ')']
      | otherwise = [integerDec n]

    showLit l =
      if l < 0
      then "(1-x[" <> intDec (abs l) <> "])"
      else "x[" <> intDec l <> "]"

    obj2 =
      case PBFile.pbObjectiveFunction formula of
        Just obj' ->
          byteString "Objective cost(type=minimize);\ncost = " <> showSum obj' <> ";\n"
        Nothing -> mempty

-- -----------------------------------------------------------------------------
