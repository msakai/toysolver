{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_HADDOCK show-extensions #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.Converter.MIP2PB
-- Copyright   :  (c) Masahiro Sakai 2016
-- License     :  BSD-style
--
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  experimental
-- Portability :  non-portable
--
-----------------------------------------------------------------------------
module ToySolver.Converter.MIP2PB
  ( mip2pb
  , MIP2PBInfo (..)
  , addMIP
  ) where

import Control.Monad
import Control.Monad.Primitive
import Control.Monad.ST
import Control.Monad.Trans
import Control.Monad.Trans.Except
import qualified Data.Aeson as J
import Data.Aeson ((.=), (.:))
import Data.Array.IArray
import qualified Data.IntSet as IntSet
import Data.List (intercalate, foldl', sortBy)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Ord
import Data.Primitive.MutVar
import Data.Ratio
import qualified Data.Set as Set
import Data.String
import Data.VectorSpace

import qualified Data.PseudoBoolean as PBFile
import qualified Numeric.Optimization.MIP as MIP

import ToySolver.Converter.Base
import ToySolver.Data.OrdRel
import ToySolver.Internal.JSON
import qualified ToySolver.SAT.Types as SAT
import qualified ToySolver.SAT.Encoder.Integer as Integer
import ToySolver.SAT.Internal.JSON
import ToySolver.SAT.Store.PB
import ToySolver.Internal.Util (revForM)

-- -----------------------------------------------------------------------------

mip2pb :: MIP.Problem Rational -> Either String (PBFile.Formula, MIP2PBInfo)
mip2pb mip = runST $ runExceptT $ m
  where
    m :: ExceptT String (ST s) (PBFile.Formula, MIP2PBInfo)
    m = do
      db <- lift $ newPBStore
      (Integer.Expr obj, info) <- addMIP' db mip
      formula <- lift $ getPBFormula db
      return $ (formula{ PBFile.pbObjectiveFunction = Just obj }, info)

data MIP2PBInfo = MIP2PBInfo (Map MIP.Var Integer.Expr) (Map MIP.Var SAT.Lit) !Integer
  deriving (Eq, Show)

instance Transformer MIP2PBInfo where
  type Source MIP2PBInfo = Map MIP.Var Rational
  type Target MIP2PBInfo = SAT.Model

instance ForwardTransformer MIP2PBInfo where
  transformForward (MIP2PBInfo vmap nonZeroTable _d) sol
    | Map.keysSet vmap /= Map.keysSet sol = error "variables mismatch"
    | otherwise = array (1, x_max) $
        [(x, val) | (var, Integer.Expr s) <- Map.toList vmap, (x, val) <- f s (sol Map.! var)] ++
        [(y, (sol Map.! var) /= 0) | (var, y) <- Map.toList nonZeroTable]
    where
      x_max :: SAT.Var
      x_max = IntSet.findMax xs
        where
          xs = IntSet.unions $
               [IntSet.fromList (map SAT.litVar lits) | Integer.Expr s <- Map.elems vmap, (_, lits) <- s] ++
               [IntSet.fromList (map SAT.litVar (Map.elems nonZeroTable))] ++
               [IntSet.singleton 0]

      f :: SAT.PBSum -> Rational -> [(SAT.Var, Bool)]
      f s val
        | denominator val /= 1 = error "value should be integer"
        | otherwise = g (numerator val - sum [c | (c, []) <- s]) (Map.toDescList tmp)
        where
          tmp :: Map Integer SAT.Var
          tmp =
            Map.fromList
            [ if c < 0 then
                error "coefficient should be non-negative"
              else if length ls > 1 then
                error "variable definition should be linear"
              else
                (c, head ls)
            | (c, ls) <- s, not (null ls), c /= 0
            ]

          g :: Integer -> [(Integer, SAT.Var)] -> [(SAT.Var, Bool)]
          g 0 [] = []
          g _ [] = error "no more variables"
          g v ((c,l) : ys)
            | v >= c    = (l, True)  : g (v - c) ys
            | otherwise = (l, False) : g v ys

instance BackwardTransformer MIP2PBInfo where
  transformBackward (MIP2PBInfo vmap _nonZeroTable _d) m = fmap (toRational . Integer.eval m) vmap

instance ObjValueTransformer MIP2PBInfo where
  type SourceObjValue MIP2PBInfo = Rational
  type TargetObjValue MIP2PBInfo = Integer

instance ObjValueForwardTransformer MIP2PBInfo where
  transformObjValueForward (MIP2PBInfo _vmap _nonZeroTable d) val = asInteger (val * fromIntegral d)

instance ObjValueBackwardTransformer MIP2PBInfo where
  transformObjValueBackward (MIP2PBInfo _vmap _nonZeroTable d) val = fromIntegral val / fromIntegral d

instance J.ToJSON MIP2PBInfo where
  toJSON (MIP2PBInfo vmap nonZeroTable d) =
    J.object
    [ "type" .= ("MIP2PBInfo" :: J.Value)
    , "substitutions" .= J.object
        [ fromString (MIP.fromVar v) .= jPBSum s
        | (v, Integer.Expr s) <- Map.toList vmap
        ]
    , "nonzero_indicators" .= J.object
        [ fromString (MIP.fromVar v) .= (jLitName lit :: J.Value)
        | (v, lit) <- Map.toList nonZeroTable
        ]
    , "objective_function_scale_factor" .= d
    ]

instance J.FromJSON MIP2PBInfo where
  parseJSON = withTypedObject "MIP2PBInfo" $ \obj -> do
    tmp1 <- obj .: "substitutions"
    subst <- liftM Map.fromList $ forM (Map.toList tmp1) $ \(name, expr) -> do
      s <- parsePBSum expr
      return (MIP.toVar name, Integer.Expr s)
    tmp2 <- obj .: "nonzero_indicators"
    nonZeroTable <- liftM Map.fromList $ forM (Map.toList tmp2) $ \(name, s) -> do
      lit <- parseLitName s
      return (MIP.toVar name, lit)
    d <- obj .: "objective_function_scale_factor"
    pure $ MIP2PBInfo subst nonZeroTable d

-- -----------------------------------------------------------------------------

addMIP :: (SAT.AddPBNL m enc, PrimMonad m) => enc -> MIP.Problem Rational -> m (Either String (Integer.Expr, MIP2PBInfo))
addMIP enc mip = runExceptT $ addMIP' enc mip

addMIP' :: forall m enc. (SAT.AddPBNL m enc, PrimMonad m) => enc -> MIP.Problem Rational -> ExceptT String m (Integer.Expr, MIP2PBInfo)
addMIP' enc mip = do
  if not (Set.null nivs) then do
    throwE $ "cannot handle non-integer variables: " ++ intercalate ", " (map MIP.fromVar (Set.toList nivs))
  else do
    vmap <- liftM Map.fromList $ revForM (Set.toList ivs) $ \v -> do
      case MIP.getBounds mip v of
        (MIP.Finite lb, MIP.Finite ub) -> do
          v2 <- lift $ Integer.newVar enc (ceiling lb) (floor ub)
          return (v,v2)
        _ -> do
          throwE $ "cannot handle unbounded variable: " ++ MIP.fromVar v
    forM_ (MIP.constraints mip) $ \c -> do
      let lhs = MIP.constrExpr c
      let f op rhs = do
            let d = foldl' lcm 1 (map denominator  (rhs:[r | MIP.Term r _ <- MIP.terms lhs]))
                lhs' = sumV [asInteger (r * fromIntegral d) *^ product [vmap Map.! v | v <- vs] | MIP.Term r vs <- MIP.terms lhs]
                rhs' = asInteger (rhs * fromIntegral d)
                c2 = case op of
                       MIP.Le  -> lhs' .<=. fromInteger rhs'
                       MIP.Ge  -> lhs' .>=. fromInteger rhs'
                       MIP.Eql -> lhs' .==. fromInteger rhs'
            case MIP.constrIndicator c of
              Nothing -> lift $ Integer.addConstraint enc c2
              Just (var, val) -> do
                let var' = asBin (vmap Map.! var)
                case val of
                  1 -> lift $ Integer.addConstraintSoft enc var' c2
                  0 -> lift $ Integer.addConstraintSoft enc (SAT.litNot var') c2
                  _ -> return ()
          g = do
            case MIP.constrIndicator c of
              Nothing -> lift $ SAT.addClause enc []
              Just (var, val) -> do
                let var' = asBin (vmap Map.! var)
                case val of
                  1 -> lift $ SAT.addClause enc [- var']
                  0 -> lift $ SAT.addClause enc [var']
                  _ -> return ()
      case (MIP.constrLB c, MIP.constrUB c) of
        (MIP.Finite x1, MIP.Finite x2) | x1==x2 -> f MIP.Eql x2
        (lb, ub) -> do
          case lb of
            MIP.NegInf -> return ()
            MIP.Finite x -> f MIP.Ge x
            MIP.PosInf -> g
          case ub of
            MIP.NegInf -> g
            MIP.Finite x -> f MIP.Le x
            MIP.PosInf -> return ()

    nonZeroTableRef <- lift $ newMutVar Map.empty
    let isNonZero :: MIP.Var -> ExceptT String m SAT.Lit
        isNonZero v = do
          tbl <- lift $ readMutVar nonZeroTableRef
          case Map.lookup v tbl of
            Just lit -> pure lit
            Nothing -> do
              let (MIP.Finite lb, MIP.Finite ub) = MIP.getBounds mip v
                  e@(Integer.Expr s) = vmap Map.! v
              lit <-
                if lb == 0 && ub == 1 then do
                  return (asBin e)
                else do
                  v <- lift $ SAT.newVar enc
                  -- F(v) → F(s ≠ 0)
                  -- ⇐ s≠0 → v
                  -- ⇔ ¬v → s=0
                  lift $ SAT.addPBNLExactlySoft enc (- v) s 0
                  return v
              lift $ writeMutVar nonZeroTableRef (Map.insert v lit tbl)
              pure lit

    forM_ (MIP.sosConstraints mip) $ \MIP.SOSConstraint{ MIP.sosType = typ, MIP.sosBody = xs } -> do
      case typ of
        MIP.S1 -> do
          ys <- mapM (isNonZero . fst) xs
          lift $ SAT.addAtMost enc ys 1
        MIP.S2 -> do
          ys <- mapM (isNonZero . fst) $ sortBy (comparing snd) xs
          lift $ SAT.addSOS2 enc ys

    let obj = MIP.objectiveFunction mip
        d = foldl' lcm 1 [denominator r | MIP.Term r _ <- MIP.terms (MIP.objExpr obj)] *
            (if MIP.objDir obj == MIP.OptMin then 1 else -1)
        obj2 = sumV [asInteger (r * fromIntegral d) *^ product [vmap Map.! v | v <- vs] | MIP.Term r vs <- MIP.terms (MIP.objExpr obj)]

    nonZeroTable <- readMutVar nonZeroTableRef

    return (obj2, MIP2PBInfo vmap nonZeroTable d)

  where
    ivs = MIP.integerVariables mip
    nivs = MIP.variables mip `Set.difference` ivs

    asBin :: Integer.Expr -> SAT.Lit
    asBin (Integer.Expr [(1,[lit])]) = lit
    asBin _ = error "asBin: failure"

-- -----------------------------------------------------------------------------

asInteger :: Rational -> Integer
asInteger r
  | denominator r /= 1 = error (show r ++ " is not integer")
  | otherwise = numerator r

-- -----------------------------------------------------------------------------
