{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_HADDOCK show-extensions #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
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
import Control.Monad.ST
import Control.Monad.Trans
import Control.Monad.Trans.Except
import qualified Data.Aeson as J
import Data.Aeson ((.=))
import Data.List (intercalate, foldl', sortBy)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Ord
import Data.Ratio
import qualified Data.Set as Set
import Data.String
import Data.VectorSpace

import qualified Data.PseudoBoolean as PBFile
import qualified Numeric.Optimization.MIP as MIP

import ToySolver.Converter.Base
import ToySolver.Data.OrdRel
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

data MIP2PBInfo = MIP2PBInfo (Map MIP.Var Integer.Expr) !Integer
  deriving (Eq, Show)

instance Transformer MIP2PBInfo where
  type Source MIP2PBInfo = Map MIP.Var Rational
  type Target MIP2PBInfo = SAT.Model

instance BackwardTransformer MIP2PBInfo where
  transformBackward (MIP2PBInfo vmap _d) m = fmap (toRational . Integer.eval m) vmap

instance ObjValueTransformer MIP2PBInfo where
  type SourceObjValue MIP2PBInfo = Rational
  type TargetObjValue MIP2PBInfo = Integer

instance ObjValueForwardTransformer MIP2PBInfo where
  transformObjValueForward (MIP2PBInfo _vmap d) val = asInteger (val * fromIntegral d)

instance ObjValueBackwardTransformer MIP2PBInfo where
  transformObjValueBackward (MIP2PBInfo _vmap d) val = fromIntegral val / fromIntegral d

instance J.ToJSON MIP2PBInfo where
  toJSON (MIP2PBInfo vmap d) =
    J.object
    [ "type" .= J.String "MIP2PBInfo"
    , "substitutions" .= J.object
        [ fromString (MIP.fromVar v) .= jPBSum s
        | (v, Integer.Expr s) <- Map.toList vmap
        ]
    , "objective_function_scale_factor" .= d
    ]

-- -----------------------------------------------------------------------------

addMIP :: SAT.AddPBNL m enc => enc -> MIP.Problem Rational -> m (Either String (Integer.Expr, MIP2PBInfo))
addMIP enc mip = runExceptT $ addMIP' enc mip

addMIP' :: SAT.AddPBNL m enc => enc -> MIP.Problem Rational -> ExceptT String m (Integer.Expr, MIP2PBInfo)
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
      case (MIP.constrLB c, MIP.constrUB c) of
        (MIP.Finite x1, MIP.Finite x2) | x1==x2 -> f MIP.Eql x2
        (lb, ub) -> do
          case lb of
            MIP.NegInf -> return ()
            MIP.Finite x -> f MIP.Ge x
            MIP.PosInf -> lift $ SAT.addClause enc []
          case ub of
            MIP.NegInf -> lift $ SAT.addClause enc []
            MIP.Finite x -> f MIP.Le x
            MIP.PosInf -> return ()

    forM_ (MIP.sosConstraints mip) $ \MIP.SOSConstraint{ MIP.sosType = typ, MIP.sosBody = xs } -> do
      case typ of
        MIP.S1 -> lift $ SAT.addAtMost enc (map (asBin . (vmap Map.!) . fst) xs) 1
        MIP.S2 -> do
          let ps = nonAdjacentPairs $ map fst $ sortBy (comparing snd) $ xs
          forM_ ps $ \(x1,x2) -> do
            lift $ SAT.addClause enc [SAT.litNot $ asBin $ vmap Map.! v | v <- [x1,x2]]

    let obj = MIP.objectiveFunction mip
        d = foldl' lcm 1 [denominator r | MIP.Term r _ <- MIP.terms (MIP.objExpr obj)] *
            (if MIP.objDir obj == MIP.OptMin then 1 else -1)
        obj2 = sumV [asInteger (r * fromIntegral d) *^ product [vmap Map.! v | v <- vs] | MIP.Term r vs <- MIP.terms (MIP.objExpr obj)]

    return (obj2, MIP2PBInfo vmap d)

  where
    ivs = MIP.integerVariables mip
    nivs = MIP.variables mip `Set.difference` ivs

    nonAdjacentPairs :: [a] -> [(a,a)]
    nonAdjacentPairs (x1:x2:xs) = [(x1,x3) | x3 <- xs] ++ nonAdjacentPairs (x2:xs)
    nonAdjacentPairs _ = []

    asBin :: Integer.Expr -> SAT.Lit
    asBin (Integer.Expr [(1,[lit])]) = lit
    asBin _ = error "asBin: failure"

-- -----------------------------------------------------------------------------

asInteger :: Rational -> Integer
asInteger r
  | denominator r /= 1 = error (show r ++ " is not integer")
  | otherwise = numerator r

-- -----------------------------------------------------------------------------
