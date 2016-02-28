{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE MultiParamTypeClasses #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.Converter.MIP2PB
-- Copyright   :  (c) Masahiro Sakai 2016
-- License     :  BSD-style
--
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  experimental
-- Portability :  non-portable (MultiParamTypeClasses)
--
-----------------------------------------------------------------------------
module ToySolver.Converter.MIP2PB
  ( convert
  , addMIP
  ) where

import Control.Monad
import Control.Monad.ST
import Control.Monad.Trans
import Control.Monad.Trans.Except
import Data.List (intercalate, foldl', sortBy)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Foldable (toList)
import Data.Ord
import Data.Ratio
import Data.Sequence (Seq, (|>))
import qualified Data.Sequence as Seq
import qualified Data.Set as Set
import Data.STRef
import Data.VectorSpace

import qualified Data.PseudoBoolean as PBFile
import qualified ToySolver.Data.MIP as MIP
import ToySolver.Data.OrdRel
import qualified ToySolver.SAT.Types as SAT
import qualified ToySolver.SAT.Integer as Integer
import ToySolver.Internal.Util (revForM)

-- -----------------------------------------------------------------------------

convert :: MIP.Problem -> Either String (PBFile.Formula, Integer -> Rational, SAT.Model -> Map MIP.Var Integer)
convert mip = runST $ runExceptT $ m
  where
    m :: ExceptT String (ST s) (PBFile.Formula, Integer -> Rational, SAT.Model -> Map MIP.Var Integer)
    m = do
      db <- lift $ newPBStore
      (Integer.Expr obj, otrans, mtrans) <- addMIP' db mip
      formula <- lift $ getPBFormula db
      return $ (formula{ PBFile.pbObjectiveFunction = Just obj }, otrans, mtrans)

-- -----------------------------------------------------------------------------

addMIP :: SAT.AddPBNL m enc => enc -> MIP.Problem -> m (Either String (Integer.Expr, Integer -> Rational, SAT.Model -> Map MIP.Var Integer))
addMIP enc mip = runExceptT $ addMIP' enc mip

addMIP' :: SAT.AddPBNL m enc => enc -> MIP.Problem -> ExceptT String m (Integer.Expr, Integer -> Rational, SAT.Model -> Map MIP.Var Integer)
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

    let transformObjVal :: Integer -> Rational
        transformObjVal val = fromIntegral val / fromIntegral d

        transformModel :: SAT.Model -> Map MIP.Var Integer
        transformModel m = Map.fromList
          [ (v, Integer.eval m (vmap Map.! v)) | v <- Set.toList ivs ]

    return (obj2, transformObjVal, transformModel)
  where
    ivs = MIP.integerVariables mip
    nivs = MIP.variables mip `Set.difference` ivs

    asInteger :: Rational -> Integer
    asInteger r
      | denominator r /= 1 = error (show r ++ " is not integer")
      | otherwise = numerator r

    nonAdjacentPairs :: [a] -> [(a,a)]
    nonAdjacentPairs (x1:x2:xs) = [(x1,x3) | x3 <- xs] ++ nonAdjacentPairs (x2:xs)
    nonAdjacentPairs _ = []

    asBin :: Integer.Expr -> SAT.Lit
    asBin (Integer.Expr [(1,[lit])]) = lit
    asBin _ = error "asBin: failure"

-- -----------------------------------------------------------------------------

data PBStore s = PBStore (STRef s Int) (STRef s (Seq PBFile.Constraint))

instance SAT.NewVar (ST s) (PBStore s) where
  newVar (PBStore ref _) = do
    modifySTRef' ref (+1)
    readSTRef ref

instance SAT.AddClause (ST s) (PBStore s) where
  addClause enc clause = SAT.addPBNLAtLeast enc [(1,[l]) | l <- clause] 1

instance SAT.AddCardinality (ST s) (PBStore s) where
  addAtLeast enc lhs rhs = SAT.addPBNLAtLeast enc [(1,[l]) | l <- lhs] (fromIntegral rhs)

instance SAT.AddPBLin (ST s) (PBStore s) where
  addPBAtLeast enc lhs rhs = SAT.addPBNLAtLeast enc [(c,[l]) | (c,l) <- lhs] rhs
  addPBAtMost enc lhs rhs  = SAT.addPBNLAtMost enc  [(c,[l]) | (c,l) <- lhs] rhs
  addPBExactly enc lhs rhs = SAT.addPBNLExactly enc [(c,[l]) | (c,l) <- lhs] rhs

instance SAT.AddPBNL (ST s) (PBStore s) where
  addPBNLAtLeast (PBStore _ ref) lhs rhs = do
    modifySTRef ref (|> (lhs, PBFile.Ge, rhs))
  addPBNLExactly (PBStore _ ref) lhs rhs = do
    modifySTRef ref (|> (lhs, PBFile.Eq, rhs))

newPBStore :: ST s (PBStore s)
newPBStore = do
  ref1 <- newSTRef 0
  ref2 <- newSTRef Seq.empty
  return (PBStore ref1 ref2)

getPBFormula :: PBStore s -> ST s (PBFile.Formula)
getPBFormula (PBStore ref1 ref2) = do
  nv <- readSTRef ref1
  cs <- readSTRef ref2
  return $
    PBFile.Formula
    { PBFile.pbObjectiveFunction = Nothing
    , PBFile.pbConstraints = toList cs
    , PBFile.pbNumVars = nv
    , PBFile.pbNumConstraints = Seq.length cs
    }

-- -----------------------------------------------------------------------------
