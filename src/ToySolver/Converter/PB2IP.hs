{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wall #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.Converter.PB2IP
-- Copyright   :  (c) Masahiro Sakai 2011-2015
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  experimental
-- Portability :  portable
--
-----------------------------------------------------------------------------
module ToySolver.Converter.PB2IP
  ( convert
  , convertWBO
  ) where

import Data.Array.IArray
import Data.Default.Class
import Data.Maybe
import Data.Map (Map)
import qualified Data.Map as Map
import Data.String

import qualified Data.PseudoBoolean as PBFile
import qualified ToySolver.Data.MIP as MIP
import ToySolver.Data.MIP ((.==.), (.<=.), (.>=.))
import qualified ToySolver.SAT.Types as SAT

convert :: forall v. MIP.IsVar v => PBFile.Formula -> (MIP.Problem v Rational, SAT.Model -> Map v Rational, Map v Rational -> SAT.Model)
convert formula = (mip, mforth, mtrans (PBFile.pbNumVars formula))
  where
    mip = def
      { MIP.objectiveFunction = obj2
      , MIP.constraints = cs2
      , MIP.varType = Map.fromList [(v, MIP.IntegerVariable) | v <- vs]
      , MIP.varBounds = Map.fromList [(v, (0,1)) | v <- vs]
      }

    vs = [convVar v | v <- [1..PBFile.pbNumVars formula]]

    obj2 =
      case PBFile.pbObjectiveFunction formula of
        Just obj' -> def{ MIP.objDir = MIP.OptMin, MIP.objExpr = convExpr obj' }
        Nothing   -> def{ MIP.objDir = MIP.OptMin, MIP.objExpr = 0 }

    cs2 = do
      (lhs,op,rhs) <- PBFile.pbConstraints formula
      let (lhs2,c) = splitConst $ convExpr lhs
          rhs2 = fromIntegral rhs - c
      return $ case op of
        PBFile.Ge -> def{ MIP.constrExpr = lhs2, MIP.constrLB = MIP.Finite rhs2 }
        PBFile.Eq -> def{ MIP.constrExpr = lhs2, MIP.constrLB = MIP.Finite rhs2, MIP.constrUB = MIP.Finite rhs2 }

    mforth :: SAT.Model -> Map v Rational
    mforth m = Map.fromList [(convVar v, if val then 1 else 0) | (v,val) <- assocs m]

convExpr :: forall v. MIP.IsVar v => PBFile.Sum -> MIP.Expr v Rational
convExpr s = sum [product (fromIntegral w : map f tm) | (w,tm) <- s]
  where
    f :: PBFile.Lit -> MIP.Expr v Rational
    f x
      | x > 0     = MIP.varExpr (convVar x)
      | otherwise = 1 - MIP.varExpr (convVar (abs x))

convVar :: MIP.IsVar v => PBFile.Var -> v
convVar x = fromString ("x" ++ show x)

convertWBO :: forall v. MIP.IsVar v => Bool -> PBFile.SoftFormula -> (MIP.Problem v Rational, SAT.Model -> Map v Rational, Map v Rational -> SAT.Model)
convertWBO useIndicator formula = (mip, mforth, mtrans (PBFile.wboNumVars formula))
  where
    mip = def
      { MIP.objectiveFunction = obj2
      , MIP.constraints = topConstr ++ map snd cs2
      , MIP.varType = Map.fromList [(v, MIP.IntegerVariable) | v <- vs]
      , MIP.varBounds = Map.fromList [(v, (0,1)) | v <- vs]
      }

    vs = [convVar v | v <- [1..PBFile.wboNumVars formula]] ++ [v | (ts, _) <- cs2, (_, v) <- ts]

    obj2 = def
      { MIP.objDir = MIP.OptMin
      , MIP.objExpr = MIP.Expr [MIP.Term (fromIntegral w) [v] | (ts, _) <- cs2, (w, v) <- ts]
      }

    topConstr :: [MIP.Constraint v Rational]
    topConstr = 
     case PBFile.wboTopCost formula of
       Nothing -> []
       Just t ->
          [ def{ MIP.constrExpr = MIP.objExpr obj2, MIP.constrUB = MIP.Finite (fromInteger t - 1) } ]

    relaxVariables :: [(v, PBFile.SoftConstraint)]
    relaxVariables = [(fromString ("r" ++ show n), c) | (n, c) <- zip [(0::Int)..] (PBFile.wboConstraints formula)]

    cs2 :: [([(Integer, v)], MIP.Constraint v Rational)]
    cs2 = do
      (v, (w, (lhs,op,rhs))) <- relaxVariables
      let (lhs2,c) = splitConst $ convExpr lhs
          rhs2 = fromIntegral rhs - c
          (ts,ind) =
            case w of
              Nothing -> ([], Nothing)
              Just w2 -> ([(w2,v)], Just (v,0))
      if isNothing w || useIndicator then do
         let c =
               case op of
                 PBFile.Ge -> (lhs2 .>=. MIP.constExpr rhs2) { MIP.constrIndicator = ind }
                 PBFile.Eq -> (lhs2 .==. MIP.constExpr rhs2) { MIP.constrIndicator = ind }
         return (ts, c)
      else do
         let (lhsGE,rhsGE) = relaxGE v (lhs2,rhs2)
             c1 = lhsGE .>=. MIP.constExpr rhsGE
         case op of
           PBFile.Ge -> do
             return (ts, c1)
           PBFile.Eq -> do
             let (lhsLE,rhsLE) = relaxLE v (lhs2,rhs2)
                 c2 = lhsLE .<=. MIP.constExpr rhsLE
             [ (ts, c1), ([], c2) ]

    mforth :: SAT.Model -> Map v Rational
    mforth m = Map.union m1 m2
      where
        m1 = Map.fromList $ [(convVar v, if val then 1 else 0) | (v,val) <- assocs m]
        m2 = Map.fromList $ [(v, if SAT.evalPBConstraint m c then 0 else 1) | (v, (Just _, c)) <- relaxVariables]

splitConst :: MIP.Expr v Rational -> (MIP.Expr v Rational, Rational)
splitConst e = (e2, c)
  where
    e2 = MIP.Expr [t | t@(MIP.Term _ (_:_)) <- MIP.terms e]
    c = sum [c | MIP.Term c [] <- MIP.terms e]

relaxGE :: MIP.IsVar v => v -> (MIP.Expr v Rational, Rational) -> (MIP.Expr v Rational, Rational)             
relaxGE v (lhs, rhs) = (MIP.constExpr (rhs - lhs_lb) * MIP.varExpr v + lhs, rhs)
  where
    lhs_lb = sum [min c 0 | MIP.Term c _ <- MIP.terms lhs]

relaxLE :: MIP.IsVar v => v -> (MIP.Expr v Rational, Rational) -> (MIP.Expr v Rational, Rational)
relaxLE v (lhs, rhs) = (MIP.constExpr (rhs - lhs_ub) * MIP.varExpr v + lhs, rhs)
  where
    lhs_ub = sum [max c 0 | MIP.Term c _ <- MIP.terms lhs]

mtrans :: MIP.IsVar v => Int -> Map v Rational -> SAT.Model
mtrans nvar m =
  array (1, nvar)
    [ (i, val)
    | i <- [1 .. nvar]
    , let val =
            case Map.findWithDefault 0 (convVar i) m of
              0  -> False
              1  -> True
              v0 -> error (show v0 ++ " is neither 0 nor 1")
    ]
