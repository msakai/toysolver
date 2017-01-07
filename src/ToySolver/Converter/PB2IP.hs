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

import qualified Data.PseudoBoolean as PBFile
import qualified ToySolver.Data.MIP as MIP
import ToySolver.Data.MIP ((.==.), (.<=.), (.>=.))
import qualified ToySolver.SAT.Types as SAT

convert :: PBFile.Formula -> (MIP.Problem Integer, SAT.Model -> Map MIP.Var Rational, Map MIP.Var Rational -> SAT.Model)
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
          rhs2 = rhs - c
      return $ case op of
        PBFile.Ge -> def{ MIP.constrExpr = lhs2, MIP.constrLB = MIP.Finite rhs2 }
        PBFile.Eq -> def{ MIP.constrExpr = lhs2, MIP.constrLB = MIP.Finite rhs2, MIP.constrUB = MIP.Finite rhs2 }

    mforth :: SAT.Model -> Map MIP.Var Rational
    mforth m = Map.fromList [(convVar v, if val then 1 else 0) | (v,val) <- assocs m]

convExpr :: PBFile.Sum -> MIP.Expr Integer
convExpr s = sum [product (fromIntegral w : map f tm) | (w,tm) <- s]
  where
    f :: PBFile.Lit -> MIP.Expr Integer
    f x
      | x > 0     = MIP.varExpr (convVar x)
      | otherwise = 1 - MIP.varExpr (convVar (abs x))

convVar :: PBFile.Var -> MIP.Var
convVar x = MIP.toVar ("x" ++ show x)

convertWBO :: Bool -> PBFile.SoftFormula -> (MIP.Problem Integer, SAT.Model -> Map MIP.Var Rational, Map MIP.Var Rational -> SAT.Model)
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
      , MIP.objExpr = MIP.Expr [MIP.Term w [v] | (ts, _) <- cs2, (w, v) <- ts]
      }

    topConstr :: [MIP.Constraint Integer]
    topConstr = 
     case PBFile.wboTopCost formula of
       Nothing -> []
       Just t ->
          [ def{ MIP.constrExpr = MIP.objExpr obj2, MIP.constrUB = MIP.Finite (fromInteger t - 1) } ]

    relaxVariables :: [(MIP.Var, PBFile.SoftConstraint)]
    relaxVariables = [(MIP.toVar ("r" ++ show n), c) | (n, c) <- zip [(0::Int)..] (PBFile.wboConstraints formula)]

    cs2 :: [([(Integer, MIP.Var)], MIP.Constraint Integer)]
    cs2 = do
      (v, (w, (lhs,op,rhs))) <- relaxVariables
      let (lhs2,c) = splitConst $ convExpr lhs
          rhs2 = rhs - c
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

    mforth :: SAT.Model -> Map MIP.Var Rational
    mforth m = Map.union m1 m2
      where
        m1 = Map.fromList $ [(convVar v, if val then 1 else 0) | (v,val) <- assocs m]
        m2 = Map.fromList $ [(v, if SAT.evalPBConstraint m c then 0 else 1) | (v, (Just _, c)) <- relaxVariables]

splitConst :: MIP.Expr Integer -> (MIP.Expr Integer, Integer)
splitConst e = (e2, c)
  where
    e2 = MIP.Expr [t | t@(MIP.Term _ (_:_)) <- MIP.terms e]
    c = sum [c | MIP.Term c [] <- MIP.terms e]
             
relaxGE :: MIP.Var -> (MIP.Expr Integer, Integer) -> (MIP.Expr Integer, Integer)
relaxGE v (lhs, rhs) = (MIP.constExpr (rhs - lhs_lb) * MIP.varExpr v + lhs, rhs)
  where
    lhs_lb = sum [min c 0 | MIP.Term c _ <- MIP.terms lhs]

relaxLE :: MIP.Var -> (MIP.Expr Integer, Integer) -> (MIP.Expr Integer, Integer)
relaxLE v (lhs, rhs) = (MIP.constExpr (rhs - lhs_ub) * MIP.varExpr v + lhs, rhs)
  where
    lhs_ub = sum [max c 0 | MIP.Term c _ <- MIP.terms lhs]

mtrans :: Int -> Map MIP.Var Rational -> SAT.Model
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
