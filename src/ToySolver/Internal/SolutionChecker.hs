{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.Internal.SolutionChecker
-- Copyright   :  (c) Masahiro Sakai 2025
-- License     :  BSD-style
--
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  unstable
-- Portability :  non-portable
--
-----------------------------------------------------------------------------

module ToySolver.Internal.SolutionChecker
  ( checkSATResult
  , checkMaxSATResult
  , checkPBResult
  , checkWBOResult
  , checkMIPResult
  ) where

import Control.Monad
import Control.Monad.RWS.Lazy
import qualified Data.ByteString.Char8 as BS
import Data.List (intercalate, sortBy)
import qualified Data.Map.Lazy as Map
import Data.Maybe
import Data.Ord
import qualified Data.PseudoBoolean as PBFile
import Data.Scientific
import Data.String
import qualified Data.Text as T
import qualified Numeric.Optimization.MIP as MIP
import Text.Printf

import qualified ToySolver.FileFormat.CNF as CNF
import qualified ToySolver.SAT.Types as SAT

-- ------------------------------------------------------------------------

type M = RWS () [String] Bool

execM :: M () -> (Bool, [String])
execM m = execRWS m () True

addInfo :: String -> M ()
addInfo s = tell [s]

addError :: String -> M ()
addError s = tell [s] >> put False

-- ------------------------------------------------------------------------

checkSATResult :: CNF.CNF -> (BS.ByteString, Maybe SAT.Model) -> (Bool, [String])
checkSATResult cnf (status, m) = execM $ do
  case status of
    "SATISFIABLE" -> do
      when (isNothing m) $ do
        addError "SATISFIABLE, but a model is missing"
    "UNSATISFIABLE" -> do
      when (isJust m) $ do
        addError "UNSATISFIABLE, but a model is provided"
    "UNKNOWN" -> return ()
    _ -> do
      addError $ "unknown status: " ++ BS.unpack status

  case m of
    Nothing -> return ()
    Just model -> do
      forM_ (CNF.cnfClauses cnf) $ \constr ->
        unless (SAT.evalClause model (SAT.unpackClause constr)) $ do
          addError $ printf "violated: %s" (showClause constr :: String)

checkMaxSATResult :: CNF.WCNF -> (BS.ByteString, Maybe Integer, Maybe SAT.Model) -> (Bool, [String])
checkMaxSATResult wcnf (status, o, m) = execM $ do
  case status of
    "OPTIMUM FOUND" -> do
      when (isNothing m) $ do
        addError "OPTIMUM FOUND, but a model is missing"
    "SATISFIABLE" -> do
      when (isNothing m) $ do
        addError "SATISFIABLE, but a model is missing"
    "UNSATISFIABLE" -> do
      when (isJust m) $ do
        addError "UNSATISFIABLE, but a model is provided"
    "UNKNOWN" -> return ()
    _ -> do
      addError $ "unknown status: " ++ BS.unpack status

  case m of
    Nothing -> return ()
    Just model -> do
      cost <- fmap sum $ forM (CNF.wcnfClauses wcnf) $ \(w, constr) ->
        if SAT.evalClause model (SAT.unpackClause constr) then do
          return 0
        else if w == CNF.wcnfTopCost wcnf then do
          addError $ printf "violated hard constraint: %s" (showClause constr :: String)
          return 0
        else do
          return w
      addInfo $ "total cost = " ++ show cost

      case o of
        Just oVal | oVal /= cost -> do
          addError $ printf "o-line value (%d) is inconsistent" oVal
        _ -> return ()

checkPBResult :: PBFile.Formula -> (BS.ByteString, Maybe Integer, Maybe SAT.Model) -> (Bool, [String])
checkPBResult opb (status, o, m) = execM $ do
  case status of
    "SATISFIABLE" -> do
      when (isNothing m) $ do
        addError "SATISFIABLE, but a model is missing"
    "OPTIMUM FOUND" -> do
      when (isNothing m) $ do
        addError "OPTIMUM FOUND, but a model is missing"
    "UNSATISFIABLE" -> do
      when (isJust m) $ do
        addError "UNSATISFIABLE, but a model is provided"
    "UNSUPPORTED" -> return ()
    "UNKNOWN" -> return ()
    _ -> do
      addError $ "unknown status: " ++ BS.unpack status

  case m of
    Nothing -> return ()
    Just model -> do
      case PBFile.pbObjectiveFunction opb of
        Nothing -> return ()
        Just objFunc -> do
          let val = SAT.evalPBSum model objFunc
          addInfo $ "objective function value = " ++ show val
          case o of
            Just oVal | val /= oVal -> do
              addError $ printf "o-line value (%d) is inconsistent" oVal
            _ -> return ()

      forM_ (PBFile.pbConstraints opb) $ \constr -> do
        unless (SAT.evalPBConstraint model constr) $ do
          addError $ printf "violated: %s" (showPBConstraint constr :: String)

checkWBOResult :: PBFile.SoftFormula -> (BS.ByteString, Maybe Integer, Maybe SAT.Model) -> (Bool, [String])
checkWBOResult wbo (status, o, m) = execM $ do
  case status of
    "SATISFIABLE" -> do
      when (isNothing m) $ do
        addError "SATISFIABLE, but a model is missing"
    "OPTIMUM FOUND" -> do
      when (isNothing m) $ do
        addError "OPTIMUM FOUND, but a model is missing"
    "UNSATISFIABLE" -> do
      when (isJust m) $ do
        addError "UNSATISFIABLE, but a model is provided"
    "UNSUPPORTED" -> return ()
    "UNKNOWN" -> return ()
    _ -> do
      addError $ "unknown status: " ++ BS.unpack status

  case m of
    Nothing -> return ()
    Just model -> do
      cost <- fmap sum $ forM (PBFile.wboConstraints wbo) $ \(w, constr) -> do
        if SAT.evalPBConstraint model constr then
          return 0
        else do
          case w of
            Nothing -> do
              addError $ printf "violated hard constraint: %s" (showPBConstraint constr :: String)
              return 0
            Just w' -> do
              return w'
      addInfo $ "total cost = " ++ show cost

      case PBFile.wboTopCost wbo of
        Just top | top <= cost -> do
          addError $ printf "total cost (%d) is greater than or equal to top cost (%d)" cost top
        _ -> return ()

      case o of
        Just oVal | oVal /= cost -> do
          addError $ printf "o-line value (%d) is inconsistent" oVal
        _ -> return ()

checkMIPResult :: MIP.Tol Scientific -> MIP.Problem Scientific -> MIP.Solution Scientific -> (Bool, [String])
checkMIPResult tol mip sol = execM $ do
  let m = MIP.solVariables sol

  let objVal = MIP.eval tol m (MIP.objExpr (MIP.objectiveFunction mip))
  addInfo $ "objective value = " ++ show objVal
  case MIP.solObjectiveValue sol of
    Nothing -> return ()
    Just declaredObjVal -> do
      unless (abs (objVal - declaredObjVal) <= MIP.feasibilityTol tol) $ do
        addError $ printf "declared objective value (%s) does not match to the computed value (%s)"
          (show declaredObjVal) (show objVal)

  forM_ (Map.toList (MIP.varDomains mip)) $ \(v, (vt, bounds@(lb,ub))) -> do
    let val = MIP.eval tol m v
        flag1 =
          case vt of
            MIP.ContinuousVariable -> True
            MIP.SemiContinuousVariable -> True
            MIP.IntegerVariable -> isIntegral tol val
            MIP.SemiIntegerVariable -> isIntegral tol val
        flag2 =
          case vt of
            MIP.ContinuousVariable -> isInBounds tol bounds val
            MIP.IntegerVariable -> isInBounds tol bounds val
            MIP.SemiIntegerVariable -> isInBounds tol (0,0) val || isInBounds tol bounds val
            MIP.SemiContinuousVariable -> isInBounds tol (0,0) val || isInBounds tol bounds val
    unless flag1 $ do
      addError $ printf "variable %s is not integral" (T.unpack (MIP.varName v))
    unless flag2 $ do
      let f MIP.NegInf = "-inf"
          f MIP.PosInf = "+inf"
          f (MIP.Finite x) = show x
      addError $ printf "variable %s is out of bounds lb=%s ub=%s" (T.unpack (MIP.varName v)) (f lb) (f ub)

  forM_ (MIP.constraints mip) $ \constr -> do
    unless (MIP.eval tol m constr) $ do
      addError $ case MIP.constrLabel constr of
        Just name -> printf "violated: %s" (T.unpack name)
        Nothing -> printf "violated: %s" (showMIPConstraint constr)

  forM_ (MIP.sosConstraints mip) $ \constr -> do
    unless (MIP.eval tol m constr) $ do
      addError $ case MIP.sosLabel constr of
        Just name -> printf "violated: %s" (T.unpack name)
        Nothing -> printf "violated: %s" (showMIPSOSConstraint constr)

-- ------------------------------------------------------------------------

showClause :: (Monoid a, IsString a) => SAT.PackedClause -> a
showClause = foldr (\f g -> f <> fromString " " <> g) mempty . map (fromString . show) . SAT.unpackClause

showPBSum :: (Monoid a, IsString a) => PBFile.Sum -> a
showPBSum = mconcat . map showWeightedTerm
  where
    showWeightedTerm :: (Monoid a, IsString a) => PBFile.WeightedTerm -> a
    showWeightedTerm (c, lits) = foldr (\f g -> f <> fromString " " <> g) mempty (x:xs)
      where
        x = if c >= 0 then fromString "+" <> fromString (show c) else fromString (show c)
        xs = map showLit $ sortBy (comparing abs) lits

    showLit :: (Monoid a, IsString a) => PBFile.Lit -> a
    showLit lit = if lit > 0 then v else fromString "~" <> v
      where
        v = fromString "x" <> fromString (show (abs lit))

showPBConstraint :: (Monoid a, IsString a) => PBFile.Constraint -> a
showPBConstraint (lhs, op, rhs) =
  showPBSum lhs <> f op <>  fromString " " <> fromString (show rhs)
  where
    f PBFile.Eq = fromString "="
    f PBFile.Ge = fromString ">="

showMIPConstraint :: MIP.Constraint Scientific -> String
showMIPConstraint constr = concat
  [ case MIP.constrIndicator constr of
      Nothing -> ""
      Just (MIP.Var var, val) ->
        let rhs =
              case floatingOrInteger val of
                Right (i :: Integer) -> show i
                Left (_ :: Double) -> show val  -- should be error?
         in T.unpack var ++ " = " ++ rhs ++ " -> "
  , case MIP.constrLB constr of
      MIP.NegInf -> ""
      MIP.PosInf -> "+inf <= "
      MIP.Finite x -> show x ++ " <= "
  , showMIPExpr (MIP.constrExpr constr)
  , case MIP.constrUB constr of
      MIP.NegInf -> "<= -inf"
      MIP.PosInf -> ""
      MIP.Finite x -> " <= " ++ show x
  ]

showMIPSOSConstraint :: MIP.SOSConstraint Scientific -> String
showMIPSOSConstraint constr = concat $
  [show (MIP.sosType constr), " ::"] ++ [
    " " ++ T.unpack (MIP.varName v) ++ " : " ++ show r
  | (v, r) <- MIP.sosBody constr
  ]

showMIPExpr :: MIP.Expr Scientific -> String
showMIPExpr e = intercalate " "
  [ intercalate "*" (((if c >= 0 then "+" ++ show c else show c) : map (T.unpack . MIP.varName) vs))
  | MIP.Term c vs <- MIP.terms e
  ]

isIntegral :: RealFrac r => MIP.Tol r -> r -> Bool
isIntegral tol x = abs (x - fromIntegral (floor (x + 0.5) :: Integer)) <= MIP.integralityTol tol

isInBounds :: (Num r, Ord r) => MIP.Tol r -> MIP.Bounds r -> r -> Bool
isInBounds tol (lb, ub) x =
  lb - MIP.Finite (MIP.feasibilityTol tol) <= MIP.Finite x &&
  MIP.Finite x <= ub + MIP.Finite (MIP.feasibilityTol tol)

-- ------------------------------------------------------------------------
