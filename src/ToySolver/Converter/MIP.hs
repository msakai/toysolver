{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_HADDOCK show-extensions #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.Converter.MIP
-- Copyright   :  (c) Masahiro Sakai 2011-2016
-- License     :  BSD-style
--
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  experimental
-- Portability :  non-portable
--
-----------------------------------------------------------------------------
module ToySolver.Converter.MIP
  (
  -- * PB/WBO to IP
    pb2ip
  , PB2IPInfo
  , wbo2ip
  , WBO2IPInfo

  -- * SAT/Max-SAT to IP
  , sat2ip
  , SAT2IPInfo
  , maxsat2ip
  , MaxSAT2IPInfo

  -- * IP to PB
  , ip2pb
  , IP2PBInfo (..)
  , addMIP

  -- * Linearization of the constant term in objective function
  , normalizeMIPObjective
  , NormalizeMIPObjectiveInfo (..)
  ) where

import Control.Monad
import Control.Monad.Primitive
import Control.Monad.ST
import Control.Monad.Trans
import Control.Monad.Trans.Except
import qualified Data.Aeson as J
import qualified Data.Aeson.Types as J
#if MIN_VERSION_aeson(2,0,0)
import qualified Data.Aeson.Key as Key
#endif
import Data.Aeson ((.=), (.:))
import Data.Array.IArray
import Data.Default.Class
import qualified Data.IntSet as IntSet
import Data.List (intercalate, foldl', foldl1',  sortBy)
import Data.Maybe
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Ord
import Data.Primitive.MutVar
import Data.Ratio
import qualified Data.Set as Set
import Data.String
import qualified Data.Text as T
import qualified Data.Vector as V
import qualified Data.Vector.Generic as VG
import Data.VectorSpace
import Text.Printf

import qualified Data.PseudoBoolean as PBFile
import qualified Numeric.Optimization.MIP as MIP

import qualified ToySolver.Combinatorial.SubsetSum as SubsetSum
import ToySolver.Converter.Base
import ToySolver.Converter.PB
import ToySolver.Data.OrdRel
import qualified ToySolver.FileFormat.CNF as CNF
import ToySolver.Internal.JSON
import ToySolver.SAT.Internal.JSON
import qualified ToySolver.SAT.Types as SAT
import qualified ToySolver.SAT.Encoder.Integer as Integer
import ToySolver.SAT.Store.PB

-- -----------------------------------------------------------------------------

newtype PB2IPInfo = PB2IPInfo Int
  deriving (Eq, Show, Read)

instance Transformer PB2IPInfo where
  type Source PB2IPInfo = SAT.Model
  type Target PB2IPInfo = Map MIP.Var Rational

instance ForwardTransformer PB2IPInfo where
  transformForward _ m =
    Map.fromList [(convVar v, if val then 1 else 0) | (v,val) <- assocs m]

instance BackwardTransformer PB2IPInfo where
  transformBackward (PB2IPInfo nv) = mtrans nv

instance ObjValueTransformer PB2IPInfo where
  type SourceObjValue PB2IPInfo = Integer
  type TargetObjValue PB2IPInfo = Rational

instance ObjValueForwardTransformer PB2IPInfo where
  transformObjValueForward _ = fromIntegral

instance ObjValueBackwardTransformer PB2IPInfo where
  transformObjValueBackward _ = round

instance J.ToJSON PB2IPInfo where
  toJSON (PB2IPInfo nv) =
    J.object
    [ "type" .= ("PB2IPInfo" :: J.Value)
    , "num_original_variables" .= nv
    ]

instance J.FromJSON PB2IPInfo where
  parseJSON =
    withTypedObject "PB2IPInfo" $ \obj ->
      PB2IPInfo <$> obj .: "num_original_variables"

pb2ip :: PBFile.Formula -> (MIP.Problem Integer, PB2IPInfo)
pb2ip formula = (mip, PB2IPInfo (PBFile.pbNumVars formula))
  where
    mip = def
      { MIP.objectiveFunction = obj2
      , MIP.constraints = cs2
      , MIP.varDomains = Map.fromList [(v, (MIP.IntegerVariable, (0,1))) | v <- vs]
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


convExpr :: PBFile.Sum -> MIP.Expr Integer
convExpr s = sum [product (fromIntegral w : map f tm) | (w,tm) <- s]
  where
    f :: PBFile.Lit -> MIP.Expr Integer
    f x
      | x > 0     = MIP.varExpr (convVar x)
      | otherwise = 1 - MIP.varExpr (convVar (abs x))

convVar :: PBFile.Var -> MIP.Var
convVar x = fromString ("x" ++ show x)

-- -----------------------------------------------------------------------------

data WBO2IPInfo = WBO2IPInfo !Int [(MIP.Var, PBFile.Constraint)]
  deriving (Eq, Show)

instance Transformer WBO2IPInfo where
  type Source WBO2IPInfo = SAT.Model
  type Target WBO2IPInfo = Map MIP.Var Rational

instance ForwardTransformer WBO2IPInfo where
  transformForward (WBO2IPInfo _nv relaxVariables) m = Map.union m1 m2
      where
        m1 = Map.fromList $ [(convVar v, if val then 1 else 0) | (v,val) <- assocs m]
        m2 = Map.fromList $ [(v, if SAT.evalPBConstraint m c then 0 else 1) | (v, c) <- relaxVariables]

instance BackwardTransformer WBO2IPInfo where
  transformBackward (WBO2IPInfo nv _relaxVariables) = mtrans nv

instance ObjValueTransformer WBO2IPInfo where
  type SourceObjValue WBO2IPInfo = Integer
  type TargetObjValue WBO2IPInfo = Rational

instance ObjValueForwardTransformer WBO2IPInfo where
  transformObjValueForward _ = fromIntegral

instance ObjValueBackwardTransformer WBO2IPInfo where
  transformObjValueBackward _ = round

instance J.ToJSON WBO2IPInfo where
  toJSON (WBO2IPInfo nv relaxVariables) =
    J.object
    [ "type" .= ("WBO2IPInfo" :: J.Value)
    , "num_original_variables" .= nv
    , "relax_variables" .= J.object
        [ toKey (MIP.varName v) .= jPBConstraint constr
        | (v, constr) <- relaxVariables
        ]
    ]
    where
#if MIN_VERSION_aeson(2,0,0)
      toKey = Key.fromText
#else
      toKey = id
#endif

instance J.FromJSON WBO2IPInfo where
  parseJSON =
    withTypedObject "WBO2IPInfo" $ \obj -> do
      xs <- obj .: "relax_variables"
      WBO2IPInfo
        <$> obj .: "num_original_variables"
        <*> mapM f (Map.toList xs)
    where
      f :: (T.Text, J.Value) -> J.Parser (MIP.Var, PBFile.Constraint)
      f (name, val) = do
        constr <- parsePBConstraint val
        pure (MIP.Var name, constr)

wbo2ip :: Bool -> PBFile.SoftFormula -> (MIP.Problem Integer, WBO2IPInfo)
wbo2ip useIndicator formula = (mip, WBO2IPInfo (PBFile.wboNumVars formula) [(r, c) | (r, (Just _, c)) <- relaxVariables])
  where
    mip = def
      { MIP.objectiveFunction = obj2
      , MIP.constraints = topConstr ++ map snd cs2
      , MIP.varDomains = Map.fromList [(v, (MIP.IntegerVariable, (0,1))) | v <- vs]
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
    relaxVariables = [(fromString ("r" ++ show n), c) | (n, c) <- zip [(0::Int)..] (PBFile.wboConstraints formula)]

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
                 PBFile.Ge -> (lhs2 MIP..>=. MIP.constExpr rhs2) { MIP.constrIndicator = ind }
                 PBFile.Eq -> (lhs2 MIP..==. MIP.constExpr rhs2) { MIP.constrIndicator = ind }
         return (ts, c)
      else do
         let (lhsGE,rhsGE) = relaxGE v (lhs2,rhs2)
             c1 = lhsGE MIP..>=. MIP.constExpr rhsGE
         case op of
           PBFile.Ge -> do
             return (ts, c1)
           PBFile.Eq -> do
             let (lhsLE,rhsLE) = relaxLE v (lhs2,rhs2)
                 c2 = lhsLE MIP..<=. MIP.constExpr rhsLE
             [ (ts, c1), ([], c2) ]

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

-- -----------------------------------------------------------------------------

type SAT2IPInfo = ComposedTransformer SAT2PBInfo PB2IPInfo

sat2ip :: CNF.CNF -> (MIP.Problem Integer, SAT2IPInfo)
sat2ip cnf = (ip, ComposedTransformer info1 info2)
  where
    (pb,info1) = sat2pb cnf
    (ip,info2) = pb2ip pb

type MaxSAT2IPInfo = ComposedTransformer MaxSAT2WBOInfo WBO2IPInfo

maxsat2ip :: Bool -> CNF.WCNF -> (MIP.Problem Integer, MaxSAT2IPInfo)
maxsat2ip useIndicator wcnf = (ip, ComposedTransformer info1 info2)
  where
    (wbo, info1) = maxsat2wbo wcnf
    (ip, info2) = wbo2ip useIndicator wbo

-- -----------------------------------------------------------------------------

ip2pb :: MIP.Problem Rational -> Either String (PBFile.Formula, IP2PBInfo)
ip2pb mip = runST $ runExceptT $ m
  where
    m :: ExceptT String (ST s) (PBFile.Formula, IP2PBInfo)
    m = do
      db <- lift $ newPBStore
      (Integer.Expr obj, info) <- addMIP' db mip
      formula <- lift $ getPBFormula db
      return $ (formula{ PBFile.pbObjectiveFunction = Just obj }, info)

data IP2PBInfo = IP2PBInfo (Map MIP.Var Integer.Expr) (Map MIP.Var SAT.Lit) !Rational
  deriving (Eq, Show)

instance Transformer IP2PBInfo where
  type Source IP2PBInfo = Map MIP.Var Rational
  type Target IP2PBInfo = SAT.Model

instance ForwardTransformer IP2PBInfo where
  transformForward (IP2PBInfo vmap nonZeroTable _s) sol
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
        | otherwise =
            case SubsetSum.subsetSum (V.fromList (map fst s')) d of
              Nothing -> error "failed to reconstruct boolean assignment"
              Just sol -> [if l > 0 then (l, v) else (- l, not v) | (l, v) <- zip (map snd s') (VG.toList sol)]
        where
          s' = [if null ls then (c, l) else error "variable definition should be linear" | (c, l : ls) <- s]
          d = numerator val - sum [c | (c, []) <- s]

instance BackwardTransformer IP2PBInfo where
  transformBackward (IP2PBInfo vmap _nonZeroTable _s) m = fmap (toRational . Integer.eval m) vmap

instance ObjValueTransformer IP2PBInfo where
  type SourceObjValue IP2PBInfo = Rational
  type TargetObjValue IP2PBInfo = Integer

instance ObjValueForwardTransformer IP2PBInfo where
  transformObjValueForward (IP2PBInfo _vmap _nonZeroTable s) val = asInteger (val * s)

instance ObjValueBackwardTransformer IP2PBInfo where
  transformObjValueBackward (IP2PBInfo _vmap _nonZeroTable s) val = fromIntegral val / s

instance J.ToJSON IP2PBInfo where
  toJSON (IP2PBInfo vmap nonZeroTable s) =
    J.object
    [ "type" .= ("IP2PBInfo" :: J.Value)
    , "substitutions" .= J.object
        [ toKey (MIP.varName v) .= jPBSum s
        | (v, Integer.Expr s) <- Map.toList vmap
        ]
    , "nonzero_indicators" .= J.object
        [ toKey (MIP.varName v) .= (jLitName lit :: J.Value)
        | (v, lit) <- Map.toList nonZeroTable
        ]
    , "objective_function_scale_factor" .=
        J.object
        [ "numerator" .= numerator s
        , "denominator" .= denominator s
        ]
    ]
    where
#if MIN_VERSION_aeson(2,0,0)
      toKey = Key.fromText
#else
      toKey = id
#endif

instance J.FromJSON IP2PBInfo where
  parseJSON = withTypedObject "IP2PBInfo" $ \obj -> do
    tmp1 <- obj .: "substitutions"
    subst <- liftM Map.fromList $ forM (Map.toList tmp1) $ \(name, expr) -> do
      s <- parsePBSum expr
      return (MIP.Var name, Integer.Expr s)
    tmp2 <- obj .: "nonzero_indicators"
    nonZeroTable <- liftM Map.fromList $ forM (Map.toList tmp2) $ \(name, s) -> do
      lit <- parseLitName s
      return (MIP.Var name, lit)
    v <- obj .: "objective_function_scale_factor"
    s <- fmap fromInteger (J.parseJSON v) `mplus` parseRat v
    pure $ IP2PBInfo subst nonZeroTable s
    where
      parseRat = J.withObject "Rational" $ \obj -> (%)
        <$> obj .: "numerator"
        <*> obj .: "denominator"

addMIP :: (SAT.AddPBNL m enc, PrimMonad m) => enc -> MIP.Problem Rational -> m (Either String (Integer.Expr, IP2PBInfo))
addMIP enc mip = runExceptT $ addMIP' enc mip

addMIP' :: forall m enc. (SAT.AddPBNL m enc, PrimMonad m) => enc -> MIP.Problem Rational -> ExceptT String m (Integer.Expr, IP2PBInfo)
addMIP' enc mip = do
  let contVars = Map.filter p (MIP.varDomains mip)
        where
          p (MIP.ContinuousVariable, _) = True
          p (MIP.SemiContinuousVariable, _) = True
          p (_, _) = False  
  unless (Map.null contVars) $ do
    let n = Map.size contVars
        vars = intercalate ", " (map (T.unpack . MIP.varName) (take 10 (Map.keys contVars)) ++ ["..." | n > 10])
        msg = printf "Unsupported problem: %d (semi-)continuous variables (%s)" n vars
    throwE msg

  let unboundedVars = Map.filter p (MIP.varDomains mip)
        where
          p (_, (MIP.Finite _, MIP.Finite _)) = False
          p (_, _) = True
  unless (Map.null unboundedVars) $ do
    let n = Map.size unboundedVars
        vars = intercalate ", " (map (T.unpack . MIP.varName) (take 10 (Map.keys unboundedVars)) ++ ["..." | n > 10])
        msg = printf "Unsupported problem: %d unbounded variables (%s)" n vars
    throwE msg

  nonZeroTableRef <- lift $ newMutVar Map.empty

  vmap <- fmap Map.fromDistinctAscList $ forM (Map.toAscList (MIP.varDomains mip)) $ \(v, dom) ->
    case dom of
      (vt, (MIP.Finite lb, MIP.Finite ub)) -> do
        let lb' = ceiling lb
            ub' = floor ub
        if vt == MIP.IntegerVariable || lb' <= 0 && 0 <= ub' then do
          v2 <- lift $ Integer.newVar enc lb' ub'
          return (v,v2)
        else do
          -- vt == MIP.IntegerVariable && (0 <= lb' || ub' <= 0)
          v2@(Integer.Expr s) <- lift $ Integer.newVar enc (min 0 lb') (max 0 ub')
          lift $ do
            y <- SAT.newVar enc
            SAT.addPBNLAtLeast enc (s ++ [(- lb', [y])]) 0
            SAT.addPBNLAtMost enc (s ++ [(- ub', [y])]) 0
            modifyMutVar nonZeroTableRef (Map.insert v y)
          return (v,v2)
      _ -> error "should not happen"

  forM_ (MIP.constraints mip) $ \c -> do
    let lhs = MIP.constrExpr c
    let f op rhs = do
          let m = foldl' lcm 1 (map denominator (rhs:[r | MIP.Term r _ <- MIP.terms lhs]))
              d = foldl1' gcd (map (abs . numerator) (rhs:[r | MIP.Term r _ <- MIP.terms lhs]))
              -- For ease of understanding, no scaling is performed if the values were already integers
              s = if m == 1 then 1 else m % d
              lhs' = sumV [asInteger (r * s) *^ product [vmap Map.! v | v <- vs] | MIP.Term r vs <- MIP.terms lhs]
              rhs' = asInteger (rhs * s)
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
      m = foldl' lcm 1 [denominator r | MIP.Term r _ <- MIP.terms (MIP.objExpr obj)]
      d = if null (MIP.terms (MIP.objExpr obj)) then 1
          else foldl1' gcd [abs (numerator r) | MIP.Term r _ <- MIP.terms (MIP.objExpr obj)]
      -- For ease of understanding, no scaling is performed if the values were already integers
      s = (if MIP.objDir obj == MIP.OptMin then 1 else -1) * (if m == 1 then 1 else m % d)
      obj2 = sumV [asInteger (r * s) *^ product [vmap Map.! v | v <- vs] | MIP.Term r vs <- MIP.terms (MIP.objExpr obj)]

  nonZeroTable <- readMutVar nonZeroTableRef

  return (obj2, IP2PBInfo vmap nonZeroTable s)

  where
    asBin :: Integer.Expr -> SAT.Lit
    asBin (Integer.Expr [(1,[lit])]) = lit
    asBin _ = error "asBin: failure"

asInteger :: Rational -> Integer
asInteger r
  | denominator r /= 1 = error (show r ++ " is not integer")
  | otherwise = numerator r

-- -----------------------------------------------------------------------------

normalizeMIPObjective :: (Num c, Eq c) => MIP.Problem c -> (MIP.Problem c, NormalizeMIPObjectiveInfo r)
normalizeMIPObjective prob@MIP.Problem{ MIP.objectiveFunction = obj }
  | offset == 0 = (prob{ MIP.objectiveFunction = obj{ MIP.objExpr = e }}, NormalizeMIPObjectiveInfo Nothing)
  | otherwise =
      ( prob
        { MIP.objectiveFunction = obj{ MIP.objExpr = e + MIP.Expr [MIP.Term offset [unit_var]] }
        , MIP.varDomains = Map.insert unit_var (MIP.IntegerVariable, (MIP.Finite 1, MIP.Finite 1)) (MIP.varDomains prob)
        }
      , NormalizeMIPObjectiveInfo (Just unit_var)
      )
  where
    offset = sum [c | MIP.Term c [] <- MIP.terms (MIP.objExpr obj)]
    e = MIP.Expr [t | t@(MIP.Term _ (_:_)) <- MIP.terms (MIP.objExpr obj)]
    used = MIP.variables prob
    candidates = map MIP.Var $ "unit" : [T.pack ("unit" ++ show i) | i <- [1..]]
    unit_var = head [name | name <- candidates, name `Set.notMember` used]

newtype NormalizeMIPObjectiveInfo r = NormalizeMIPObjectiveInfo (Maybe MIP.Var)
  deriving (Eq, Show)

instance Transformer (NormalizeMIPObjectiveInfo r) where
  type Source (NormalizeMIPObjectiveInfo r) = Map MIP.Var r
  type Target (NormalizeMIPObjectiveInfo r) = Map MIP.Var r

instance Num r => ForwardTransformer (NormalizeMIPObjectiveInfo r) where
  transformForward (NormalizeMIPObjectiveInfo Nothing) sol = sol
  transformForward (NormalizeMIPObjectiveInfo (Just v)) sol = Map.insert v 1 sol

instance BackwardTransformer (NormalizeMIPObjectiveInfo r) where
  transformBackward (NormalizeMIPObjectiveInfo Nothing) sol = sol
  transformBackward (NormalizeMIPObjectiveInfo (Just v)) sol = Map.delete v sol

instance ObjValueTransformer (NormalizeMIPObjectiveInfo r) where
  type SourceObjValue (NormalizeMIPObjectiveInfo r) = r
  type TargetObjValue (NormalizeMIPObjectiveInfo r) = r

instance ObjValueForwardTransformer (NormalizeMIPObjectiveInfo r) where
  transformObjValueForward (NormalizeMIPObjectiveInfo _) val = val

instance ObjValueBackwardTransformer (NormalizeMIPObjectiveInfo r) where
  transformObjValueBackward (NormalizeMIPObjectiveInfo _) val = val

instance J.ToJSON (NormalizeMIPObjectiveInfo r) where
  toJSON (NormalizeMIPObjectiveInfo m) =
    J.object
    [ "type" .= ("NormalizeMIPObjectiveInfo" :: J.Value)
    , "unit_var" .= fmap MIP.varName m
    ]

instance J.FromJSON (NormalizeMIPObjectiveInfo r) where
  parseJSON = withTypedObject "NormalizeMIPObjectiveInfo" $ \obj -> do
    (NormalizeMIPObjectiveInfo . fmap MIP.Var) <$> obj .: "unit_var"

-- -----------------------------------------------------------------------------
