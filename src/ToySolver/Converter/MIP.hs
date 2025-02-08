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
  , mip2pb
  , MIP2PBInfo (..)
  , addMIP
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
import Data.List (intercalate, foldl', sortBy)
import Data.Maybe
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Ord
import Data.Primitive.MutVar
import Data.Ratio
import qualified Data.Set as Set
import Data.String
import qualified Data.Text as T
import Data.VectorSpace

import qualified Data.PseudoBoolean as PBFile
import qualified Numeric.Optimization.MIP as MIP

import ToySolver.Converter.Base
import ToySolver.Converter.PB
import ToySolver.Data.OrdRel
import qualified ToySolver.FileFormat.CNF as CNF
import ToySolver.Internal.JSON
import ToySolver.SAT.Internal.JSON
import qualified ToySolver.SAT.Types as SAT
import qualified ToySolver.SAT.Encoder.Integer as Integer
import ToySolver.SAT.Store.PB
import ToySolver.Internal.Util (revForM)

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
        [ toKey (MIP.varName v) .= jPBSum s
        | (v, Integer.Expr s) <- Map.toList vmap
        ]
    , "nonzero_indicators" .= J.object
        [ toKey (MIP.varName v) .= (jLitName lit :: J.Value)
        | (v, lit) <- Map.toList nonZeroTable
        ]
    , "objective_function_scale_factor" .= d
    ]
    where
#if MIN_VERSION_aeson(2,0,0)
      toKey = Key.fromText
#else
      toKey = id
#endif

instance J.FromJSON MIP2PBInfo where
  parseJSON = withTypedObject "MIP2PBInfo" $ \obj -> do
    tmp1 <- obj .: "substitutions"
    subst <- liftM Map.fromList $ forM (Map.toList tmp1) $ \(name, expr) -> do
      s <- parsePBSum expr
      return (MIP.Var name, Integer.Expr s)
    tmp2 <- obj .: "nonzero_indicators"
    nonZeroTable <- liftM Map.fromList $ forM (Map.toList tmp2) $ \(name, s) -> do
      lit <- parseLitName s
      return (MIP.Var name, lit)
    d <- obj .: "objective_function_scale_factor"
    pure $ MIP2PBInfo subst nonZeroTable d

addMIP :: (SAT.AddPBNL m enc, PrimMonad m) => enc -> MIP.Problem Rational -> m (Either String (Integer.Expr, MIP2PBInfo))
addMIP enc mip = runExceptT $ addMIP' enc mip

addMIP' :: forall m enc. (SAT.AddPBNL m enc, PrimMonad m) => enc -> MIP.Problem Rational -> ExceptT String m (Integer.Expr, MIP2PBInfo)
addMIP' enc mip = do
  if not (Set.null nivs) then do
    throwE $ "cannot handle non-integer variables: " ++ intercalate ", " (map (T.unpack . MIP.varName) (Set.toList nivs))
  else do
    vmap <- liftM Map.fromList $ revForM (Set.toList ivs) $ \v -> do
      case MIP.getBounds mip v of
        (MIP.Finite lb, MIP.Finite ub) -> do
          v2 <- lift $ Integer.newVar enc (ceiling lb) (floor ub)
          return (v,v2)
        _ -> do
          throwE $ "cannot handle unbounded variable: " ++ T.unpack (MIP.varName v)
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

asInteger :: Rational -> Integer
asInteger r
  | denominator r /= 1 = error (show r ++ " is not integer")
  | otherwise = numerator r

-- -----------------------------------------------------------------------------
