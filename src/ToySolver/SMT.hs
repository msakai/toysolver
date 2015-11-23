{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances, CPP #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.SMT
-- Copyright   :  (c) Masahiro Sakai 2015
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  unstable
-- Portability :  non-portable (MultiParamTypeClasses, FlexibleInstances, CPP)
--
-----------------------------------------------------------------------------
module ToySolver.SMT
  (
  -- * The Solver type
    Solver
  , newSolver

  -- * Problem Specification
  , SSym (..)
  , ssymArity
  , Sort (..)
  , sBool
  , sReal
  , Type
  , Expr (..)
  , FSym
  , declareSSym
  , declareSort
  , VASortFun
  , declareFSym
  , declareFun
  , declareConst
  , VAFun
  , assert

  -- * Solving
  , checkSAT
  , pushContext
  , popContext

  -- * Model
  , Model
  , Value (..)
  , getModel
  , eval
  ) where

import Control.Monad
import Control.Monad.Trans
import Control.Monad.Trans.Except
import Data.Either
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import Data.IORef
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.VectorSpace

import ToySolver.Data.Delta
import ToySolver.Data.Boolean
import ToySolver.Data.BoolExpr
import ToySolver.Data.OrdRel
import qualified ToySolver.Data.LA as LA
import qualified ToySolver.Internal.Data.Vec as Vec
import qualified ToySolver.SAT as SAT
import ToySolver.SAT.TheorySolver
import qualified ToySolver.SAT.TseitinEncoder as Tseitin
import qualified ToySolver.Arith.Simplex2 as Simplex2
import qualified ToySolver.EUF.EUFSolver as EUF

type FSym = String

-- | Sort symbols
data SSym
  = SSymBool
  | SSymReal
  | SSymUserDefined String !Int
  deriving (Show, Eq, Ord)

ssymArity :: SSym -> Int
ssymArity SSymBool = 0
ssymArity SSymReal = 0
ssymArity (SSymUserDefined _ ar) = ar

data Sort = Sort SSym [Sort]
  deriving (Show, Eq, Ord)

sBool :: Sort
sBool = Sort SSymBool []

sReal :: Sort
sReal = Sort SSymReal []

type Type = ([Sort],Sort)

data Expr
  = EAp FSym [Expr]
  | EFrac Rational
  deriving (Show)

instance MonotoneBoolean Expr where
  true  = EAp "true" []
  false = EAp "false" []
  andB = EAp "and"
  orB  = EAp "or"

instance Complement Expr where
  notB x = EAp "not" [x]

instance IfThenElse Expr Expr where
  ite x y z = EAp "ite" [x,y,z]

instance Boolean Expr where
  x .=>. y  = EAp "=>" [x,y]
  x .<=>. y = EAp "<=>" [x,y]

instance Num Expr where
  x + y = EAp "+" [x,y]
  x - y = EAp "-" [x,y]
  x * y = EAp "*" [x,y]
  negate x = EAp "-" [x]
  abs x = error "Num{ToySolver.SMT.Expr}.abs is not implemented"
  signum x = error "Num{ToySolver.SMT.Expr}.signum is not implemented"
  fromInteger x = EFrac (fromInteger x)

instance Fractional Expr where
  x / y = EAp "/" [x,y]
  fromRational x = EFrac x

instance IsEqRel Expr Expr where
  a .==. b = EAp "=" [a,b]
  a ./=. b = notB (a .==. b)

instance IsOrdRel Expr Expr where
  a .<. b = EAp "<" [a,b]
  a .>. b = EAp ">" [a,b]
  a .<=. b = EAp "<=" [a,b]
  a .>=. b = EAp ">=" [a,b]

data FDef
  = FBoolVar SAT.Var
  | FLRAVar LA.Var
  | FEUFFun Type EUF.FSym
  deriving (Show)

data Solver
  = Solver
  { smtSAT :: !SAT.Solver
  , smtEnc :: !Tseitin.Encoder
  , smtEUF :: !EUF.Solver
  , smtLRA :: !(Simplex2.GenericSolver (Delta Rational))

  , smtEUFAtomDefs  :: !(IORef (Map (EUF.Term, EUF.Term) SAT.Var, IntMap (EUF.Term, EUF.Term)))
  , smtLRAAtomDefs  :: !(IORef (Map (LA.Var, Rational) (SAT.Lit, SAT.Lit, SAT.Lit), IntMap (LA.Atom Rational)))
  , smtBoolTermDefs :: !(IORef (Map EUF.Term SAT.Lit, IntMap EUF.Term))
  , smtRealTermDefs :: !(IORef (Map (LA.Expr Rational) EUF.FSym, IntMap (LA.Expr Rational)))
  , smtEUFTrue  :: !EUF.Term
  , smtEUFFalse :: !EUF.Term
  , smtEUFModel :: !(IORef EUF.Model)

  , smtFDefs :: !(IORef (Map FSym FDef))

  , smtContexts :: !(Vec.UVec SAT.Lit)
  }

newSolver :: IO Solver
newSolver = do
  sat <- SAT.newSolver
  enc <- Tseitin.newEncoder sat
  euf <- EUF.newSolver
  lra <- Simplex2.newSolver

  litTrue <- Tseitin.encodeConj enc []
  let litFalse = -litTrue

  eufTrue  <- EUF.newConst euf
  eufFalse <- EUF.newConst euf
  EUF.assertNotEqual euf eufTrue eufFalse

  eufAtomDefs <- newIORef (Map.empty, IntMap.empty)
  lraAtomDefs <- newIORef (Map.empty, IntMap.empty)
  boolTermDefs <- newIORef $
    ( Map.fromList [(eufTrue, litTrue), (eufFalse, litFalse)]
    , IntMap.fromList [(litTrue, eufTrue), (litFalse, eufFalse)]
    )
  realTermDefs <- newIORef (Map.empty, IntMap.empty)

  eufModelRef <- newIORef (undefined :: EUF.Model)

  fdefs <- newIORef Map.empty

  conflictTheory <- newIORef True

  let tsolver =
        TheorySolver
        { thAssertLit = \_ l -> do
            (_, defsLRA) <- readIORef lraAtomDefs
            (_, defsEUF) <- readIORef eufAtomDefs
            case IntMap.lookup l defsLRA of
              Just atom -> do
                Simplex2.assertAtomEx' lra atom (Just l)
                return True
              Nothing ->
                case IntMap.lookup (SAT.litVar l) defsEUF of
                  Just (t1,t2) -> do
                    if SAT.litPolarity l then do
                      EUF.assertEqual' euf t1 t2 (Just l)
                      return True
                    else do
                      EUF.assertNotEqual' euf t1 t2 (Just l)
                      return True
                  Nothing ->
                    return True
        , thCheck = \callback -> do
            b <- Simplex2.check lra
            if b then do
              b2 <- EUF.check euf
              if b2 then do
                (_, defsEUF) <- readIORef eufAtomDefs
                liftM isRight $ runExceptT $ do
                  forM_ (IntMap.toList defsEUF) $ \(v, (t1, t2)) -> do
                    b3 <- lift $ EUF.areEqual euf t1 t2
                    when b3 $ do
                      b4 <- lift $ callback v
                      unless b4 $ throwE ()
              else do
                writeIORef conflictTheory False
                return b2
            else do
              writeIORef conflictTheory True
              return False
        , thExplain = \m -> do
            case m of
              Nothing -> do
                b <- readIORef conflictTheory
                if b then
                  liftM IntSet.toList $ Simplex2.explain lra
                else
                  liftM IntSet.toList $ EUF.explain euf Nothing
              Just v -> do
                (_, defsEUF) <- readIORef eufAtomDefs
                case IntMap.lookup v defsEUF of
                  Nothing -> error "should not happen"
                  Just (t1,t2) -> liftM IntSet.toList $ EUF.explain euf (Just (t1,t2))
        , thPushBacktrackPoint = do
            Simplex2.pushBacktrackPoint lra
            EUF.pushBacktrackPoint euf
        , thPopBacktrackPoint = do
            Simplex2.popBacktrackPoint lra
            EUF.popBacktrackPoint euf
        , thConstructModel = do
            writeIORef eufModelRef =<< EUF.getModel euf
            return ()
        }
  SAT.setTheory sat tsolver

  contexts <- Vec.new

  return $
    Solver
    { smtSAT = sat
    , smtEnc = enc
    , smtEUF = euf
    , smtLRA = lra

    , smtEUFAtomDefs = eufAtomDefs
    , smtLRAAtomDefs = lraAtomDefs
    , smtBoolTermDefs = boolTermDefs
    , smtRealTermDefs = realTermDefs
    , smtEUFTrue  = eufTrue
    , smtEUFFalse = eufFalse
    , smtEUFModel = eufModelRef

    , smtFDefs = fdefs

    , smtContexts = contexts
    }

declareSSym :: Solver -> String -> Int -> IO SSym
declareSSym solver name arity = return (SSymUserDefined name arity)

declareSort :: VASortFun a => Solver -> String -> Int -> IO a
declareSort solver name arity = do
  ssym <- declareSSym solver name arity
  let f = withSortVArgs (Sort ssym)
  unless (arityVASortFun f == arity) $ error "ToySolver.SMT.declareSort: argument number error"
  return f

class VASortFun a where
  withSortVArgs :: ([Sort] -> Sort) -> a
  arityVASortFun :: a -> Int

instance VASortFun Sort where
  withSortVArgs k = k []
  arityVASortFun f = 0

instance VASortFun a => VASortFun (Sort -> a) where
  withSortVArgs k x = withSortVArgs (\xs -> k (x : xs))
  arityVASortFun f = arityVASortFun (f undefined) + 1

declareFSym :: Solver -> String -> [Sort] -> Sort -> IO FSym
declareFSym solver f xs y = do
  fdefs <- readIORef (smtFDefs solver)
  when (f `Map.member` fdefs) $ do
    error $ "function symbol " ++ f ++ " is already declared"
  fdef <-
    case (xs, y) of
      ([], Sort SSymBool []) -> do
        v <- SAT.newVar (smtSAT solver)
        return (FBoolVar v)
      ([], Sort SSymReal []) -> do
        v <- Simplex2.newVar (smtLRA solver)
        return (FLRAVar v)
      _ -> do
        v <- EUF.newFSym (smtEUF solver)
        return (FEUFFun (xs,y) v)
  fdefs <- readIORef (smtFDefs solver)
  when (f `Map.member` fdefs) $ error ("function " ++ show f ++ " is already defined")
  writeIORef (smtFDefs solver) $ Map.insert f fdef fdefs
  return f

class VAFun a where
  withVArgs :: ([Expr] -> Expr) -> a
  arityVAFun :: a -> Int

instance VAFun Expr where
  withVArgs k = k []
  arityVAFun _ = 0

instance VAFun a => VAFun (Expr -> a) where
  withVArgs k x = withVArgs (\xs -> k (x : xs))
  arityVAFun f = arityVAFun (f undefined) + 1

declareFun :: VAFun a => Solver -> String -> [Sort] -> Sort -> IO a
declareFun solver name ps r = do
  fsym <- declareFSym solver name ps r
  let f = withVArgs (EAp fsym)
  unless (arityVAFun f == length ps) $ error "ToySolver.SMT.declareFun: argument number error"
  return f

declareConst :: Solver -> String -> Sort -> IO Expr
declareConst solver name s = declareFun solver name [] s

assert :: Solver -> Expr -> IO ()
assert solver e = do
  formula <- exprToFormula solver e
  n <- Vec.getSize (smtContexts solver)
  if n>0 then do
    lit <- Vec.peek (smtContexts solver)
    Tseitin.addFormula (smtEnc solver) $ Atom lit .=>. formula
  else
    Tseitin.addFormula (smtEnc solver) formula

exprSort :: Solver -> Expr -> IO Sort
exprSort solver (EFrac _) = return (Sort SSymReal [])
exprSort solver (EAp f xs)
  | f `Set.member` Set.fromList ["true","false","and","or","not","=>","<=>","=",">=","<=",">","<"] = return (Sort SSymBool [])
  | f `Set.member` Set.fromList ["+", "-", "*"] = return (Sort SSymReal [])
  | f == "ite" = exprSort solver (xs !! 1)
  | otherwise = do
      fdefs <- readIORef (smtFDefs solver)
      case fdefs Map.! f of
        FBoolVar _ -> return (Sort SSymBool [])
        FLRAVar _ -> return (Sort SSymReal [])
        FEUFFun (_,s) _ -> return s

-- -------------------------------------------------------------------
                                              
exprToFormula :: Solver -> Expr -> IO Tseitin.Formula
exprToFormula solver (EAp "true" [])  = return true
exprToFormula solver (EAp "false" []) = return false
exprToFormula solver (EAp "and" xs) =
  liftM andB $ mapM (exprToFormula solver) xs
exprToFormula solver (EAp "or" xs) =
  liftM orB $ mapM (exprToFormula solver) xs
exprToFormula solver (EAp "not" [x]) =
  liftM notB $ exprToFormula solver x
exprToFormula solver (EAp "not" _) = undefined
exprToFormula solver (EAp "=>" [e1,e2]) = do
  b1 <- exprToFormula solver e1
  b2 <- exprToFormula solver e2
  return $ b1 .=>. b2
exprToFormula solver (EAp "<=>" [e1,e2]) = do
  b1 <- exprToFormula solver e1
  b2 <- exprToFormula solver e2
  return $ b1 .<=>. b2
exprToFormula solver (EAp "ite" [e1,e2,e3]) = do
  b1 <- exprToFormula solver e1
  b2 <- exprToFormula solver e2
  b3 <- exprToFormula solver e3
  return $ ite b1 b2 b3
exprToFormula solver (EAp "=" [e1,e2]) = do
  s <- exprSort solver e1
  case s of
    (Sort SSymBool _) -> do
      b1 <- exprToFormula solver e1
      b2 <- exprToFormula solver e2
      return $ b1 .<=>. b2
    (Sort SSymReal _) -> do
      e1' <- exprToLRAExpr solver e1
      e2' <- exprToLRAExpr solver e2
      liftM Atom $ abstractLRAAtom solver (e1' .==. e2')
    (Sort (SSymUserDefined _ _) _) -> do
      e1' <- exprToEUFArg solver e1
      e2' <- exprToEUFArg solver e2
      liftM Atom $ abstractEUFAtom solver (e1',e2')
exprToFormula solver (EAp "=" _) = undefined
exprToFormula solver (EAp ">=" [e1,e2]) = do
  e1' <- exprToLRAExpr solver e1
  e2' <- exprToLRAExpr solver e2
  liftM Atom $ abstractLRAAtom solver (e1' .>=. e2')
exprToFormula solver (EAp "<=" [e1,e2]) = do
  e1' <- exprToLRAExpr solver e1
  e2' <- exprToLRAExpr solver e2
  liftM Atom $ abstractLRAAtom solver (e1' .<=. e2')
exprToFormula solver (EAp ">" [e1,e2]) = do
  e1' <- exprToLRAExpr solver e1
  e2' <- exprToLRAExpr solver e2
  liftM Atom $ abstractLRAAtom solver (e1' .>. e2')
exprToFormula solver (EAp "<" [e1,e2]) = do
  e1' <- exprToLRAExpr solver e1
  e2' <- exprToLRAExpr solver e2
  liftM Atom $ abstractLRAAtom solver (e1' .<. e2')
exprToFormula solver (EAp f []) = do
  fdefs <- readIORef (smtFDefs solver)
  case Map.lookup f fdefs of
    Just (FBoolVar v) -> return (Atom v)
    Just _ -> error "non Bool constant appears in a boolean context"
    Nothing -> error "unknown constant"
exprToFormula solver (EAp f xs) = do
  e' <- exprToEUFTerm solver f xs
  formulaFromEUFTerm solver e'

-- -------------------------------------------------------------------

exprToLRAExpr :: Solver -> Expr -> IO (LA.Expr Rational)
exprToLRAExpr solver (EFrac r) = return (LA.constant r)
exprToLRAExpr solver (EAp "-" [x]) = liftM negateV $ exprToLRAExpr solver x
exprToLRAExpr solver (EAp "-" [x,y]) = liftM2 (^-^) (exprToLRAExpr solver x) (exprToLRAExpr solver y)
exprToLRAExpr solver (EAp "+" xs) = liftM sumV $ mapM (exprToLRAExpr solver) xs
exprToLRAExpr solver (EAp "*" xs) = liftM (foldr mult (LA.constant 1)) $ mapM (exprToLRAExpr solver) xs
  where
    mult e1 e2
      | Just c <- LA.asConst e1 = c *^ e2
      | Just c <- LA.asConst e2 = c *^ e1
      | otherwise = error "non-linear multiplication is not supported"
exprToLRAExpr solver (EAp "/" [x,y]) = do
  x' <- exprToLRAExpr solver x
  y' <- exprToLRAExpr solver y
  case LA.asConst y' of
    Nothing -> error "division by non-constant is not supported"
    Just c -> return $ (1/c) *^ x'
exprToLRAExpr solver (EAp f xs) = 
  lraExprFromTerm solver =<< exprToEUFTerm solver f xs

abstractLRAAtom :: Solver -> LA.Atom Rational -> IO SAT.Lit
abstractLRAAtom solver atom = do
  (v,op,rhs) <- Simplex2.simplifyAtom (smtLRA solver) atom
  (tbl,defs) <- readIORef (smtLRAAtomDefs solver)
  (vLt, vEq, vGt) <-
    case Map.lookup (v,rhs) tbl of
      Just (vLt, vEq, vGt) -> return (vLt, vEq, vGt)
      Nothing -> do
        vLt <- SAT.newVar (smtSAT solver)
        vEq <- SAT.newVar (smtSAT solver)
        vGt <- SAT.newVar (smtSAT solver)
        SAT.addClause (smtSAT solver) [vLt,vEq,vGt]
        SAT.addClause (smtSAT solver) [-vLt, -vEq]
        SAT.addClause (smtSAT solver) [-vLt, -vGt]                 
        SAT.addClause (smtSAT solver) [-vEq, -vGt]
        let xs = IntMap.fromList
                 [ (vEq,  LA.var v .==. LA.constant rhs)
                 , (vLt,  LA.var v .<.  LA.constant rhs)
                 , (vGt,  LA.var v .>.  LA.constant rhs)
                 , (-vLt, LA.var v .>=. LA.constant rhs)
                 , (-vGt, LA.var v .<=. LA.constant rhs)
                 ]
        writeIORef (smtLRAAtomDefs solver) (Map.insert (v,rhs) (vLt, vEq, vGt) tbl, IntMap.union xs defs)
        return (vLt, vEq, vGt)
  case op of
    Lt  -> return vLt
    Gt  -> return vGt
    Eql -> return vEq
    Le  -> return (-vGt)
    Ge  -> return (-vLt)
    NEq -> return (-vEq)


lraExprToEUFTerm :: Solver -> LA.Expr Rational -> IO EUF.Term
lraExprToEUFTerm solver e = do
  (realToFSym, fsymToReal) <- readIORef (smtRealTermDefs solver)
  case Map.lookup e realToFSym of
    Just c -> return (EUF.TApp c [])
    Nothing -> do
      c <- EUF.newFSym (smtEUF solver)
      forM_ (IntMap.toList fsymToReal) $ \(d, d_lra) -> do
        -- allocate interface equalities
        b1 <- abstractEUFAtom solver (EUF.TApp c [], EUF.TApp d [])
        b2 <- abstractLRAAtom solver (e .==. d_lra)
        Tseitin.addFormula (smtEnc solver) (Atom b1 .<=>. Atom b2)
      writeIORef (smtRealTermDefs solver) $
        ( Map.insert e c realToFSym
        , IntMap.insert c e fsymToReal
        )
      return (EUF.TApp c [])

lraExprFromTerm :: Solver -> EUF.Term -> IO (LA.Expr Rational)
lraExprFromTerm solver t = do
  (realToFSym, fsymToReal) <- readIORef (smtRealTermDefs solver)
  c <- EUF.termToFSym (smtEUF solver) t
  case IntMap.lookup c fsymToReal of
    Just e -> return e
    Nothing -> do
      v <- Simplex2.newVar (smtLRA solver)
      let e = LA.var v
      forM_ (IntMap.toList fsymToReal) $ \(d, d_lra) -> do
        -- allocate interface equalities
        b1 <- abstractEUFAtom solver (EUF.TApp c [], EUF.TApp d [])
        b2 <- abstractLRAAtom solver (e .==. d_lra)
        Tseitin.addFormula (smtEnc solver) (Atom b1 .<=>. Atom b2)
      writeIORef (smtRealTermDefs solver) $
        ( Map.insert e c realToFSym
        , IntMap.insert c e fsymToReal
        )
      return e

-- -------------------------------------------------------------------

exprToEUFTerm :: Solver -> FSym -> [Expr] -> IO EUF.Term
exprToEUFTerm solver f xs = do
  fdefs <- readIORef (smtFDefs solver)
  case Map.lookup f fdefs of
    Just (FBoolVar v) -> formulaToEUFTerm solver (Atom v)
    Just (FLRAVar v) -> lraExprToEUFTerm solver (LA.var v)
    Just (FEUFFun _ fsym) ->
      liftM (EUF.TApp fsym) $ mapM (exprToEUFArg solver) xs
    _ -> error ("hogehoge: " ++ show (f,xs))

exprToEUFArg :: Solver -> Expr -> IO EUF.Term
exprToEUFArg solver (EFrac r) = lraExprToEUFTerm solver (LA.constant r)
exprToEUFArg solver e@(EAp f xs) = do
  Sort s _ <- exprSort solver e
  case s of
    SSymBool -> formulaToEUFTerm solver =<< exprToFormula solver e
    SSymReal -> lraExprToEUFTerm solver =<< exprToLRAExpr solver e
    _ -> exprToEUFTerm solver f xs

abstractEUFAtom :: Solver -> (EUF.Term, EUF.Term) -> IO SAT.Lit
abstractEUFAtom solver (t1,t2) | t1 >= t2 = abstractEUFAtom solver (t2,t1)
abstractEUFAtom solver (t1,t2) = do
  (tbl,defs) <- readIORef (smtEUFAtomDefs solver)
  case Map.lookup (t1,t2) tbl of
    Just v -> return v
    Nothing -> do
      v <- SAT.newVar (smtSAT solver)
      writeIORef (smtEUFAtomDefs solver) (Map.insert (t1,t2) v tbl, IntMap.insert v (t1,t2) defs)
      return v

formulaToEUFTerm :: Solver -> Tseitin.Formula -> IO EUF.Term
formulaToEUFTerm solver formula = do
  lit <- Tseitin.encodeFormula (smtEnc solver) formula
  (_, boolToTerm) <- readIORef (smtBoolTermDefs solver)
  case IntMap.lookup lit boolToTerm of
    Just t -> return t
    Nothing -> do
      t <- EUF.newConst (smtEUF solver)
      connectBoolTerm solver lit t
      return t

formulaFromEUFTerm :: Solver -> EUF.Term -> IO Tseitin.Formula
formulaFromEUFTerm solver t = do
  (termToBool, _) <- readIORef (smtBoolTermDefs solver)
  case Map.lookup t termToBool of
    Just lit -> return (Atom lit)
    Nothing -> do
      lit <- SAT.newVar (smtSAT solver)
      connectBoolTerm solver lit t
      return $ Atom lit

connectBoolTerm :: Solver -> SAT.Lit -> EUF.Term -> IO ()
connectBoolTerm solver lit t = do
  lit1 <- abstractEUFAtom solver (t, smtEUFTrue solver)
  lit2 <- abstractEUFAtom solver (t, smtEUFFalse solver)
  SAT.addClause (smtSAT solver) [-lit, lit1]  --  lit  ->  lit1
  SAT.addClause (smtSAT solver) [-lit1, lit]  --  lit1 ->  lit
  SAT.addClause (smtSAT solver) [lit, lit2]   -- -lit  ->  lit2
  SAT.addClause (smtSAT solver) [-lit2, -lit] --  lit2 -> -lit
  modifyIORef (smtBoolTermDefs solver) $ \(termToBool, boolToTerm) ->
    ( Map.insert t lit termToBool
    , IntMap.insert lit t boolToTerm
    )

-- -------------------------------------------------------------------

checkSAT :: Solver -> IO Bool
checkSAT solver = do  
  l <- getContextLit solver
  SAT.solveWith (smtSAT solver) [l]

getContextLit :: Solver -> IO SAT.Lit
getContextLit solver = do
  n <- Vec.getSize (smtContexts solver)
  if n>0 then
    Vec.peek (smtContexts solver)
  else
    Tseitin.encodeConj (smtEnc solver) [] -- true

pushContext :: Solver -> IO ()
pushContext solver = do
  l1 <- getContextLit solver
  l2 <- SAT.newVar (smtSAT solver)
  SAT.addClause (smtSAT solver) [-l2, l1] -- l2 → l1
  Vec.push (smtContexts solver) l2

popContext :: Solver -> IO ()
popContext solver = do
  Vec.pop (smtContexts solver)
  return ()

-- -------------------------------------------------------------------

data Model
  = Model
  { mDefs      :: !(Map FSym FDef)
  , mBoolModel :: !SAT.Model
  , mLRAModel  :: !Simplex2.Model
  , mEUFModel  :: !EUF.Model
  , mEUFTrue   :: !EUF.Entity
  , mEUFFalse  :: !EUF.Entity
  , mEntityToRational :: !(IntMap Rational)
  , mRationalToEntity :: !(Map Rational EUF.Entity)
  }
  deriving (Show)

data Value
  = ValRational !Rational
  | ValBool !Bool
  | ValUninterpreted !Int
  deriving (Eq, Show)

getModel :: Solver -> IO Model
getModel solver = do
  defs <- readIORef (smtFDefs solver)
  boolModel <- SAT.getModel (smtSAT solver)
  lraModel <- Simplex2.getModel (smtLRA solver)
  eufModel <- readIORef (smtEUFModel solver)
  (_, fsymToReal) <- readIORef (smtRealTermDefs solver)
  let xs = [(e, LA.evalExpr lraModel lraExpr) | (fsym, lraExpr) <- IntMap.toList fsymToReal, let e = EUF.evalAp eufModel fsym [], e /= EUF.mUnspecified eufModel]
  return $
    Model
    { mDefs = defs
    , mBoolModel = boolModel
    , mLRAModel = lraModel
    , mEUFModel = eufModel
    , mEUFTrue  = EUF.eval eufModel (smtEUFTrue solver)
    , mEUFFalse = EUF.eval eufModel (smtEUFFalse solver)
    , mEntityToRational = IntMap.fromList xs
    , mRationalToEntity = Map.fromList [(r,e) | (e,r) <- xs]
    }

eval :: Model -> Expr -> Value
eval m (EFrac r) = ValRational r
eval m (EAp "true" [])   = ValBool True
eval m (EAp "false" [])  = ValBool False
eval m (EAp "ite" [a,b,c]) = if valToBool m (eval m a) then eval m b else eval m c
eval m (EAp "and" xs)    = ValBool $ and $ map (valToBool m . eval m) xs
eval m (EAp "or" xs)     = ValBool $ or $ map (valToBool m . eval m) xs
eval m (EAp "not" [x])   = ValBool $ not $ valToBool m $ eval m x
eval m (EAp "=>" [x,y])  = ValBool $ valToBool m (eval m x) .=>. valToBool m (eval m y)
eval m (EAp "<=>" [x,y]) = ValBool $ valToBool m (eval m x) .<=>. valToBool m (eval m y)
eval m (EAp "<=" [x,y])  = ValBool $ valToRational m (eval m x) <= valToRational m (eval m y)
eval m (EAp ">=" [x,y])  = ValBool $ valToRational m (eval m x) >= valToRational m (eval m y)
eval m (EAp ">" [x,y])   = ValBool $ valToRational m (eval m x) >  valToRational m (eval m y)
eval m (EAp "<" [x,y])   = ValBool $ valToRational m (eval m x) <  valToRational m (eval m y)
eval m (EAp "+" xs)      = ValRational $ sum $ map (valToRational m . eval m) xs
eval m (EAp "-" [x])     = ValRational $ negate $ valToRational m (eval m x)
eval m (EAp "-" [x,y])   = ValRational $ valToRational m (eval m x) - valToRational m (eval m y)
eval m (EAp "*" xs)      = ValRational $ product $ map (valToRational m . eval m) xs
eval m (EAp "/" [x,y])   = ValRational $ valToRational m (eval m x) / valToRational m (eval m y)
eval m (EAp "=" [x,y])   = ValBool $
  case (eval m x, eval m y) of
    (v1, v2) -> v1 == v2
eval m (EAp f xs) =
  case Map.lookup f (mDefs m) of
    Nothing -> error ("unknown symbol: " ++ show f)
    Just (FBoolVar v) -> ValBool $ SAT.evalLit (mBoolModel m) v
    Just (FLRAVar v) -> ValRational $ mLRAModel m IntMap.! v
    Just (FEUFFun (_, Sort s []) sym) ->
      let e = EUF.evalAp (mEUFModel m) sym (map (valToEntity m . eval m) xs)
      in case s of
           SSymUserDefined _ _ -> ValUninterpreted e
           SSymBool -> ValBool (e == mEUFTrue m)
           SSymReal ->
             case IntMap.lookup e (mEntityToRational m) of
               Just r -> ValRational r
               Nothing -> ValRational (fromIntegral (1000000 + e))

valToBool :: Model -> Value -> Bool
valToBool _ (ValBool b) = b
valToBool _ _ = error "boolean value is expected"

valToRational :: Model -> Value -> Rational
valToRational _ (ValRational r) = r
valToRational _ _ = error "rational value is expected"

valToEntity :: Model -> Value -> EUF.Entity
valToEntity _ (ValUninterpreted e) = e
valToEntity m (ValBool b)     = if b then mEUFTrue m else mEUFFalse m
valToEntity m (ValRational r) =
  case Map.lookup r (mRationalToEntity m) of
    Just e -> e
    Nothing -> EUF.mUnspecified (mEUFModel m)

-- -------------------------------------------------------------------

#if !MIN_VERSION_base(4,7,0)

isRight :: Either a b -> Bool
isRight (Left  _) = False
isRight (Right _) = True

#endif
