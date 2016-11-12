{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances, DeriveDataTypeable, CPP, OverloadedStrings #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.SMT
-- Copyright   :  (c) Masahiro Sakai 2015
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  unstable
-- Portability :  non-portable (MultiParamTypeClasses, FlexibleInstances, DeriveDataTypeable, CPP, OverloadedStrings)
--
-----------------------------------------------------------------------------
module ToySolver.SMT
  (
  -- * The Solver type
    Solver
  , newSolver
  , Exception (..)

  -- * Problem Specification
  , SSym (..)
  , ssymArity
  , Sort (..)
  , sBool
  , sReal
  , FunType
  , Expr (..)
  , exprSort
  , Index (..)
  , FSym (..)
  , declareSSym
  , declareSort
  , VASortFun
  , declareFSym
  , declareFun
  , declareConst
  , VAFun
  , assert
  , assertNamed
  , getGlobalDeclarations
  , setGlobalDeclarations

  -- * Solving
  , checkSAT
  , checkSATAssuming
  , push
  , pop

  -- * Inspecting models
  , Model
  , Value (..)
  , getModel
  , eval
  , valSort
  , FunDef (..)
  , evalFSym

  -- * Inspecting proofs
  , getUnsatAssumptions
  , getUnsatCore
  ) where

import Control.Applicative
import qualified Control.Exception as E
import Control.Monad
import Control.Monad.Trans
import Control.Monad.Trans.Except
import Data.Bits
import Data.Either
import Data.Interned (intern, unintern)
import Data.Interned.Text
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import Data.IORef
import Data.List
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe (catMaybes)
import Data.Monoid
import Data.Set (Set)
import qualified Data.Set as Set
import Data.String
import qualified Data.Text as T
import Data.Typeable
import Data.VectorSpace

import ToySolver.Data.Delta
import ToySolver.Data.Boolean
import ToySolver.Data.BoolExpr
import ToySolver.Data.OrdRel
import qualified ToySolver.Data.LA as LA
import qualified ToySolver.Internal.Data.Vec as Vec
import qualified ToySolver.SAT as SAT
import ToySolver.SAT.TheorySolver
import qualified ToySolver.SAT.Encoder.Tseitin as Tseitin
import qualified ToySolver.Arith.Simplex2 as Simplex2
import qualified ToySolver.BitVector as BV
import qualified ToySolver.EUF.EUFSolver as EUF

data Index
  = IndexNumeral !Integer
  | IndexSymbol !InternedText
  deriving (Show,Eq, Ord)

data FSym
  = FSym !InternedText [Index]
  deriving (Show,Eq,Ord)

instance IsString FSym where
  fromString s = FSym (fromString s) []

-- | Sort symbols
data SSym
  = SSymBool
  | SSymReal
  | SSymBitVec !Int
  | SSymUserDeclared String !Int
  deriving (Show, Eq, Ord)

ssymArity :: SSym -> Int
ssymArity SSymBool = 0
ssymArity SSymReal = 0
ssymArity (SSymBitVec _) = 0
ssymArity (SSymUserDeclared _ ar) = ar

data Sort = Sort SSym [Sort]
  deriving (Show, Eq, Ord)

sBool :: Sort
sBool = Sort SSymBool []

sReal :: Sort
sReal = Sort SSymReal []

sBitVec :: Int -> Sort
sBitVec n = Sort (SSymBitVec n) []

type FunType = ([Sort],Sort)

data Expr
  = EAp FSym [Expr]
  | EFrac Rational
  | EBitVec BV.BV
  deriving (Show, Eq, Ord)

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
  x .<=>. y = EAp "=" [x,y]

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
  | FBVVar BV.Var
  | FEUFFun FunType EUF.FSym
  deriving (Show)

data Exception
  = Error String
  | Unsupported
  deriving (Show, Typeable)

instance E.Exception Exception    

data Solver
  = Solver
  { smtSAT :: !SAT.Solver
  , smtEnc :: !(Tseitin.Encoder IO)
  , smtEUF :: !EUF.Solver
  , smtLRA :: !(Simplex2.GenericSolver (Delta Rational))
  , smtBV :: !BV.Solver

  , smtEUFAtomDefs  :: !(IORef (Map (EUF.Term, EUF.Term) SAT.Var, IntMap (EUF.Term, EUF.Term)))
  , smtLRAAtomDefs  :: !(IORef (Map (LA.Var, Rational) (SAT.Lit, SAT.Lit, SAT.Lit), IntMap (LA.Atom Rational)))
  , smtBVAtomDefs   :: !(IORef (Map BVAtomNormalized SAT.Var, IntMap BVAtomNormalized))
  , smtBoolTermDefs :: !(IORef (Map EUF.Term SAT.Lit, IntMap EUF.Term))
  , smtRealTermDefs :: !(IORef (Map (LA.Expr Rational) EUF.FSym, IntMap (LA.Expr Rational)))
  , smtBVTermDefs :: !(IORef (Map BV.Expr EUF.FSym, IntMap BV.Expr))
  , smtEUFTrue  :: !EUF.Term
  , smtEUFFalse :: !EUF.Term

  , smtEUFModel :: !(IORef EUF.Model)
  , smtLRAModel :: !(IORef Simplex2.Model)
  , smtBVModel :: !(IORef BV.Model)

  , smtGlobalDeclarationsRef :: !(IORef Bool)
  , smtFDefs :: !(IORef (Map FSym FDef))
  , smtNamedAssertions :: !(IORef (Map String SAT.Lit))
  , smtAssertionStack :: !(Vec.Vec AssertionLevel)

  , smtUnsatAssumptions :: !(IORef [Expr])
  , smtUnsatCore :: !(IORef [String])
  }

data AssertionLevel
  = AssertionLevel
  { alSavedNamedAssertions :: Map String SAT.Lit
  , alSavedFDefs :: Maybe (Map FSym FDef)
  , alSelector :: SAT.Lit
  }

data TheorySolverID
  = TheorySolverEUF
  | TheorySolverSimplex
  | TheorySolverBV
  deriving (Eq, Ord, Enum, Bounded)

newSolver :: IO Solver
newSolver = do
  sat <- SAT.newSolver
  enc <- Tseitin.newEncoder sat
  euf <- EUF.newSolver
  lra <- Simplex2.newSolver
  bv <- BV.newSolver

  litTrue <- Tseitin.encodeConj enc []
  let litFalse = -litTrue

  eufTrue  <- EUF.newConst euf
  eufFalse <- EUF.newConst euf
  EUF.assertNotEqual euf eufTrue eufFalse
  divByZero <- EUF.newFSym euf

  eufAtomDefs <- newIORef (Map.empty, IntMap.empty)
  lraAtomDefs <- newIORef (Map.empty, IntMap.empty)
  bvAtomDefs <- newIORef (Map.empty, IntMap.empty)
  boolTermDefs <- newIORef $
    ( Map.fromList [(eufTrue, litTrue), (eufFalse, litFalse)]
    , IntMap.fromList [(litTrue, eufTrue), (litFalse, eufFalse)]
    )
  realTermDefs <- newIORef (Map.empty, IntMap.empty)
  bvTermDefs <- newIORef (Map.empty, IntMap.empty)

  eufModelRef <- newIORef (undefined :: EUF.Model)
  lraModelRef <- newIORef (undefined :: Simplex2.Model)
  bvModelRef <- newIORef (undefined :: BV.Model)

  globalDeclarationsRef <- newIORef False
  fdefs <- newIORef $ Map.singleton "_/0" (FEUFFun ([sReal], sReal) divByZero)

  conflictTheory <- newIORef undefined

  let tsolver =
        TheorySolver
        { thAssertLit = \_ l -> liftM (either id id) $ runExceptT $ do
            (_, defsLRA) <- lift $ readIORef lraAtomDefs
            case IntMap.lookup l defsLRA of
              Nothing -> return ()
              Just atom -> do
                lift $ Simplex2.assertAtomEx' lra atom (Just l)
                throwE True

            (_, defsEUF) <- lift $ readIORef eufAtomDefs
            case IntMap.lookup (SAT.litVar l) defsEUF of
              Nothing -> return ()
              Just (t1,t2) -> do
                if SAT.litPolarity l then do
                  lift $ EUF.assertEqual' euf t1 t2 (Just l)
                else do
                  lift $ EUF.assertNotEqual' euf t1 t2 (Just l)
                throwE True

            (_, defsBV) <- lift $ readIORef bvAtomDefs
            case IntMap.lookup (SAT.litVar l) defsBV of
              Nothing -> return ()
              Just atom -> do
                lift $ BV.assertAtom bv (unnormalizeBVAtom (atom, SAT.litPolarity l)) (Just l)
                throwE True

            return True

        , thCheck = \callback -> liftM isRight $ runExceptT $ do
            do b <- lift $ Simplex2.check lra
               unless b $ do
                 lift $ writeIORef conflictTheory TheorySolverSimplex
                 throwE ()
            do b <- lift $ EUF.check euf
               unless b $ do
                 lift $ writeIORef conflictTheory TheorySolverEUF
                 throwE ()
               (_, defsEUF) <- lift $ readIORef eufAtomDefs
               forM_ (IntMap.toList defsEUF) $ \(v, (t1, t2)) -> do
                  b2 <- lift $ EUF.areEqual euf t1 t2
                  when b2 $ do
                    b3 <- lift $ callback v
                    unless b3 $ throwE ()
            do b <- lift $ BV.check bv
               unless b $ do
                 lift $ writeIORef conflictTheory TheorySolverBV
                 throwE ()

        , thExplain = \m -> do
            case m of
              Nothing -> do
                t <- readIORef conflictTheory
                case t of
                  TheorySolverSimplex -> liftM IntSet.toList $ Simplex2.explain lra
                  TheorySolverBV -> liftM IntSet.toList $ BV.explain bv
                  TheorySolverEUF -> liftM IntSet.toList $ EUF.explain euf Nothing
              Just v -> do
                (_, defsEUF) <- readIORef eufAtomDefs
                case IntMap.lookup v defsEUF of
                  Nothing -> error "should not happen"
                  Just (t1,t2) -> liftM IntSet.toList $ EUF.explain euf (Just (t1,t2))

        , thPushBacktrackPoint = do
            Simplex2.pushBacktrackPoint lra
            EUF.pushBacktrackPoint euf
            BV.pushBacktrackPoint bv
        , thPopBacktrackPoint = do
            Simplex2.popBacktrackPoint lra
            EUF.popBacktrackPoint euf
            BV.popBacktrackPoint bv
        , thConstructModel = do
            writeIORef eufModelRef =<< EUF.getModel euf
            -- We need to call Simplex2.getModel here.
            -- Because backtracking removes constraints that are necessary
            -- for computing the value of delta.
            writeIORef lraModelRef =<< Simplex2.getModel lra
            writeIORef bvModelRef =<< BV.getModel bv
            return ()
        }
  SAT.setTheory sat tsolver

  named <- newIORef Map.empty

  stack <- Vec.new

  unsatAssumptionsRef <- newIORef undefined
  unsatCoreRef <- newIORef undefined

  return $
    Solver
    { smtSAT = sat
    , smtEnc = enc
    , smtEUF = euf
    , smtLRA = lra
    , smtBV  = bv

    , smtEUFAtomDefs = eufAtomDefs
    , smtLRAAtomDefs = lraAtomDefs
    , smtBVAtomDefs = bvAtomDefs
    , smtBoolTermDefs = boolTermDefs
    , smtRealTermDefs = realTermDefs
    , smtBVTermDefs = bvTermDefs
    , smtEUFTrue  = eufTrue
    , smtEUFFalse = eufFalse

    , smtEUFModel = eufModelRef
    , smtLRAModel = lraModelRef
    , smtBVModel = bvModelRef

    , smtGlobalDeclarationsRef = globalDeclarationsRef
    , smtFDefs = fdefs
    , smtNamedAssertions = named
    , smtAssertionStack = stack

    , smtUnsatAssumptions = unsatAssumptionsRef
    , smtUnsatCore = unsatCoreRef
    }

declareSSym :: Solver -> String -> Int -> IO SSym
declareSSym solver name arity = return (SSymUserDeclared name arity)

declareSort :: VASortFun a => Solver -> String -> Int -> IO a
declareSort solver name arity = do
  ssym <- declareSSym solver name arity
  let f = withSortVArgs (Sort ssym)
  unless (arityVASortFun f == arity) $ do
    E.throwIO $ Error "ToySolver.SMT.declareSort: argument number error"
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
declareFSym solver f' xs y = do
  let f = FSym (intern (T.pack f')) []
  fdefs <- readIORef (smtFDefs solver)
  when (f `Map.member` fdefs) $ do
    E.throwIO $ Error $ "function symbol " ++ f' ++ " is already used"
  fdef <-
    case (xs, y) of
      ([], Sort SSymBool []) -> do
        v <- SAT.newVar (smtSAT solver)
        return (FBoolVar v)
      ([], Sort SSymReal []) -> do
        v <- Simplex2.newVar (smtLRA solver)
        return (FLRAVar v)
      ([], Sort (SSymBitVec n) []) -> do
        BV.EVar v <- BV.newVar (smtBV solver) n -- XXX
        return (FBVVar v)
      _ -> do
        v <- EUF.newFSym (smtEUF solver)
        return (FEUFFun (xs,y) v)
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
  unless (arityVAFun f == length ps) $ do
    E.throwIO $ Error "ToySolver.SMT.declareFun: argument number error"
  return f

declareConst :: Solver -> String -> Sort -> IO Expr
declareConst solver name s = declareFun solver name [] s

assert :: Solver -> Expr -> IO ()
assert solver e = do
  formula <- exprToFormula solver e
  n <- Vec.getSize (smtAssertionStack solver)
  if n>0 then do
    assertionLevel <- Vec.peek (smtAssertionStack solver)
    Tseitin.addFormula (smtEnc solver) $ Atom (alSelector assertionLevel) .=>. formula
  else
    Tseitin.addFormula (smtEnc solver) formula

assertNamed :: Solver -> String -> Expr -> IO ()
assertNamed solver name e = do
  lit <- Tseitin.encodeFormula (smtEnc solver) =<< exprToFormula solver e
  modifyIORef (smtNamedAssertions solver) (Map.insert name lit)

getGlobalDeclarations :: Solver -> IO Bool
getGlobalDeclarations solver = readIORef (smtGlobalDeclarationsRef solver)

setGlobalDeclarations :: Solver -> Bool -> IO ()
setGlobalDeclarations solver = writeIORef (smtGlobalDeclarationsRef solver)

exprSort :: Solver -> Expr -> IO Sort
exprSort solver e = do
  fdefs <- readIORef (smtFDefs solver)
  return $! exprSort' fdefs e

exprSort' :: Map FSym FDef -> Expr -> Sort
exprSort' _fdefs (EFrac _) = Sort SSymReal []
exprSort' _fdefs (EBitVec bv) = Sort (SSymBitVec (BV.width bv)) []
exprSort' fdefs (EAp f xs)
  | f `Set.member` Set.fromList ["true","false","and","or","xor","not","=>","=",">=","<=",">","<"] = Sort SSymBool []
  | f `Set.member` Set.fromList ["bvule", "bvult", "bvuge", "bvugt", "bvsle", "bvslt", "bvsge", "bvsgt"] = Sort SSymBool []
  | f `Set.member` Set.fromList ["+", "-", "*", "/"] = Sort SSymReal []
  | FSym "extract" [IndexNumeral i, IndexNumeral j] <- f = Sort (SSymBitVec (fromIntegral (i - j + 1))) []
  | f == "concat" =
      case (exprSort' fdefs (xs !! 0), exprSort' fdefs (xs !! 1)) of
        (Sort (SSymBitVec m) [], Sort (SSymBitVec n) []) -> Sort (SSymBitVec (m+n)) []
        _ -> undefined
  | FSym "repeat" [IndexNumeral i] <- f =
      case exprSort' fdefs (xs !! 0) of
        Sort (SSymBitVec m) [] -> Sort (SSymBitVec (m * fromIntegral i)) []
        _ -> undefined
  | FSym name [IndexNumeral i] <- f, name == "zero_extend" || name == "sign_extend" =
      case exprSort' fdefs (xs !! 0) of
        Sort (SSymBitVec m) [] -> Sort (SSymBitVec (m + fromIntegral i)) []
        _ -> undefined
  | FSym name [IndexNumeral i] <- f, name == "rotate_left" || name == "rotate_right" =
      exprSort' fdefs (xs !! 0)
  | f == "bvnot" || f == "bvneg" = exprSort' fdefs (xs !! 0)
  | f == "bvcomp" = Sort (SSymBitVec 1) []
  | f `Set.member` Set.fromList [name | (name, op) <- bvBinOpsSameSize] =
      exprSort' fdefs (xs !! 0)
  | f == "ite" = exprSort' fdefs (xs !! 1)
  | otherwise =
      case Map.lookup f fdefs of
        Nothing -> error $ show f ++ " was not found"
        Just fdef ->
          case fdef of
            FBoolVar _ -> Sort SSymBool []
            FLRAVar _ -> Sort SSymReal []
            FBVVar v -> Sort (SSymBitVec (BV.width (BV.EVar v))) [] -- XXX
            FEUFFun (_,s) _ -> s

-- -------------------------------------------------------------------
                                              
exprToFormula :: Solver -> Expr -> IO Tseitin.Formula
exprToFormula solver (EAp "true" [])  = return true
exprToFormula solver (EAp "false" []) = return false
exprToFormula solver (EAp "and" xs) =
  liftM andB $ mapM (exprToFormula solver) xs
exprToFormula solver (EAp "or" xs) =
  liftM orB $ mapM (exprToFormula solver) xs
exprToFormula solver (EAp "xor" xs) = do
  ys <- mapM (exprToFormula solver) xs
  return $ foldr (\a b -> notB (a .<=>. b)) false ys
exprToFormula solver (EAp "not" [x]) =
  liftM notB $ exprToFormula solver x
exprToFormula solver (EAp "not" _) = undefined
exprToFormula solver (EAp "=>" [e1,e2]) = do
  b1 <- exprToFormula solver e1
  b2 <- exprToFormula solver e2
  return $ b1 .=>. b2
exprToFormula solver (EAp "ite" [e1,e2,e3]) = do
  b1 <- exprToFormula solver e1
  b2 <- exprToFormula solver e2
  b3 <- exprToFormula solver e3
  return $ ite b1 b2 b3
exprToFormula solver (EAp "=" []) = return true -- ???
exprToFormula solver (EAp "=" xs) =
  chain solver (abstractEq solver) xs
exprToFormula solver (EAp "distinct" []) = return true -- ???
exprToFormula solver (EAp "distinct" xs) =
  pairwise solver (\e1 e2 -> liftM notB (abstractEq solver e1 e2)) xs
exprToFormula solver (EAp ">=" xs) = do
  let f e1 e2 = do
        e1' <- exprToLRAExpr solver e1
        e2' <- exprToLRAExpr solver e2
        liftM Atom $ abstractLRAAtom solver (e1' .>=. e2')
  chain solver f xs
exprToFormula solver (EAp "<=" xs) = do
    let f e1 e2 = do
          e1' <- exprToLRAExpr solver e1
          e2' <- exprToLRAExpr solver e2
          liftM Atom $ abstractLRAAtom solver (e1' .<=. e2')
    chain solver f xs
exprToFormula solver (EAp ">" xs) = do
  let f e1 e2 = do
        e1' <- exprToLRAExpr solver e1
        e2' <- exprToLRAExpr solver e2
        liftM Atom $ abstractLRAAtom solver (e1' .>. e2')
  chain solver f xs
exprToFormula solver (EAp "<" xs) = do
  let f e1 e2 = do
        e1' <- exprToLRAExpr solver e1
        e2' <- exprToLRAExpr solver e2
        liftM Atom $ abstractLRAAtom solver (e1' .<. e2')
  chain solver f xs
exprToFormula solver (EAp f []) = do
  fdefs <- readIORef (smtFDefs solver)
  case Map.lookup f fdefs of
    Just (FBoolVar v) -> return (Atom v)
    Just _ -> E.throwIO $ Error "non Bool constant appears in a boolean context"
    Nothing -> E.throwIO $ Error $ "unknown function symbol: " ++ show f
exprToFormula solver (EAp op [e1,e2]) | Just f <- Map.lookup op table = do
  e1' <- exprToBVExpr solver e1
  e2' <- exprToBVExpr solver e2
  liftM Atom $ abstractBVAtom solver (f e1' e2')
  where
    table = Map.fromList
      [ ("bvule", BV.bvule)
      , ("bvult", BV.bvult)
      , ("bvuge", BV.bvuge)
      , ("bvugt", BV.bvugt)
      , ("bvsle", BV.bvsle)
      , ("bvslt", BV.bvslt)
      , ("bvsge", BV.bvsge)
      , ("bvsgt", BV.bvsgt)
      ]
exprToFormula solver (EAp f xs) = do
  e' <- exprToEUFTerm solver f xs
  formulaFromEUFTerm solver e'

chain :: Solver -> (Expr -> Expr -> IO Tseitin.Formula) -> [Expr] -> IO Tseitin.Formula
chain _ _ [] = return true
chain solver p xs = liftM andB $ mapM (uncurry p) (zip xs (tail xs))

pairwise :: Solver -> (Expr -> Expr -> IO Tseitin.Formula) -> [Expr] -> IO Tseitin.Formula
pairwise _ _ [] = return true
pairwise solver p xs = liftM andB $ mapM (uncurry p) (pairs xs)

abstractEq :: Solver -> Expr -> Expr -> IO Tseitin.Formula
abstractEq solver e1 e2 = do
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
    (Sort (SSymBitVec _) _) -> do
      e1' <- exprToBVExpr solver e1
      e2' <- exprToBVExpr solver e2
      liftM Atom $ abstractBVAtom solver (e1' .==. e2')
    (Sort (SSymUserDeclared _ _) _) -> do
      e1' <- exprToEUFArg solver e1
      e2' <- exprToEUFArg solver e2
      liftM Atom $ abstractEUFAtom solver (e1',e2')

-- -------------------------------------------------------------------

exprToLRAExpr :: Solver -> Expr -> IO (LA.Expr Rational)
exprToLRAExpr solver (EFrac r) = return (LA.constant r)
exprToLRAExpr solver (EAp "-" []) = E.throwIO $ Error "ToySolver.SMT: nullary '-' function"
exprToLRAExpr solver (EAp "-" [x]) = liftM negateV $ exprToLRAExpr solver x
exprToLRAExpr solver (EAp "-" (x:xs)) = do
  x' <- exprToLRAExpr solver x
  xs' <- mapM (exprToLRAExpr solver) xs
  return $ foldl' (^-^) x' xs'
exprToLRAExpr solver (EAp "+" xs) = liftM sumV $ mapM (exprToLRAExpr solver) xs
exprToLRAExpr solver (EAp "*" xs) = liftM (foldr mult (LA.constant 1)) $ mapM (exprToLRAExpr solver) xs
  where
    mult e1 e2
      | Just c <- LA.asConst e1 = c *^ e2
      | Just c <- LA.asConst e2 = c *^ e1
      | otherwise = E.throw $ Error "non-linear multiplication is not supported"
exprToLRAExpr solver (EAp "/" [x,y]) = do
  y' <- exprToLRAExpr solver y
  case LA.asConst y' of
    Nothing -> E.throwIO $ Error "division by non-constant is not supported"
    Just 0 -> do
      lraExprFromTerm solver =<< exprToEUFTerm solver "_/0" [x]
    Just c -> do
      x' <- exprToLRAExpr solver x
      return $ (1/c) *^ x'
exprToLRAExpr solver (EAp "ite" [c,t,e]) = do
  c' <- exprToFormula solver c
  ret <- liftM LA.var $ Simplex2.newVar (smtLRA solver)
  t' <- exprToLRAExpr solver t
  e' <- exprToLRAExpr solver e
  c1 <- abstractLRAAtom solver (ret .==. t')
  c2 <- abstractLRAAtom solver (ret .==. e')
  Tseitin.addFormula (smtEnc solver) $ ite c' (Atom c1) (Atom c2)
  return ret
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

bvBinOpsSameSize :: IsString s => [(s, BV.Op2)]
bvBinOpsSameSize =
  [ ("bvand", BV.OpAnd)
  , ("bvor", BV.OpOr)
  , ("bvxor", BV.OpXOr)
  , ("bvnand", BV.OpNAnd)
  , ("bvnor", BV.OpNOr)
  , ("bvxnor", BV.OpXNOr)
  , ("bvadd", BV.OpAdd)
  , ("bvsub", BV.OpSub)
  , ("bvmul", BV.OpMul)
  , ("bvudiv", BV.OpUDiv)
  , ("bvurem", BV.OpURem)
  , ("bvsdiv", BV.OpSDiv)
  , ("bvsrem", BV.OpSRem)
  , ("bvsmod", BV.OpSMod)
  , ("bvshl", BV.OpShl)
  , ("bvlshr", BV.OpLShr)
  , ("bvashr", BV.OpAShr)
  ]

exprToBVExpr :: Solver -> Expr -> IO BV.Expr
exprToBVExpr solver (EBitVec bv) = return $ BV.fromBV bv
exprToBVExpr solver (EAp "concat" [x,y]) = do
  liftM2 (<>) (exprToBVExpr solver x) (exprToBVExpr solver y)
exprToBVExpr solver (EAp (FSym "extract" [IndexNumeral i, IndexNumeral j]) [x]) = do
  BV.extract (fromIntegral i) (fromIntegral j) <$> exprToBVExpr solver x
exprToBVExpr solver (EAp (FSym "repeat" [IndexNumeral i]) [x]) = do
  BV.repeat (fromIntegral i) <$> exprToBVExpr solver x
exprToBVExpr solver (EAp (FSym "zero_extend" [IndexNumeral i]) [x]) = do
  BV.zeroExtend (fromIntegral i) <$> exprToBVExpr solver x
exprToBVExpr solver (EAp (FSym "sign_extend" [IndexNumeral i]) [x]) = do
  BV.signExtend (fromIntegral i) <$> exprToBVExpr solver x
exprToBVExpr solver (EAp (FSym "rotate_left" [IndexNumeral i]) [x]) = do
  rotateL <$> exprToBVExpr solver x <*> pure (fromIntegral i)
exprToBVExpr solver (EAp (FSym "rotate_right" [IndexNumeral i]) [x]) = do
  rotateR <$> exprToBVExpr solver x <*> pure (fromIntegral i)
exprToBVExpr solver (EAp (FSym op1 []) [x])
  | Just op1' <- Map.lookup op1 table = BV.EOp1 op1' <$> exprToBVExpr solver x
  where
    table =
      Map.fromList
      [ ("bvnot", BV.OpNot)
      , ("bvneg", BV.OpNeg)
      ]
exprToBVExpr solver (EAp (FSym op2 []) [x,y])
  | Just op2' <- Map.lookup op2 table = liftM2 (BV.EOp2 op2') (exprToBVExpr solver x) (exprToBVExpr solver y)
  where
    table = Map.fromList $ [("bvcomp", BV.OpComp)] ++ bvBinOpsSameSize
exprToBVExpr solver (EAp "ite" [c,t,e]) = do
  c' <- exprToFormula solver c
  t' <- exprToBVExpr solver t
  e' <- exprToBVExpr solver e
  ret <- BV.newVar (smtBV solver) (BV.width t')
  c1 <- abstractBVAtom solver (ret .==. t')
  c2 <- abstractBVAtom solver (ret .==. e')
  Tseitin.addFormula (smtEnc solver) $ ite c' (Atom c1) (Atom c2)
  return ret
exprToBVExpr solver e@(EAp f xs) = do
  s <- exprSort solver e
  case s of
    Sort (SSymBitVec w) [] -> do
      t <- exprToEUFTerm solver f xs
      bvExprFromTerm solver t w
    _ -> error "should not happen"

data BVAtomNormalized
  = BVEql BV.Expr BV.Expr
  | BVULt BV.Expr BV.Expr
  | BVSLt BV.Expr BV.Expr
  deriving (Eq, Ord)

normalizeBVAtom :: BV.Atom -> (BVAtomNormalized, Bool)
normalizeBVAtom (BV.Rel (OrdRel lhs op rhs) False) =
  case op of
    Lt  -> (BVULt lhs rhs, True)
    Gt  -> (BVULt rhs lhs, True)
    Eql -> (BVEql lhs rhs, True)
    NEq -> (BVEql lhs rhs, False)
    Le  -> (BVULt rhs lhs, False)
    Ge  -> (BVULt lhs rhs, False)
normalizeBVAtom (BV.Rel (OrdRel lhs op rhs) True) =
  case op of
    Lt  -> (BVSLt lhs rhs, True)
    Gt  -> (BVSLt rhs lhs, True)
    Eql -> (BVEql lhs rhs, True)
    NEq -> (BVEql lhs rhs, False)
    Le  -> (BVSLt rhs lhs, False)
    Ge  -> (BVSLt lhs rhs, False)

unnormalizeBVAtom :: (BVAtomNormalized, Bool) -> BV.Atom
unnormalizeBVAtom (BVEql lhs rhs, p) = (if p then id else notB) $ BV.Rel (OrdRel lhs Eql rhs) False
unnormalizeBVAtom (BVULt lhs rhs, p) = (if p then id else notB) $ BV.Rel (OrdRel lhs Lt rhs) False
unnormalizeBVAtom (BVSLt lhs rhs, p) = (if p then id else notB) $ BV.Rel (OrdRel lhs Lt rhs) True

abstractBVAtom :: Solver -> BV.Atom -> IO SAT.Lit
abstractBVAtom solver atom = do
  let (atom', s) = normalizeBVAtom atom
  (tbl,defs) <- readIORef (smtBVAtomDefs solver)
  v <- case Map.lookup atom' tbl of
         Just v -> return v
         Nothing -> do
           v <- SAT.newVar (smtSAT solver)
           writeIORef (smtBVAtomDefs solver) (Map.insert atom' v tbl, IntMap.insert v atom' defs)
           return v
  return $ if s then v else -v

bvExprToEUFTerm :: Solver -> BV.Expr -> IO EUF.Term
bvExprToEUFTerm solver e = do
  (bvToFSym, fsymToBV) <- readIORef (smtBVTermDefs solver)
  case Map.lookup e bvToFSym of
    Just c -> return (EUF.TApp c [])
    Nothing -> do
      c <- EUF.newFSym (smtEUF solver)
      let w1 = BV.width e
      forM_ (IntMap.toList fsymToBV) $ \(d, d_bv) -> do
        let w2 = BV.width d_bv
        when (w1 == w2) $ do
          -- allocate interface equalities
          b1 <- abstractEUFAtom solver (EUF.TApp c [], EUF.TApp d [])
          b2 <- abstractBVAtom solver (e .==. d_bv)
          Tseitin.addFormula (smtEnc solver) (Atom b1 .<=>. Atom b2)
      writeIORef (smtBVTermDefs solver) $
        ( Map.insert e c bvToFSym
        , IntMap.insert c e fsymToBV
        )
      return (EUF.TApp c [])

bvExprFromTerm :: Solver -> EUF.Term -> Int -> IO BV.Expr
bvExprFromTerm solver t w = do
  (bvToFSym, fsymToBV) <- readIORef (smtBVTermDefs solver)
  c <- EUF.termToFSym (smtEUF solver) t
  case IntMap.lookup c fsymToBV of
    Just e -> return e
    Nothing -> do
      e <- BV.newVar (smtBV solver) w
      forM_ (IntMap.toList fsymToBV) $ \(d, d_bv) -> do
        let w2 = BV.width d_bv
        when (w == w2) $ do
          -- allocate interface equalities
          b1 <- abstractEUFAtom solver (EUF.TApp c [], EUF.TApp d [])
          b2 <- abstractBVAtom solver (e .==. d_bv)
          Tseitin.addFormula (smtEnc solver) (Atom b1 .<=>. Atom b2)
      writeIORef (smtBVTermDefs solver) $
        ( Map.insert e c bvToFSym
        , IntMap.insert c e fsymToBV
        )
      return e

-- -------------------------------------------------------------------

exprToEUFTerm :: Solver -> FSym -> [Expr] -> IO EUF.Term
exprToEUFTerm solver "ite" [c,t,e] = do
  c' <- exprToFormula solver c
  ret <- EUF.newConst (smtEUF solver)
  t' <- exprToEUFArg solver t
  e' <- exprToEUFArg solver e
  c1 <- abstractEUFAtom solver (ret, t')
  c2 <- abstractEUFAtom solver (ret, e')
  Tseitin.addFormula (smtEnc solver) $ ite c' (Atom c1) (Atom c2)
  return ret
exprToEUFTerm solver f xs = do
  fdefs <- readIORef (smtFDefs solver)
  case Map.lookup f fdefs of
    Just (FBoolVar v) -> formulaToEUFTerm solver (Atom v)
    Just (FLRAVar v) -> lraExprToEUFTerm solver (LA.var v)
    Just (FBVVar v) -> bvExprToEUFTerm solver (BV.EVar v)
    Just (FEUFFun (ps,_) fsym) -> do
      unless (length ps == length xs) $ do
        E.throwIO $ Error "argument number error"
      liftM (EUF.TApp fsym) $ mapM (exprToEUFArg solver) xs
    _ -> E.throw $ Error $ "unknown function symbol: " ++ show f

exprToEUFArg :: Solver -> Expr -> IO EUF.Term
exprToEUFArg solver (EFrac r) = lraExprToEUFTerm solver (LA.constant r)
exprToEUFArg solver e@(EAp f xs) = do
  Sort s _ <- exprSort solver e
  case s of
    SSymBool -> formulaToEUFTerm solver =<< exprToFormula solver e
    SSymReal -> lraExprToEUFTerm solver =<< exprToLRAExpr solver e
    SSymBitVec _ -> bvExprToEUFTerm solver =<< exprToBVExpr solver e
    _ -> exprToEUFTerm solver f xs

abstractEUFAtom :: Solver -> (EUF.Term, EUF.Term) -> IO SAT.Lit
abstractEUFAtom solver (t1,t2) | t1 > t2 = abstractEUFAtom solver (t2,t1)
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
checkSAT solver = checkSATAssuming solver []

checkSATAssuming :: Solver -> [Expr] -> IO Bool
checkSATAssuming solver xs = do
  l <- getContextLit solver
  named <- readIORef (smtNamedAssertions solver) 

  ref <- newIORef IntMap.empty
  ls <- forM xs $ \x -> do
    b <- Tseitin.encodeFormula (smtEnc solver) =<< exprToFormula solver x
    modifyIORef ref (IntMap.insert b x)
    return b

  ret <- SAT.solveWith (smtSAT solver) (l : ls ++ Map.elems named)
  if ret then do
    writeIORef (smtUnsatAssumptions solver) undefined
    writeIORef (smtUnsatCore solver) undefined
  else do
    m1 <- readIORef ref
    let m2 = IntMap.fromList [(lit, name) | (name, lit) <- Map.toList named]
    failed <- SAT.getFailedAssumptions (smtSAT solver)
    writeIORef (smtUnsatAssumptions solver) $ catMaybes [IntMap.lookup l m1 | l <- failed]
    writeIORef (smtUnsatCore solver) $ catMaybes [IntMap.lookup l m2 | l <- failed]
  return ret

getContextLit :: Solver -> IO SAT.Lit
getContextLit solver = do
  n <- Vec.getSize (smtAssertionStack solver)
  if n>0 then do
    assertionLevel <- Vec.peek (smtAssertionStack solver)
    return $ alSelector assertionLevel
  else
    Tseitin.encodeConj (smtEnc solver) [] -- true

push :: Solver -> IO ()
push solver = do
  l1 <- getContextLit solver
  l2 <- SAT.newVar (smtSAT solver)
  SAT.addClause (smtSAT solver) [-l2, l1] -- l2 → l1
  globalDeclarations <- readIORef (smtGlobalDeclarationsRef solver)
  named <- readIORef (smtNamedAssertions solver)
  fdefs <- readIORef (smtFDefs solver)
  let newLevel =
        AssertionLevel
        { alSavedNamedAssertions = named
        , alSavedFDefs = if globalDeclarations then Nothing else Just fdefs
        , alSelector = l2
        }  
  Vec.push (smtAssertionStack solver) newLevel

pop :: Solver -> IO ()
pop solver = do
  n <- Vec.getSize (smtAssertionStack solver)
  if n==0 then
    E.throwIO $ Error $ "cannot pop first assertion level"
  else do
    assertionLevel <- Vec.unsafePop (smtAssertionStack solver)
    SAT.addClause (smtSAT solver) [- alSelector assertionLevel]
    writeIORef (smtNamedAssertions solver) (alSavedNamedAssertions assertionLevel)
    case alSavedFDefs assertionLevel of
      Nothing -> return ()
      Just fdefs -> writeIORef (smtFDefs solver) fdefs
    return ()

-- -------------------------------------------------------------------

data Model
  = Model
  { mDefs      :: !(Map FSym FDef)
  , mBoolModel :: !SAT.Model
  , mLRAModel  :: !Simplex2.Model
  , mBVModel   :: !BV.Model
  , mEUFModel  :: !EUF.Model
  , mEUFTrue   :: !EUF.Entity
  , mEUFFalse  :: !EUF.Entity
  , mEntityToRational :: !(IntMap Rational)
  , mRationalToEntity :: !(Map Rational EUF.Entity)
  , mEntityToBitVec :: !(IntMap BV.BV)
  , mBitVecToEntity :: !(Map BV.BV EUF.Entity)
  }
  deriving (Show)

data Value
  = ValRational !Rational
  | ValBitVec !BV.BV
  | ValBool !Bool
  | ValUninterpreted !Int !Sort
  deriving (Eq, Show)

getModel :: Solver -> IO Model
getModel solver = do
  defs <- readIORef (smtFDefs solver)
  boolModel <- SAT.getModel (smtSAT solver)
  lraModel <- readIORef (smtLRAModel solver)
  bvModel  <- readIORef (smtBVModel solver)
  eufModel <- readIORef (smtEUFModel solver)

  (_, fsymToReal) <- readIORef (smtRealTermDefs solver)
  let xs = [(e, LA.eval lraModel lraExpr) | (fsym, lraExpr) <- IntMap.toList fsymToReal, let e = EUF.evalAp eufModel fsym [], e /= EUF.mUnspecified eufModel]

  (_, fsymToBV) <- readIORef (smtBVTermDefs solver)
  let ys = [(e, BV.evalExpr bvModel bvExpr) | (fsym, bvExpr) <- IntMap.toList fsymToBV, let e = EUF.evalAp eufModel fsym [], e /= EUF.mUnspecified eufModel]

  return $
    Model
    { mDefs = defs
    , mBoolModel = boolModel
    , mLRAModel = lraModel
    , mBVModel  = bvModel
    , mEUFModel = eufModel
    , mEUFTrue  = EUF.eval eufModel (smtEUFTrue solver)
    , mEUFFalse = EUF.eval eufModel (smtEUFFalse solver)
    , mEntityToRational = IntMap.fromList xs
    , mRationalToEntity = Map.fromList [(r,e) | (e,r) <- xs]

    , mEntityToBitVec = IntMap.fromList ys
    , mBitVecToEntity = Map.fromList [(bv,e) | (e,bv) <- ys]
    }

eval :: Model -> Expr -> Value
eval m (EFrac r) = ValRational r
eval m (EBitVec bv) = ValBitVec bv
eval m (EAp "true" [])   = ValBool True
eval m (EAp "false" [])  = ValBool False
eval m (EAp "ite" [a,b,c]) = if valToBool m (eval m a) then eval m b else eval m c
eval m (EAp "and" xs)    = ValBool $ and $ map (valToBool m . eval m) xs
eval m (EAp "or" xs)     = ValBool $ or $ map (valToBool m . eval m) xs
eval m (EAp "xor" xs)    = ValBool $ foldr xor False $ map (valToBool m . eval m) xs
eval m (EAp "not" [x])   = ValBool $ not $ valToBool m $ eval m x
eval m (EAp "=>" [x,y])  = ValBool $ valToBool m (eval m x) .=>. valToBool m (eval m y)
eval m (EAp "<=" [x,y])  = ValBool $ valToRational m (eval m x) <= valToRational m (eval m y)
eval m (EAp ">=" [x,y])  = ValBool $ valToRational m (eval m x) >= valToRational m (eval m y)
eval m (EAp ">" [x,y])   = ValBool $ valToRational m (eval m x) >  valToRational m (eval m y)
eval m (EAp "<" [x,y])   = ValBool $ valToRational m (eval m x) <  valToRational m (eval m y)
eval m (EAp "+" xs)      = ValRational $ sum $ map (valToRational m . eval m) xs
eval m (EAp "-" [x])     = ValRational $ negate $ valToRational m (eval m x)
eval m (EAp "-" [x,y])   = ValRational $ valToRational m (eval m x) - valToRational m (eval m y)
eval m (EAp "*" xs)      = ValRational $ product $ map (valToRational m . eval m) xs
eval m (EAp "/" [x,y])
  | y' == 0   = eval m (EAp "_/0" [x])
  | otherwise = ValRational $ valToRational m (eval m x) / y'
  where
    y' = valToRational m (eval m y)

eval m (EAp "bvule" [x,y]) = ValBool $ BV.bvule (valToBitVec m (eval m x)) (valToBitVec m (eval m y))
eval m (EAp "bvult" [x,y]) = ValBool $ BV.bvult (valToBitVec m (eval m x)) (valToBitVec m (eval m y))
eval m (EAp "bvuge" [x,y]) = ValBool $ BV.bvuge (valToBitVec m (eval m x)) (valToBitVec m (eval m y))
eval m (EAp "bvugt" [x,y]) = ValBool $ BV.bvugt (valToBitVec m (eval m x)) (valToBitVec m (eval m y))
eval m (EAp "bvsle" [x,y]) = ValBool $ BV.bvsle (valToBitVec m (eval m x)) (valToBitVec m (eval m y))
eval m (EAp "bvslt" [x,y]) = ValBool $ BV.bvslt (valToBitVec m (eval m x)) (valToBitVec m (eval m y))
eval m (EAp "bvsge" [x,y]) = ValBool $ BV.bvsge (valToBitVec m (eval m x)) (valToBitVec m (eval m y))
eval m (EAp "bvsgt" [x,y]) = ValBool $ BV.bvsgt (valToBitVec m (eval m x)) (valToBitVec m (eval m y))
eval m (EAp "concat" [x,y]) =
  ValBitVec $ valToBitVec m (eval m x) <> valToBitVec m (eval m y)
eval m (EAp (FSym "extract" [IndexNumeral i, IndexNumeral j]) [x]) =
  ValBitVec $ BV.extract (fromIntegral i) (fromIntegral j) (valToBitVec m (eval m x))
eval m (EAp (FSym "repeat" [IndexNumeral i]) [x]) =
  ValBitVec $ BV.repeat (fromIntegral i) (valToBitVec m (eval m x))
eval m (EAp (FSym "zero_extend" [IndexNumeral i]) [x]) =
  ValBitVec $ BV.zeroExtend (fromIntegral i) (valToBitVec m (eval m x))
eval m (EAp (FSym "sign_extend" [IndexNumeral i]) [x]) =
  ValBitVec $ BV.signExtend (fromIntegral i) (valToBitVec m (eval m x))
eval m (EAp (FSym "rotate_left" [IndexNumeral i]) [x]) =
  ValBitVec $ rotateL (valToBitVec m (eval m x)) (fromIntegral i)
eval m (EAp (FSym "rotate_right" [IndexNumeral i]) [x]) =
  ValBitVec $ rotateR (valToBitVec m (eval m x)) (fromIntegral i)
eval m (EAp (FSym op1 []) [x])
  | Just op1' <- Map.lookup op1 table =
      let x' = BV.EConst $ valToBitVec m (eval m x)
      in ValBitVec $ BV.evalExpr (mBVModel m) $ BV.EOp1 op1' x'
  where
    table =
      Map.fromList
      [ ("bvnot", BV.OpNot)
      , ("bvneg", BV.OpNeg)
      ]
eval m (EAp (FSym op2 []) [x,y])
  | Just op2' <- Map.lookup op2 table =
      let x' = BV.EConst $ valToBitVec m (eval m x)
          y' = BV.EConst $ valToBitVec m (eval m y)
      in ValBitVec $ BV.evalExpr (mBVModel m) $ BV.EOp2 op2' x' y'
  where
    table = Map.fromList $ [("bvcomp", BV.OpComp)] ++ bvBinOpsSameSize

eval m (EAp "=" [x,y])   = ValBool $
  case (eval m x, eval m y) of
    (v1, v2) -> v1 == v2
eval m expr@(EAp f xs) =
  case Map.lookup f (mDefs m) of
    Nothing -> E.throw $ Error $ "unknown function symbol: " ++ show f
    Just (FBoolVar v) -> ValBool $ SAT.evalLit (mBoolModel m) v
    Just (FLRAVar v) -> ValRational $ mLRAModel m IntMap.! v
    Just (FBVVar v) -> ValBitVec $ BV.evalExpr (mBVModel m) (BV.EVar v)
    Just (FEUFFun (_, Sort s []) sym) ->
      let e = EUF.evalAp (mEUFModel m) sym (map (valToEntity m . eval m) xs)
      in case s of
           SSymUserDeclared _ _ -> ValUninterpreted e (exprSort' (mDefs m) expr)
           SSymBool -> ValBool (e == mEUFTrue m)
           SSymReal ->
             case IntMap.lookup e (mEntityToRational m) of
               Just r -> ValRational r
               Nothing -> ValRational (fromIntegral (1000000 + e))

valToBool :: Model -> Value -> Bool
valToBool _ (ValBool b) = b
valToBool _ _ = E.throw $ Error "boolean value is expected"

valToRational :: Model -> Value -> Rational
valToRational _ (ValRational r) = r
valToRational _ _ = E.throw $ Error "rational value is expected"

valToBitVec :: Model -> Value -> BV.BV
valToBitVec _ (ValBitVec bv) = bv
valToBitVec _ _ = E.throw $ Error "bitvector value is expected"

valToEntity :: Model -> Value -> EUF.Entity
valToEntity _ (ValUninterpreted e _) = e
valToEntity m (ValBool b)     = if b then mEUFTrue m else mEUFFalse m
valToEntity m (ValRational r) =
  case Map.lookup r (mRationalToEntity m) of
    Just e -> e
    Nothing -> EUF.mUnspecified (mEUFModel m)
valToEntity m (ValBitVec bv) =
  case Map.lookup bv (mBitVecToEntity m) of
    Just e -> e
    Nothing -> EUF.mUnspecified (mEUFModel m)

entityToValue :: Model -> EUF.Entity -> Sort -> Value
entityToValue m e s = 
  case s of
    Sort SSymBool _ -> ValBool (e == mEUFTrue m)
    Sort SSymReal _ ->
      case IntMap.lookup e (mEntityToRational m) of
        Just r -> ValRational r
        Nothing -> ValRational (fromIntegral (1000000 + e))
    Sort (SSymBitVec n) _ ->
      case IntMap.lookup e (mEntityToBitVec m) of
        Just bv -> ValBitVec bv
        Nothing -> ValBitVec (BV.nat2bv n 0)
    Sort (SSymUserDeclared _ _) _ -> ValUninterpreted e s

valSort :: Model -> Value -> Sort
valSort _m (ValUninterpreted _e s) = s
valSort _m (ValBool _b)     = sBool
valSort _m (ValRational _r) = sReal
valSort _m (ValBitVec bv) = sBitVec (BV.width bv)

data FunDef = FunDef [([Value], Value)] Value

evalFSym :: Model -> FSym -> FunDef
evalFSym m f = 
  case Map.lookup f (mDefs m) of
    Just (FEUFFun (argsSorts@(_:_), resultSort) sym) -> -- proper function symbol
      let tbl = EUF.mFunctions (mEUFModel m) IntMap.! sym
          defaultVal =
            case resultSort of
              Sort SSymReal [] -> ValRational 555555 -- Is it ok?
              Sort SSymBool [] -> ValBool False -- Is it ok?
              Sort (SSymUserDeclared _s _ar) _ss -> ValUninterpreted (EUF.mUnspecified (mEUFModel m)) resultSort
      in FunDef [ (zipWith (entityToValue m) args argsSorts, entityToValue m result resultSort)
                | (args, result) <- Map.toList tbl ]
                defaultVal
    Just _ -> FunDef [] $ eval m (EAp f []) -- constant symbol
    Nothing -> E.throw $ Error $ "unknown function symbol: " ++ show f

-- -------------------------------------------------------------------

getUnsatAssumptions :: Solver -> IO [Expr]
getUnsatAssumptions solver = do
  readIORef (smtUnsatAssumptions solver)

getUnsatCore :: Solver -> IO [String]
getUnsatCore solver = do
  readIORef (smtUnsatCore solver)

-- -------------------------------------------------------------------

pairs :: [a] -> [(a,a)]
pairs [] = []
pairs (x:xs) = [(x,y) | y <- xs] ++ pairs xs
