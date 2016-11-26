{-# OPTIONS_GHC -Wall #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.SMT.SMTLIB2Solver
-- Copyright   :  (c) Masahiro Sakai 2015
-- License     :  BSD-style
--
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  experimental
-- Portability :  portable
--
-----------------------------------------------------------------------------
module ToySolver.SMT.SMTLIB2Solver
  ( module Smtlib.Syntax.Syntax
  , ShowSL (..)

  -- * The solver type
  , Solver
  , newSolver

  -- * High-level API
  , execCommand
  , execCommandString
  , runCommand
  , runCommandString
  , printResponse

  -- * Individual commands

  -- ** (Re)starting and terminating
  , reset
  , setLogic
  , setOption
  , exit

  -- ** Modifying the assertion stack
  , push
  , pop
  , resetAssertions

  -- ** Introducing new symbols
  , declareSort
  , defineSort
  , declareConst
  , declareFun
  , defineFun
  , defineFunRec
  , defineFunsRec

  -- ** Asserting and inspecting formulas
  , assert
  , getAssertions

  -- ** Checking for satisfiability
  , checkSat
  , checkSatAssuming

  -- ** Inspecting models
  , getValue
  , getAssignment
  , getModel

  -- ** Inspecting proofs
  , getProof
  , getUnsatCore
  , getUnsatAssumptions

  -- ** Inspecting settings
  , getInfo
  , getOption

  -- ** Script information
  , setInfo
  , echo
  ) where

import Control.Applicative
import qualified Control.Exception as E
import Control.Monad
import Data.Interned (unintern)
import Data.Interned.Text
import Data.IORef
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe (catMaybes)
import Data.Ratio
import Data.String
import qualified Data.Text as T
import qualified Data.Version as V
import Numeric (readDec, readFloat, readHex)
import System.Exit
import System.IO
import qualified Text.Parsec as Parsec

import qualified ToySolver.BitVector as BV
import qualified ToySolver.SMT as SMT
import ToySolver.Version
import Smtlib.Syntax.Syntax
import Smtlib.Syntax.ShowSL
import qualified Smtlib.Parsers.CommandsParsers as CommandsParsers

-- ----------------------------------------------------------------------

data Mode
  = ModeStart
  | ModeAssert
  | ModeSat
  | ModeUnsat
  deriving (Eq, Ord, Show)

type EEnv = Map String EEntry
type SortEnv = Map String SortEntry
type Env = (EEnv, SortEnv)

data EEntry
  = EFSymBuiltin InternedText
  | EFSymDeclared SMT.FSym [SMT.Sort] SMT.Sort
  | EExpr SMT.Expr Bool
  | EFunDef EEnv [(String, SMT.Sort)] SMT.Sort Term

data SortEntry
  = SortSym SMT.SSym
  | SortExpr SMT.Sort
  | SortDef SortEnv [String] Sort

interpretSort :: SortEnv -> Sort -> SMT.Sort
interpretSort env s =
  case s of
    SortId ident -> f ident []
    SortIdentifiers ident args -> f ident args
  where
    f ident@(I_Symbol "BitVec" indexes) args
      | not (null args) = error (showSL ident ++ ": wrong number of arguments (" ++ show (length args) ++ " for 0)")
      | [IndexNumeral n] <- indexes = SMT.sBitVec n
      | otherwise = error ("BitVec: wrong number of indexes (" ++ show (length indexes) ++ " for 1)")
    f ident@(I_Symbol _ _) _ =
      error ("unknown sort: " ++ showSL ident)
    f ident@(ISymbol name) args =
      case Map.lookup name env of
        Nothing -> error ("unknown sort: " ++ showSL ident)
        Just (SortSym ssym)
          | SMT.ssymArity ssym == length args -> SMT.Sort ssym args'
          | otherwise -> error (showSL ident ++ ": wrong number of arguments (" ++ show (length args) ++ " for " ++ show (SMT.ssymArity ssym) ++ ")")
        Just (SortExpr s')
          | null args -> s'
          | otherwise -> error (showSL ident ++ ": wrong number of arguments (" ++ show (length args) ++ " for 0)")
        Just (SortDef env' params body) ->
          interpretSort (Map.fromList (zip params (map SortExpr args')) `Map.union` env') body
      where
        args' = map (interpretSort env) args

interpretFun :: EEnv -> Term -> SMT.Expr
interpretFun env t =
  case t of
    TermSpecConstant (SpecConstantNumeral n) -> SMT.EValue $ SMT.ValRational $ fromInteger n
    TermSpecConstant (SpecConstantDecimal s) -> SMT.EValue $ SMT.ValRational $ fst $ head $ readFloat s
    TermSpecConstant (SpecConstantHexadecimal s) -> 
      let n = fst $ head $ readHex s
      in SMT.EValue $ SMT.ValBitVec $ BV.nat2bv (length s * 4) n
    TermSpecConstant (SpecConstantBinary s) -> 
      SMT.EValue $ SMT.ValBitVec $ BV.fromDescBits [c == '1' | c <- s]
    TermSpecConstant c@(SpecConstantString _s) -> error (show c)
    TermQualIdentifier qid -> f qid []
    TermQualIdentifierT  qid args -> f qid args
    TermLet bindings body ->
      interpretFun (Map.fromList [(v, EExpr (interpretFun env t2) False) | VB v t2 <- bindings] `Map.union` env) body
    TermForall _bindings _body -> error "universal quantifiers are not supported yet"
    TermExists _bindings _body -> error "existential quantifiers are not supported yet"
    TermAnnot t2 _ -> interpretFun env t2 -- annotations are not supported yet
  where
    unIdentifier :: Identifier -> (String, [Index])
    unIdentifier (ISymbol name) = (name, [])
    unIdentifier (I_Symbol name indexes) = (name, indexes)

    f (QIdentifierAs ident _sort) args = f (QIdentifier ident) args
    f (QIdentifier ident) args
      | ('b':'v':xs, [IndexNumeral n]) <- unIdentifier ident
      , ((x,_):_) <- readDec xs
      , x < 2^n
      = if not (null args)
        then error (showSL ident ++ " does not take indexes")
        else SMT.EValue $ SMT.ValBitVec $ BV.nat2bv n x
    f qid@(QIdentifier ident) args =
      case Map.lookup name env of
        Nothing -> error ("unknown function symbol: " ++ showSL qid)
        Just (EFSymBuiltin name') ->
          SMT.EAp (SMT.FSym name' indexes') (map (interpretFun env) args)
        Just _ | not (null indexes) -> error (showSL ident ++ " does not take indexes")
        Just (EExpr e _) -> e
        Just (EFSymDeclared fsym _ _) -> SMT.EAp fsym (map (interpretFun env) args)
        Just (EFunDef env' params _y body) ->
          interpretFun (Map.fromList [(p,a) | ((p,_s),a) <- zip params (map (\t -> EExpr (interpretFun env t) False) args) ] `Map.union` env') body
      where
        (name, indexes) = unIdentifier ident
        indexes' = map g indexes
        g (IndexNumeral n) = SMT.IndexNumeral (fromIntegral n)
        g (IndexSymbol s) = SMT.IndexSymbol (fromString s)

valueToTerm :: SMT.Value -> Term
valueToTerm (SMT.ValRational v) =
  case v `compare` 0 of
    GT -> f v
    EQ -> TermSpecConstant (SpecConstantNumeral 0)
    LT -> TermQualIdentifierT (QIdentifier $ ISymbol "-") [ f (negate v) ]
  where
    f v = TermQualIdentifierT (QIdentifier $ ISymbol "/")
          [ TermSpecConstant (SpecConstantNumeral (numerator v))
          , TermSpecConstant (SpecConstantNumeral (denominator v))
          ]
valueToTerm (SMT.ValBool b) =
  TermQualIdentifier $ QIdentifier $ ISymbol $ if b then "true" else "false"
valueToTerm (SMT.ValBitVec bv) =
  TermSpecConstant (SpecConstantBinary $ [if b then '1' else '0' | b <- BV.toDescBits bv])
valueToTerm (SMT.ValUninterpreted n s) =
  TermQualIdentifier $ QIdentifierAs (ISymbol $ "@" ++ show n) (sortToSortTerm s)

ssymToSymbol :: SMT.SSym -> Identifier
ssymToSymbol SMT.SSymBool = ISymbol "Bool"
ssymToSymbol SMT.SSymReal = ISymbol "Real"
ssymToSymbol (SMT.SSymBitVec n) = I_Symbol "BitVec" [IndexNumeral n]
ssymToSymbol (SMT.SSymUninterpreted name _) = ISymbol (T.unpack (unintern name))

sortToSortTerm :: SMT.Sort -> Sort
sortToSortTerm (SMT.Sort s []) = SortId (ssymToSymbol s)
sortToSortTerm (SMT.Sort s xs) = SortIdentifiers (ssymToSymbol s) (map sortToSortTerm xs)

-- ----------------------------------------------------------------------

data Solver
  = Solver
  { svSMTSolverRef :: !(IORef SMT.Solver)
  , svEnvRef :: !(IORef Env)
  , svModeRef :: !(IORef Mode)
  , svSavedContextsRef :: !(IORef [(Maybe (EEnv, SortEnv), [Term])])
  , svStatusRef :: IORef (Maybe Bool)
  , svAssertionsRef :: IORef [Term]
  , svRegularOutputChannelRef :: !(IORef (String, Handle))
  , svDiagnosticOutputChannelRef :: !(IORef (String, Handle))
  , svPrintSuccessRef :: !(IORef Bool)
  , svProduceAssertionsRef :: !(IORef Bool)
  , svProduceAssignmentRef :: !(IORef Bool)
  , svProduceModelsRef :: !(IORef Bool)
  , svProduceUnsatAssumptionsRef :: !(IORef Bool)
  , svProduceUnsatCoresRef :: !(IORef Bool)
  , svGlobalDeclarationsRef :: !(IORef Bool)
  , svUnsatAssumptionsRef :: !(IORef [Term])
  }

newSolver :: IO Solver
newSolver = do
  solverRef <- newIORef =<< SMT.newSolver
  envRef <- newIORef initialEnv
  modeRef <- newIORef ModeStart
  savedContextsRef <- newIORef []
  statusRef <- newIORef Nothing
  assertionsRef <- newIORef ([] :: [Term])
  regOutputRef <- newIORef ("stdout", stdout)
  diagOutputRef <- newIORef ("stderr", stderr)
  printSuccessRef <- newIORef True
  produceAssertionsRef <- newIORef False
  produceAssignmentRef <- newIORef False
  produceModelsRef <- newIORef False
  produceUnsatAssumptionsRef <- newIORef False
  produceUnsatCoresRef <- newIORef False  
  globalDeclarationsRef <- newIORef False
  unsatAssumptionsRef <- newIORef undefined
  return $
    Solver
    { svSMTSolverRef = solverRef
    , svEnvRef = envRef
    , svModeRef = modeRef
    , svUnsatAssumptionsRef = unsatAssumptionsRef
    , svSavedContextsRef = savedContextsRef
    , svStatusRef = statusRef
    , svAssertionsRef = assertionsRef
    , svRegularOutputChannelRef = regOutputRef
    , svDiagnosticOutputChannelRef = diagOutputRef
    , svPrintSuccessRef = printSuccessRef
    , svProduceAssertionsRef = produceAssertionsRef
    , svProduceAssignmentRef = produceAssignmentRef
    , svProduceModelsRef = produceModelsRef
    , svProduceUnsatCoresRef = produceUnsatCoresRef
    , svProduceUnsatAssumptionsRef = produceUnsatAssumptionsRef
    , svGlobalDeclarationsRef = globalDeclarationsRef
    }

initialEnv :: Env
initialEnv = (fenv, senv)
  where
    fenv = Map.fromList
      [ (name, EFSymBuiltin (fromString name))
      | name <- ["=", "true", "false", "not", "and", "or", "xor", "ite", "=>", "distinct"
                , "+", "-", "*", "/", ">=", "<=", ">", "<"
                , "extract", "concat", "bvnot", "bvneg"
                , "repeat", "zero_extend", "sign_extend", "rotate_left", "rotate_right"
                , "bvcomp"
                , "bvand", "bvor", "bvxor", "bvnand", "bvnor", "bvxnor"
                , "bvadd", "bvsub", "bvmul", "bvudiv", "bvurem", "bvsdiv", "bvsrem", "bvsmod", "bvshl", "bvlshr", "bvashr"
                , "bvule", "bvult", "bvuge", "bvugt", "bvsle", "bvslt", "bvsge", "bvsgt"
                ]
      ]
    senv = Map.fromList
      [ ("Real", SortSym SMT.SSymReal)
      , ("Bool", SortSym SMT.SSymBool)
      ]

execCommand :: Solver -> Command -> IO ()
execCommand solver cmd = do
  -- putStrLn $ showSL cmd
  printResponse solver =<< runCommand solver cmd

printResponse :: Solver -> CmdResponse -> IO ()
printResponse solver rsp = do
  b <- readIORef (svPrintSuccessRef solver)
  unless (rsp == CmdGenResponse Success && not b) $ do
    (_,h) <- readIORef (svRegularOutputChannelRef solver)
    hPutStrLn h (showSL rsp)

runCommand :: Solver -> Command -> IO CmdResponse
runCommand solver cmd = E.handle h $ do
  case cmd of
    SetLogic logic -> const (CmdGenResponse Success) <$> setLogic solver logic
    SetOption opt -> const (CmdGenResponse Success) <$> setOption solver opt
    GetOption s -> CmdGetOptionResponse <$> getOption solver s
    SetInfo attr -> const (CmdGenResponse Success) <$> setInfo solver attr
    GetInfo flags -> CmdGetInfoResponse <$> getInfo solver flags
    Push n -> const (CmdGenResponse Success) <$> push solver n
    Pop n -> const (CmdGenResponse Success) <$> pop solver n
    DeclareSort name arity -> const (CmdGenResponse Success) <$> declareSort solver name arity
    DefineSort name xs body -> const (CmdGenResponse Success) <$> defineSort solver name xs body
    DeclareConst name y -> const (CmdGenResponse Success) <$> declareConst solver name y
    DeclareFun name xs y -> const (CmdGenResponse Success) <$> declareFun solver name xs y
    DefineFun name xs y body -> const (CmdGenResponse Success) <$> defineFun solver name xs y body
    DefineFunRec name xs y body -> const (CmdGenResponse Success) <$> defineFunRec solver name xs y body
    DefineFunsRec fundecs terms -> const (CmdGenResponse Success) <$> defineFunsRec solver fundecs terms
    Assert tm -> const (CmdGenResponse Success) <$> assert solver tm
    GetAssertions -> CmdGetAssertionsResponse <$> getAssertions solver
    CheckSat -> CmdCheckSatResponse <$> checkSat solver
    CheckSatAssuming ts -> CmdCheckSatResponse <$> checkSatAssuming solver ts
    GetValue ts -> CmdGetValueResponse <$> getValue solver ts
    GetAssignment -> CmdGetAssignmentResponse <$> getAssignment solver
    GetModel -> CmdGetModelResponse <$> getModel solver
    GetProof -> CmdGetProofResponse <$> getProof solver
    GetUnsatCore -> CmdGetUnsatCoreResponse <$> getUnsatCore solver
    GetUnsatAssumptions -> CmdGetUnsatAssumptionsResponse <$> getUnsatAssumptions solver  
    Reset -> const (CmdGenResponse Success) <$> reset solver
    ResetAssertions -> const (CmdGenResponse Success) <$> resetAssertions solver
    Echo s -> CmdEchoResponse <$> echo solver s
    Exit -> const (CmdGenResponse Success) <$> exit solver
  where
    h SMT.Unsupported = return (CmdGenResponse Unsupported)
    h (SMT.Error s) = return $ CmdGenResponse $
     -- GenResponse type uses strings in printed form.
     Error $ "\"" ++ concat [if c == '"' then "\"\"" else [c] | c <- s] ++ "\""

execCommandString :: Solver -> String -> IO ()
execCommandString solver cmd = do
  printResponse solver =<< runCommandString solver cmd

runCommandString :: Solver -> String -> IO CmdResponse
runCommandString solver cmd =
  case Parsec.parse (Parsec.spaces >> CommandsParsers.parseCommand <* Parsec.eof) "" cmd of
    Left err -> 
      -- GenResponse type uses strings in printed form.
      return $ CmdGenResponse $ Error $ "\"" ++ concat [if c == '"' then "\"\"" else [c] | c <- show err] ++ "\""
    Right cmd ->
      runCommand solver cmd

-- ----------------------------------------------------------------------

reset :: Solver -> IO GenResponse
reset solver = do
  writeIORef (svSMTSolverRef solver) =<< SMT.newSolver
  writeIORef (svEnvRef solver) initialEnv
  writeIORef (svModeRef solver) ModeStart
  writeIORef (svSavedContextsRef solver) []
  writeIORef (svStatusRef solver) Nothing
  writeIORef (svRegularOutputChannelRef solver) ("stdout",stdout)
  writeIORef (svDiagnosticOutputChannelRef solver) ("stderr",stderr)
  writeIORef (svPrintSuccessRef solver) True
  writeIORef (svProduceAssertionsRef solver) False
  writeIORef (svProduceAssignmentRef solver) False
  writeIORef (svProduceModelsRef solver) False
  writeIORef (svProduceUnsatAssumptionsRef solver) False
  writeIORef (svProduceUnsatCoresRef solver) False
  writeIORef (svUnsatAssumptionsRef solver) undefined
  return Success

setLogic :: Solver -> String -> IO ()
setLogic solver logic = do
  mode <- readIORef (svModeRef solver)
  if mode /= ModeStart then do
    E.throwIO $ SMT.Error "set-logic can only be used in start mode"
  else do
    writeIORef (svModeRef solver) ModeAssert
    case logic of
      "QF_UFLRA" -> return ()
      "QF_UFRDL" -> return ()
      "QF_UF" -> return ()
      "QF_RDL" -> return ()
      "QF_LRA" -> return ()
      "QF_BV" -> return ()
      "QF_UFBV" -> return ()
      "ALL" -> return ()
      _ -> E.throwIO SMT.Unsupported

setOption :: Solver -> Option -> IO ()
setOption solver opt = do
  mode <- readIORef (svModeRef solver)
  case opt of
    PrintSuccess b -> do
      writeIORef (svPrintSuccessRef solver) b
    ExpandDefinitions _b -> do
      -- expand-definitions has been removed in SMT-LIB 2.5.
      E.throwIO SMT.Unsupported
    InteractiveMode b -> do
      -- interactive-mode is the old name for produce-assertions. Deprecated.
      unless (mode == ModeStart) $ do
        E.throwIO $ SMT.Error "interactive-mode option can be set only in start mode"
      writeIORef (svProduceAssertionsRef solver) b
      return ()
    ProduceProofs b -> do
      if mode /= ModeStart then
        E.throwIO $ SMT.Error "produce-proofs option can be set only in start mode"
      else if b then
        E.throwIO SMT.Unsupported
      else
        return ()
    ProduceUnsatCores b -> do
      unless (mode == ModeStart) $ do
        E.throwIO $ SMT.Error "produce-unsat-cores option can be set only in start mode"
      writeIORef (svProduceUnsatCoresRef solver) b
      return ()
    ProduceUnsatAssumptions b -> do
      unless (mode == ModeStart) $ do
        E.throwIO $ SMT.Error "produce-unsat-assumptions option can be set only in start mode"
      writeIORef (svProduceUnsatAssumptionsRef solver) b
      return ()
    ProduceModels b -> do
      unless (mode == ModeStart) $ do
        E.throwIO $ SMT.Error "produce-models option can be set only in start mode"
      writeIORef (svProduceModelsRef solver) b
      return ()
    ProduceAssignments b -> do
      unless (mode == ModeStart) $ do
        E.throwIO $ SMT.Error "produce-assignments option can be set only in start mode"
      writeIORef (svProduceAssignmentRef solver) b
      return ()
    ProduceAssertions b -> do
      unless (mode == ModeStart) $ do
        E.throwIO $ SMT.Error "produce-assertions option can be set only in start mode"
      writeIORef (svProduceAssertionsRef solver) b
      return ()
    GlobalDeclarations b -> do
      unless (mode == ModeStart) $ do
        E.throwIO $ SMT.Error "global-declarations option can be set only in start mode"
      writeIORef (svGlobalDeclarationsRef solver) b
      smt <- readIORef (svSMTSolverRef solver)
      SMT.setGlobalDeclarations smt b
    RegularOutputChannel fname -> do
      h <- if fname == "stdout" then
             return stdout
           else
             openFile fname AppendMode
      writeIORef (svRegularOutputChannelRef solver) (fname, h)
      return ()
    DiagnosticOutputChannel fname -> do
      h <- if fname == "stderr" then
             return stderr
           else
             openFile fname AppendMode
      writeIORef (svDiagnosticOutputChannelRef solver) (fname, h)
      return ()
    RandomSeed _i ->
      if mode /= ModeStart then
        E.throwIO $ SMT.Error "random-seed option can be set only in start mode"
      else
        E.throwIO SMT.Unsupported
    Verbosity _lv -> E.throwIO SMT.Unsupported
    ReproducibleResourceLimit _val -> do
      if mode /= ModeStart then
        E.throwIO $ SMT.Error "reproducible-resource-limit option can be set only in start mode"
      else
        E.throwIO SMT.Unsupported
    OptionAttr _attr -> E.throwIO SMT.Unsupported

getOption :: Solver -> String -> IO GetOptionResponse
getOption solver opt =
  case opt of
    ":expand-definitions" -> do
      -- expand-definitions has been removed in SMT-LIB 2.5.
      let b = False
      return $ AttrValueSymbol (showSL b)
    ":global-declarations" -> do
      b <- readIORef (svGlobalDeclarationsRef solver)
      return $ AttrValueSymbol (showSL b)
    ":interactive-mode" -> do
      -- interactive-mode is the old name for produce-assertions. Deprecated.
      b <- readIORef (svProduceAssertionsRef solver)
      return $ AttrValueSymbol (showSL b)
    ":print-success" -> do
      b <- readIORef (svPrintSuccessRef solver)
      return $ AttrValueSymbol (showSL b) 
    ":produce-assertions" -> do
      b <- readIORef (svProduceAssertionsRef solver)
      return $ AttrValueSymbol (showSL b)
    ":produce-assignments" -> do
      b <- readIORef (svProduceAssignmentRef solver)
      return $ AttrValueSymbol (showSL b)
    ":produce-models" -> do
      b <- readIORef (svProduceModelsRef solver)
      return $ AttrValueSymbol (showSL b)
    ":produce-proofs" -> do
      let b = False -- default value
      return $ AttrValueSymbol (showSL b)
    ":produce-unsat-cores" -> do
      b <- readIORef (svProduceUnsatCoresRef solver)
      return $ AttrValueSymbol (showSL b)
    ":produce-unsat-assumptions" -> do
      b <- readIORef (svProduceUnsatAssumptionsRef solver)
      return $ AttrValueSymbol (showSL b)
    ":regular-output-channel" -> do
      (fname,_) <- readIORef (svRegularOutputChannelRef solver)
      return $ AttrValueConstant (SpecConstantString fname)
    ":diagnostic-output-channel" -> do
      (fname,_) <- readIORef (svDiagnosticOutputChannelRef solver)
      return $ AttrValueConstant (SpecConstantString fname)
    ":random-seed" -> do
      return $ AttrValueConstant (SpecConstantNumeral 0) -- default value
    ":reproducible-resource-limit" -> do
      return $ AttrValueConstant (SpecConstantNumeral 0) -- default value
    ":verbosity" -> do
      return $ AttrValueConstant (SpecConstantNumeral 0) -- default value
    _ -> do
      E.throwIO SMT.Unsupported

setInfo :: Solver -> Attribute -> IO ()
setInfo solver (AttributeVal ":status" (AttrValueSymbol s)) = do
  v <- case s of
         "sat" -> return $ Just True
         "unsat" -> return $ Just False
         "unknown" -> return $ Nothing
         _ -> E.throwIO $ SMT.Error $ "invalid status value: " ++ s
  writeIORef (svStatusRef solver) v
setInfo _solver _ = return ()

getInfo :: Solver -> InfoFlags -> IO GetInfoResponse
getInfo solver flags = do
  mode <- readIORef (svModeRef solver)
  case flags of
    ErrorBehavior -> return [ResponseErrorBehavior ContinuedExecution]
    Name -> return [ResponseName "toysmt"]
    Authors -> return [ResponseName "Masahiro Sakai"]
    Version -> return [ResponseVersion (V.showVersion version)]
    Status -> E.throwIO SMT.Unsupported
    ReasonUnknown -> do
      if mode /= ModeSat then
        E.throwIO $ SMT.Error "Executions of get-info with :reason-unknown are allowed only when the solver is in sat mode following a check command whose response was unknown."
      else
        return [ResponseReasonUnknown Incomplete]
    AllStatistics -> do
      if not (mode == ModeSat || mode == ModeUnsat) then
        E.throwIO $ SMT.Error "Executions of get-info with :all-statistics are allowed only when the solver is in sat or unsat mode."
      else
        E.throwIO SMT.Unsupported
    AssertionStackLevels -> do
      saved <- readIORef (svSavedContextsRef solver)
      let n = length saved
      n `seq` return [ResponseAssertionStackLevels n]
    InfoFlags _s -> do
      E.throwIO SMT.Unsupported

push :: Solver -> Int -> IO ()
push solver n = do
  replicateM_ n $ do
    (env,senv) <- readIORef (svEnvRef solver)
    assertions <- readIORef (svAssertionsRef solver)
    globalDeclarations <- readIORef (svGlobalDeclarationsRef solver)
    if globalDeclarations then
      modifyIORef (svSavedContextsRef solver) ((Nothing, assertions) :)
    else
      modifyIORef (svSavedContextsRef solver) ((Just (env,senv), assertions) :)
    SMT.push =<< readIORef (svSMTSolverRef solver)
    writeIORef (svModeRef solver) ModeAssert

pop :: Solver -> Int -> IO ()
pop solver n = do
  replicateM_ n $ do
    cs <- readIORef (svSavedContextsRef solver)
    case cs of
      [] -> E.throwIO $ SMT.Error "pop from empty context"
      ((m,assertions) : cs) -> do
        case m of
          Just (env,senv) -> writeIORef (svEnvRef solver) (env,senv)
          Nothing -> return ()
        writeIORef (svAssertionsRef solver) assertions
        writeIORef (svSavedContextsRef solver) cs
        SMT.pop =<< readIORef (svSMTSolverRef solver)
        writeIORef (svModeRef solver) ModeAssert

resetAssertions :: Solver -> IO ()
resetAssertions solver = do
  cs <- readIORef (svSavedContextsRef solver)
  pop solver (length cs)

echo :: Solver -> String -> IO String
echo _solver s = return s

declareSort :: Solver -> String -> Int -> IO ()
declareSort solver name arity = do
  smt <- readIORef (svSMTSolverRef solver)
  s <- SMT.declareSSym smt name arity
  insertSort solver name (SortSym s)
  writeIORef (svModeRef solver) ModeAssert

defineSort :: Solver -> String -> [String] -> Sort -> IO ()
defineSort solver name xs body = do
  (_, senv) <- readIORef (svEnvRef solver)
  insertSort solver name (SortDef senv xs body)
  writeIORef (svModeRef solver) ModeAssert

declareConst :: Solver -> String -> Sort -> IO ()
declareConst solver name y = declareFun solver name [] y

declareFun :: Solver -> String -> [Sort] -> Sort -> IO ()
declareFun solver name xs y = do
  smt <- readIORef (svSMTSolverRef solver)
  (_, senv) <- readIORef (svEnvRef solver)
  let argsSorts = map (interpretSort senv) xs
      resultSort = interpretSort senv y
  f <- SMT.declareFSym smt name argsSorts resultSort
  insertFun solver name (EFSymDeclared f argsSorts resultSort)
  writeIORef (svModeRef solver) ModeAssert

defineFun :: Solver -> String -> [SortedVar] -> Sort -> Term -> IO ()
defineFun solver name xs y body = do
  writeIORef (svModeRef solver) ModeAssert
  (_, senv) <- readIORef (svEnvRef solver)
  let xs' = map (\(SV x s) -> (x, interpretSort senv s)) xs
      y'  = interpretSort senv y
  if null xs' then do
    body' <- processNamed solver body
    (fenv, _) <- readIORef (svEnvRef solver)
    -- use EExpr?
    insertFun solver name (EFunDef fenv [] y' body')
  else do
    (fenv, _) <- readIORef (svEnvRef solver)
    insertFun solver name (EFunDef fenv xs' y' body)
  writeIORef (svModeRef solver) ModeAssert

defineFunRec :: Solver -> String -> [SortedVar] -> Sort -> Term -> IO ()
defineFunRec _solver _name _xs _y _body = do
  E.throwIO SMT.Unsupported

defineFunsRec :: Solver -> [FunDec] -> [Term] -> IO ()
defineFunsRec _solver _fundecs _terms = do
  E.throwIO SMT.Unsupported

assert :: Solver -> Term -> IO ()
assert solver tm = do
  let mname =
        case tm of
          TermAnnot _body attrs
            | name:_ <- [name | AttributeVal ":named" (AttrValueSymbol name) <- attrs] ->
                Just name
          _ -> Nothing
  tm' <- processNamed solver tm
  smt <- readIORef (svSMTSolverRef solver)
  (env,_) <- readIORef (svEnvRef solver)
  case mname of
    Nothing -> SMT.assert smt (interpretFun env tm')
    Just name -> SMT.assertNamed smt name (interpretFun env tm')
  do b <- readIORef (svProduceAssertionsRef solver)
     when b $ modifyIORef (svAssertionsRef solver) (tm :)
  writeIORef (svModeRef solver) ModeAssert

getAssertions :: Solver -> IO GetAssertionsResponse
getAssertions solver = do
  mode <- readIORef (svModeRef solver)
  when (mode == ModeStart) $ do
    E.throwIO $ SMT.Error "get-assertions cannot be used in start mode"
  b <- readIORef (svProduceAssertionsRef solver)
  unless b $ do
    E.throwIO $ SMT.Error ":produce-assertions is not enabled"
  reverse <$> readIORef (svAssertionsRef solver)

checkSat :: Solver -> IO CheckSatResponse
checkSat solver = checkSatAssuming solver []

checkSatAssuming :: Solver -> [Term] -> IO CheckSatResponse
checkSatAssuming solver xs = do
  smt <- readIORef (svSMTSolverRef solver)

  (env,_) <- readIORef (svEnvRef solver)
  ref <- newIORef Map.empty
  ys <- forM xs $ \x -> do
    let y = interpretFun env x
    modifyIORef ref (Map.insert y x)
    return y

  ret <- SMT.checkSATAssuming smt ys

  do expected <- readIORef (svStatusRef solver)
     writeIORef (svStatusRef solver) Nothing -- I'm not sure if we should reset or not.
     h <- snd <$> readIORef (svDiagnosticOutputChannelRef solver)
     case expected of
       Just True | not ret -> hPutStrLn h "WARNING: unexpected unsat; expecting sat"
       Just False | ret -> hPutStrLn h "WARNING: unexpected sat; expecting unsat"
       _ -> return ()
     hFlush h

  if ret then do
    writeIORef (svModeRef solver) ModeSat
    return Sat
  else do
    writeIORef (svModeRef solver) ModeUnsat
    m <- readIORef ref
    es <- SMT.getUnsatAssumptions smt
    writeIORef (svUnsatAssumptionsRef solver) [m Map.! e | e <- es]
    return Unsat

getValue :: Solver -> [Term] -> IO GetValueResponse
getValue solver ts = do
  ts <- mapM (processNamed solver) ts  
  mode <- readIORef (svModeRef solver)
  unless (mode == ModeSat) $ do
    E.throwIO $ SMT.Error "get-value can only be used in sat mode"
  smt <- readIORef (svSMTSolverRef solver)
  m <- SMT.getModel smt
  (env,_) <- readIORef (svEnvRef solver)
  forM ts $ \t -> do
    let e = interpretFun env t
    let v = SMT.eval m e
    return $ ValuationPair t (valueToTerm v)

getAssignment :: Solver -> IO GetAssignmentResponse
getAssignment solver = do
  mode <- readIORef (svModeRef solver)
  unless (mode == ModeSat) $ do
    E.throwIO $ SMT.Error "get-assignment can only be used in sat mode"
  smt <- readIORef (svSMTSolverRef solver)
  m <- SMT.getModel smt
  (env, _) <- readIORef (svEnvRef solver)
  liftM concat $ forM (Map.toList env) $ \(name, entry) -> do
    case entry of
      EExpr e True -> do
        s <- SMT.exprSort smt e
        if s /= SMT.sBool then do
          return []
        else do
          let v = SMT.eval m e
          case v of
            (SMT.ValBool b) -> return [TValuationPair name b]
            _ -> E.throwIO $ SMT.Error "get-assignment: should not happen"
      _ -> return []

getModel :: Solver -> IO GetModelResponse
getModel solver = do
  mode <- readIORef (svModeRef solver)
  unless (mode == ModeSat) $ do
    E.throwIO $ SMT.Error "get-model can only be used in sat mode"
  smt <- readIORef (svSMTSolverRef solver)
  m <- SMT.getModel smt
  (env, _) <- readIORef (svEnvRef solver)
  liftM catMaybes $ forM (Map.toList env) $ \(name, entry) -> do
    case entry of
      EFSymDeclared sym argsSorts resultSort -> do
        case SMT.evalFSym m sym of
          SMT.FunDef [] val ->  do -- constant
            return $ Just $ DefineFun name [] (sortToSortTerm resultSort) (valueToTerm val)
          SMT.FunDef tbl defaultVal -> do -- proper function
            let argsSV :: [SortedVar]
                argsSV = [SV ("x!" ++ show i) (sortToSortTerm s) | (i,s) <- zip [(1::Int)..] argsSorts]
                args :: [Term]
                args = [TermQualIdentifier (QIdentifier (ISymbol x)) | SV x _ <- argsSV]
                f :: ([SMT.Value], SMT.Value) -> Term -> Term
                f (vals,val) tm = 
                  TermQualIdentifierT (QIdentifier (ISymbol "ite")) [cond, valueToTerm val, tm]
                  where
                    cond =
                      case zipWith (\arg val -> TermQualIdentifierT (QIdentifier (ISymbol "=")) [arg, valueToTerm val]) args vals of
                        [c] -> c
                        cs -> TermQualIdentifierT (QIdentifier (ISymbol "and")) cs
            return $ Just $ DefineFun name argsSV (sortToSortTerm resultSort) $
              foldr f (valueToTerm defaultVal) tbl
      _ -> return Nothing

getProof :: Solver -> IO GetProofResponse
getProof solver = do
  mode <- readIORef (svModeRef solver)
  if mode /= ModeUnsat then
    E.throwIO $ SMT.Error "get-proof can only be used in unsat mode"
  else
    E.throwIO SMT.Unsupported

getUnsatCore :: Solver -> IO GetUnsatCoreResponse
getUnsatCore solver = do
  smt <- readIORef (svSMTSolverRef solver)
  mode <- readIORef (svModeRef solver)
  unless (mode == ModeUnsat) $ do
    E.throwIO $ SMT.Error "get-unsat-core can only be used in unsat mode"
  SMT.getUnsatCore smt

getUnsatAssumptions :: Solver -> IO [Term]
getUnsatAssumptions solver = do
  mode <- readIORef (svModeRef solver)
  unless (mode == ModeUnsat) $ do
    E.throwIO $ SMT.Error "get-unsat-assumptions can only be used in unsat mode"
  readIORef (svUnsatAssumptionsRef solver)

exit :: Solver -> IO ()
exit _solver = exitSuccess

-- ----------------------------------------------------------------------

insertSort :: Solver -> String -> SortEntry -> IO ()
insertSort solver name sdef = do
  (fenv, senv) <- readIORef (svEnvRef solver)
  case Map.lookup name senv of
    Nothing -> writeIORef (svEnvRef solver) (fenv, Map.insert name sdef senv)
    Just _ -> E.throwIO $ SMT.Error (name ++ " is already used")

insertFun :: Solver -> String -> EEntry -> IO ()
insertFun solver name fdef = do
  (fenv, senv) <- readIORef (svEnvRef solver)
  case Map.lookup name fenv of
    Nothing -> writeIORef (svEnvRef solver) (Map.insert name fdef fenv, senv)
    Just _ -> E.throwIO $ SMT.Error (name ++ " is already used")

-- TODO: check closedness of terms
processNamed :: Solver -> Term -> IO Term
processNamed solver = f
  where
    f t@(TermSpecConstant _) = return t
    f t@(TermQualIdentifier _) = return t
    f (TermQualIdentifierT qid args) = do
      args' <- mapM f args
      return $ TermQualIdentifierT qid args'
    f (TermLet bindings body) = do
      body' <- f body
      return $ TermLet bindings body'
    f (TermForall bindings body) = do
      body' <- f body
      return $ TermForall bindings body'
    f (TermExists bindings body) = do
      body' <- f body
      return $ TermExists bindings body'
    f (TermAnnot body attrs) = do
      body' <- f body
      forM_ attrs $ \attr -> do
        case attr of
          AttributeVal ":named" val ->
            case val of
              AttrValueSymbol name -> do
                (env,_) <- readIORef (svEnvRef solver)
                let e = interpretFun env body'
                -- smt <- readIORef (svSMTSolverRef solver)
                -- s <- SMT.exprSort smt e
                insertFun solver name (EExpr e True)
              _ -> E.throwIO $ SMT.Error ":named attribute value should be a symbol"
          _ -> return ()
      let attrs' = [attr | attr <- attrs, attrName attr /= ":named"]
            where
              attrName (Attribute s) = s
              attrName (AttributeVal s _v) = s
      if null attrs' then
        return body'
      else
        return $ TermAnnot body' attrs'
