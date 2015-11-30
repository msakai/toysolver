{-# OPTIONS_GHC -Wall #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Solver
-- Copyright   :  (c) Masahiro Sakai 2015
-- License     :  BSD-style
--
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  experimental
-- Portability :  portable
--
-----------------------------------------------------------------------------
module Solver
  ( Solver
  , newSolver

  -- * High-level API
  , execCommand
  , runCommand
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

  -- ** Introducing new symbols
  , declareSort
  , defineSort
  , declareFun
  , defineFun

  -- ** Asserting and inspecting formulas
  , assert
  , getAssertions

  -- ** Checking for satisfiability
  , checkSat

  -- ** Inspecting models
  , getValue
  , getAssignment

  -- ** Inspecting proofs
  , getProof
  , getUnsatCore

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
import Control.Monad.Trans
import Control.Monad.Trans.Except
import Data.Either
import Data.IORef
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Version as V
import Numeric (readFloat, readHex)
import System.Exit
import System.IO

import qualified ToySolver.SMT as SMT
import ToySolver.Version
import Smtlib.Syntax.Syntax
import Smtlib.Syntax.ShowSL

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
  = EFSym SMT.FSym
  | EExpr SMT.Expr
  | EFunDef EEnv [(String, SMT.Sort)] SMT.Sort Term

data SortEntry
  = SortSym SMT.SSym
  | SortExpr SMT.Sort
  | SortDef SortEnv [String] Sort

interpretSort :: SortEnv -> Sort -> SMT.Sort
interpretSort env s =
  case s of
    SortId (ISymbol name) -> f name []
    SortIdentifiers (ISymbol name) args -> f name args
    SortId (I_Symbol _ _) -> undefined
    SortIdentifiers (I_Symbol _ _) _ -> undefined
  where
    f name args =
      case Map.lookup name env of
        Nothing -> error ("unknown sort: " ++ name)
        Just (SortSym ssym) -> SMT.Sort ssym []
        Just (SortExpr s') -> s'
        Just (SortDef env' params body) ->
          interpretSort (Map.fromList (zip params (map (SortExpr . interpretSort env) args)) `Map.union` env') body

interpretFun :: EEnv -> Term -> SMT.Expr
interpretFun env t =
  case t of
    TermSpecConstant (SpecConstantNumeral n) -> SMT.EFrac (fromInteger n)
    TermSpecConstant (SpecConstantDecimal s) -> SMT.EFrac $ fst $ head $ readFloat s
    TermSpecConstant (SpecConstantHexadecimal s) -> SMT.EFrac $ fst $ head $ readHex s
    TermSpecConstant c@(SpecConstantBinary _s) -> error (show c)
    TermSpecConstant c@(SpecConstantString _s) -> error (show c)
    TermQualIdentifier qid -> f qid []
    TermQualIdentifierT  qid args -> f qid args
    TermLet bindings body ->
      interpretFun (Map.fromList [(v, EExpr (interpretFun env t2)) | VB v t2 <- bindings] `Map.union` env) body
    TermForall _bindings _body -> error "universal quantifiers are not supported yet"
    TermExists _bindings _body -> error "existential quantifiers are not supported yet"
    TermAnnot t2 _ -> interpretFun env t2 -- annotations are not supported yet
  where
    getName :: QualIdentifier -> String
    getName (QIdentifier id) = idToName id
    getName (QIdentifierAs id _sort) = idToName id

    idToName :: Identifier -> String
    idToName (ISymbol s) = s
    idToName (I_Symbol s _) = s -- XXX

    f qid args =
      case Map.lookup (getName qid) env of
        Nothing -> error ("unknown function symbol: " ++ getName qid)
        Just (EExpr e) -> e
        Just (EFSym fsym) -> SMT.EAp fsym (map (interpretFun env) args)
        Just (EFunDef env' params _y body) ->
          interpretFun (Map.fromList [(p,a) | ((p,_s),a) <- zip params (map (EExpr . interpretFun env) args) ] `Map.union` env') body

-- ----------------------------------------------------------------------

data Solver
  = Solver
  { svSMTSolverRef :: !(IORef SMT.Solver)
  , svEnvRef :: !(IORef Env)
  , svModeRef :: !(IORef Mode)
  , svSavedContextsRef :: !(IORef [Env])
  , svInfoRef :: IORef [Attribute]
  , svRegularOutputChannelRef :: !(IORef (String, Handle))
  , svDiagnosticOutputChannelRef :: !(IORef (String, Handle))
  , svPrintSuccessRef :: !(IORef Bool)
  }

newSolver :: IO Solver
newSolver = do
  solverRef <- newIORef =<< SMT.newSolver
  let fenv = Map.fromList
        [ (name, EFSym name)
        | name <- ["=", "true", "false", "not", "and", "or", "ite", "=>", "distinct", "+", "-", "*", "/", ">=", "<=", ">", "<"]
        ]
      senv = Map.fromList
        [ ("Real", SortExpr SMT.sReal)
        , ("Bool", SortExpr SMT.sBool)
        ]
  envRef <- newIORef (fenv, senv)
  modeRef <- newIORef ModeStart
  savedContextsRef <- newIORef []
  infoRef <- newIORef ([] :: [Attribute])
  regOutputRef <- newIORef ("stdout", stdout)
  diagOutputRef <- newIORef ("stderr", stderr)
  printSuccessRef <- newIORef True
  return $
    Solver
    { svSMTSolverRef = solverRef
    , svEnvRef = envRef
    , svModeRef = modeRef
    , svSavedContextsRef = savedContextsRef
    , svInfoRef = infoRef
    , svRegularOutputChannelRef = regOutputRef
    , svDiagnosticOutputChannelRef = diagOutputRef
    , svPrintSuccessRef = printSuccessRef
    }

execCommand :: Solver -> Command -> IO ()
execCommand solver cmd = do
  printResponse solver =<< runCommand solver cmd

printResponse :: Solver -> CmdResponse -> IO ()
printResponse solver rsp = do
  b <- readIORef (svPrintSuccessRef solver)
  unless (rsp == CmdGenResponse Success && not b) $ do
    (_,h) <- readIORef (svRegularOutputChannelRef solver)
    hPutStrLn h (showSL rsp)

runCommand :: Solver -> Command -> IO CmdResponse
runCommand solver cmd = E.handle h $
  case cmd of
    -- FIXME: unsupported commands
    -- * reset-assertions
    -- * declare-const, define-fun-rec, define-funs-rec
    -- * get-model
    -- * get-unsat-assumptions
    -- * reset
    -- * echo
    SetLogic logic -> CmdGenResponse <$> setLogic solver logic
    SetOption opt -> CmdGenResponse <$> setOption solver opt
    GetOption s -> either CmdGenResponse CmdGetOptionResponse <$> getOption solver s
    SetInfo attr -> CmdGenResponse <$> setInfo solver attr
    GetInfo flags -> either CmdGenResponse CmdGetInfoResponse <$> getInfo solver flags
    Push n -> CmdGenResponse <$> push solver n
    Pop n -> CmdGenResponse <$> pop solver n
    DeclareSort name arity -> CmdGenResponse <$> declareSort solver name arity
    DefineSort name xs body -> CmdGenResponse <$> defineSort solver name xs body
    DeclareFun name xs y -> CmdGenResponse <$> declareFun solver name xs y
    DefineFun name xs y body -> CmdGenResponse <$> defineFun solver name xs y body
    Assert tm -> CmdGenResponse <$> assert solver tm
    GetAssertions -> either CmdGenResponse CmdGetAssertionsResponse <$> getAssertions solver
    CheckSat -> CmdCheckSatResponse <$> checkSat solver
    GetValue ts -> either CmdGenResponse CmdGetValueResponse <$> getValue solver ts
    GetAssignment -> either CmdGenResponse CmdGetAssignmentResponse <$> getAssignment solver
    GetProof -> either CmdGenResponse CmdGetProofResponse <$> getProof solver
    GetUnsatCore -> either CmdGenResponse CmdGetUnsatCoreResponse <$> getUnsatCore solver
    Exit -> CmdGenResponse <$> exit solver
  where
    h SMT.Unsupported = return (CmdGenResponse Unsupported)
    h (SMT.Error s) = return (CmdGenResponse (Error s))

-- ----------------------------------------------------------------------

reset :: Solver -> IO GenResponse
reset solver = do
  writeIORef (svSMTSolverRef solver) =<< SMT.newSolver
  let fenv = Map.fromList
        [ (name, EFSym name)
        | name <- ["=", "true", "false", "not", "and", "or", "ite", "=>", "distinct", "+", "-", "*", "/", ">=", "<=", ">", "<"]
        ]
      senv = Map.fromList
        [ ("Real", SortExpr SMT.sReal)
        , ("Bool", SortExpr SMT.sBool)
        ]
  writeIORef (svEnvRef solver) (fenv, senv)
  writeIORef (svModeRef solver) ModeStart
  writeIORef (svSavedContextsRef solver) []
  writeIORef (svInfoRef solver) []
  writeIORef (svRegularOutputChannelRef solver) ("stdout",stdout)
  writeIORef (svDiagnosticOutputChannelRef solver) ("stderr",stderr)
  writeIORef (svPrintSuccessRef solver) True
  return Success

setLogic :: Solver -> String -> IO GenResponse
setLogic solver logic = do
  mode <- readIORef (svModeRef solver)
  if mode /= ModeStart then do
    return (Error "set-logic: not start mode")
  else do
    writeIORef (svModeRef solver) ModeAssert
    case logic of
      "QF_UFLRA" -> return Success
      "QF_UF" -> return Success
      "QF_LRA" -> return Success
      "ALL" -> return Success
      _ -> return Unsupported

setOption :: Solver -> Option -> IO GenResponse
setOption solver opt = do
  mode <- readIORef (svModeRef solver)
  case opt of
    PrintSuccess b -> do
      writeIORef (svPrintSuccessRef solver) b
      return Success
    ExpandDefinitions _b -> do
      -- expand-definitions has been removed in SMT-LIB 2.5.
      return Unsupported
    InteractiveMode _b -> do
      -- interactive-mode is the old name for produce-assertions. Deprecated.
      if mode /= ModeStart then
        return (Error "interactive-mode option can be set only in start mode")
      else
        return Unsupported
    ProduceProofs b ->
      if mode /= ModeStart then
        return (Error "produce-proofs option can be set only in start mode")
      else if b then
        return Unsupported
      else
        return Success
    ProduceUnsatCores b ->
      if mode /= ModeStart then
        return (Error "produce-unsat-cores option can be set only in start mode")
      else if b then
        return Unsupported
      else
        return Success
    ProduceModels b ->
      if mode /= ModeStart then
        return (Error "produce-models option can be set only in start mode")
      else if b then
        return Unsupported
      else
        return Success
    ProduceAssignments b ->
      if mode /= ModeStart then
        return (Error "produce-assignments option can be set only in start mode")
      else if b then
        return Unsupported
      else
        return Success
    RegularOutputChannel fname -> do
      h <- if fname == "stdout" then
             return stdout
           else
             openFile fname AppendMode
      writeIORef (svRegularOutputChannelRef solver) (fname, h)
      return Success
    DiagnosticOutputChannel fname -> do
      h <- if fname == "stderr" then
             return stderr
           else
             openFile fname AppendMode
      writeIORef (svDiagnosticOutputChannelRef solver) (fname, h)
      return Success
    RandomSeed _i ->
      if mode /= ModeStart then
        return (Error "produce-assignments option can be set only in start mode")
      else
        return Unsupported
    Verbosity _lv -> return Unsupported
    OptionAttr (AttributeVal "produce-assertions" _) -> do
      if mode /= ModeStart then
        return (Error "produce-assertions option can be set only in start mode")
      else
        return Unsupported
    OptionAttr (AttributeVal "produce-unsat-assumptions" _) -> do
      if mode /= ModeStart then
        return (Error "produce-unsat-assumptions option can be set only in start mode")
      else
        return Unsupported
    OptionAttr (AttributeVal "global-declarations" _) -> do
      if mode /= ModeStart then
        return (Error "global-declarations option can be set only in start mode")
      else
        return Unsupported
    OptionAttr (AttributeVal "reproducible-resource-limit" _) -> do
      if mode /= ModeStart then
        return (Error "reproducible-resource-limit option can be set only in start mode")
      else
        return Unsupported
    OptionAttr _attr -> return Unsupported

getOption :: Solver -> String -> IO (Either GenResponse GetOptionResponse)
getOption solver opt =
  case opt of
    "expand-definitions" -> do
      -- expand-definitions has been removed in SMT-LIB 2.5.
      return $ Left Unsupported -- FIXME?
    "global-declarations" ->
      return $ Right $ AttrValueSymbol "false" -- default value
    "interactive-mode" -> do
      return $ Right $ AttrValueSymbol "false" -- default value
    "print-success" -> do
      b <- readIORef (svPrintSuccessRef solver)
      return $ Right $ AttrValueSymbol $ if b then "true" else "false"
    "produce-assignments" -> do
      return $ Right $ AttrValueSymbol "false" -- default value
    "produce-models" -> do
      return $ Right $ AttrValueSymbol "false" -- default value
    "produce-proofs" -> do
      return $ Right $ AttrValueSymbol "false" -- default value
    "produce-unsat-cores" -> do
      return $ Right $ AttrValueSymbol "false" -- default value
    "produce-unsat-assumptions" -> do
      return $ Right $ AttrValueSymbol "false" -- default value
    "regular-output-channel" -> do
      (fname,_) <- readIORef (svRegularOutputChannelRef solver)
      return $ Right $ AttrValueConstant (SpecConstantString fname)
    "diagnostic-output-channel" -> do
      (fname,_) <- readIORef (svDiagnosticOutputChannelRef solver)
      return $ Right $ AttrValueConstant (SpecConstantString fname)
    "random-seed" -> do
      return $ Right $ AttrValueConstant (SpecConstantNumeral 0) -- default value
    "reproducible-resource-limit" -> do
      return $ Right $ AttrValueConstant (SpecConstantNumeral 0) -- default value
    "verbosity" -> do
      return $ Right $ AttrValueConstant (SpecConstantNumeral 0) -- default value
    _ -> do
      return $ Left Unsupported

setInfo :: Solver -> Attribute -> IO GenResponse
setInfo solver attr = do
  modifyIORef (svInfoRef solver) (attr : )
  return Success

getInfo :: Solver -> InfoFlags -> IO (Either GenResponse GetInfoResponse)
getInfo solver flags = do
  mode <- readIORef (svModeRef solver)
  case flags of
    ErrorBehavior -> return $ Right [ResponseErrorBehavior ImmediateExit]
    Name -> return $ Right [ResponseName "toysmt"]
    Authors -> return $ Right [ResponseName "Masahiro Sakai"]
    Version -> return $ Right [ResponseVersion (V.showVersion version)]
    Status -> return $ Left Unsupported
    ReasonUnknown -> do
      if mode /= ModeSat then
        return $ Left (Error "Executions of get-info with :reason-unknown are allowed only when the solver is in sat mode following a check command whose response was unknown.")
      else
        return $ Right [ResponseReasonUnknown Incomplete]
    AllStatistics -> do
      if not (mode == ModeSat || mode == ModeUnsat) then
        return $ Left (Error "Executions of get-info with :all-statistics are allowed only when the solver is in sat or unsat mode.")
      else
        return $ Left Unsupported
    InfoFlags _s -> do
      return $ Left Unsupported

push :: Solver -> Int -> IO GenResponse
push solver n = do
  replicateM_ n $ do
    (env,senv) <- readIORef (svEnvRef solver)
    modifyIORef (svSavedContextsRef solver) ((env,senv) :)
    writeIORef (svModeRef solver) ModeAssert
  return Success

pop :: Solver -> Int -> IO GenResponse
pop solver n = liftM (either id id) $ runExceptT $ do
  replicateM_ n $ do
    cs <- lift $ readIORef (svSavedContextsRef solver)
    case cs of
      [] -> throwE (Error "pop from empty context")
      ((env,senv) : cs) -> lift $ do
        writeIORef (svEnvRef solver) (env,senv)
        writeIORef (svSavedContextsRef solver) cs
        writeIORef (svModeRef solver) ModeAssert
  return Success

echo :: Solver -> String -> IO ()
echo solver s = do
  (_,h) <- readIORef (svRegularOutputChannelRef solver)
  hPrint h s -- "simply prints back s as is—including the surrounding double-quotes"

declareSort :: Solver -> String -> Int -> IO GenResponse
declareSort solver name arity = do
  smt <- readIORef (svSMTSolverRef solver)
  s <- SMT.declareSSym smt name arity
  modifyIORef (svEnvRef solver) $ (\(fenv, senv) -> (fenv, Map.insert name (SortSym s) senv))
  writeIORef (svModeRef solver) ModeAssert
  return Success

defineSort :: Solver -> String -> [String] -> Sort -> IO GenResponse
defineSort solver name xs body = do
  modifyIORef (svEnvRef solver) $ (\(fenv, senv) -> (fenv, Map.insert name (SortDef senv xs body) senv))
  writeIORef (svModeRef solver) ModeAssert
  return Success

declareFun :: Solver -> String -> [Sort] -> Sort -> IO GenResponse
declareFun solver name xs y = do
  smt <- readIORef (svSMTSolverRef solver)
  (_, senv) <- readIORef (svEnvRef solver)
  f <- SMT.declareFSym smt name (map (interpretSort senv) xs) (interpretSort senv y)
  modifyIORef (svEnvRef solver) $ \(fenv, senv) -> (Map.insert name (EFSym f) fenv, senv)
  writeIORef (svModeRef solver) ModeAssert
  return Success

defineFun :: Solver -> String -> [SortedVar] -> Sort -> Term -> IO GenResponse
defineFun solver name xs y body = do
  writeIORef (svModeRef solver) ModeAssert
  (_, senv) <- readIORef (svEnvRef solver)
  let xs' = map (\(SV x s) -> (x, interpretSort senv s)) xs
      y'  = interpretSort senv y
  modifyIORef (svEnvRef solver) $ \(fenv, senv) -> (Map.insert name (EFunDef fenv xs' y' body) fenv, senv)
  writeIORef (svModeRef solver) ModeAssert
  return Success

assert :: Solver -> Term -> IO GenResponse
assert solver tm = do
  smt <- readIORef (svSMTSolverRef solver)
  (env,_) <- readIORef (svEnvRef solver)
  SMT.assert smt (interpretFun env tm)
  writeIORef (svModeRef solver) ModeAssert
  return Success

getAssertions :: Solver -> IO (Either GenResponse GetAssertionsResponse)
getAssertions solver = do
  mode <- readIORef (svModeRef solver)
  if mode == ModeStart then
    return $ Left $ Error "get-assertions cannot be used in start mode"
  else
    return $ Left $ Unsupported

checkSat :: Solver -> IO CheckSatResponse
checkSat solver = do
  smt <- readIORef (svSMTSolverRef solver)
  ret <- SMT.checkSAT smt
  if ret then do
    writeIORef (svModeRef solver) ModeSat
    return Sat
  else do
    writeIORef (svModeRef solver) ModeUnsat
    return Unsat

getValue :: Solver -> [Term] -> IO (Either GenResponse GetValueResponse)
getValue solver _ts = do
  mode <- readIORef (svModeRef solver)
  if mode /= ModeSat then
    return $ Left $ Error "get-value can only be used in sat mode"
  else
    return $ Left $ Unsupported

getAssignment :: Solver -> IO (Either GenResponse GetAssignmentResponse)
getAssignment solver = do
  mode <- readIORef (svModeRef solver)
  if mode /= ModeSat then
    return $ Left $ Error "get-assignment can only be used in sat mode"
  else
    return $ Left $ Unsupported

getProof :: Solver -> IO (Either GenResponse GetProofResponse)
getProof solver = do
  mode <- readIORef (svModeRef solver)
  if mode /= ModeUnsat then
    return $ Left $ Error "get-proof can only be used in unsat mode"
  else
    return $ Left $ Unsupported

getUnsatCore :: Solver -> IO (Either GenResponse GetUnsatCoreResponse)
getUnsatCore solver = do
  mode <- readIORef (svModeRef solver)
  if mode /= ModeUnsat then
    return $ Left $ Error "get-unsat-core can only be used in unsat mode"
  else
    return $ Left $ Unsupported

exit :: Solver -> IO GenResponse
exit _solver = exitSuccess

-- ----------------------------------------------------------------------
