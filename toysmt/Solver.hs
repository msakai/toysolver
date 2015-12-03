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
  , resetAssertions

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
import Data.IORef
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Ratio
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
valueToTerm (SMT.ValUninterpreted n) =
  TermQualIdentifier $ QIdentifier $ ISymbol $ "@" ++ show n
                       
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
    SetLogic logic -> const (CmdGenResponse Success) <$> setLogic solver logic
    SetOption opt -> const (CmdGenResponse Success) <$> setOption solver opt
    GetOption s -> CmdGetOptionResponse <$> getOption solver s
    SetInfo attr -> const (CmdGenResponse Success) <$> setInfo solver attr
    GetInfo flags -> CmdGetInfoResponse <$> getInfo solver flags
    Push n -> const (CmdGenResponse Success) <$> push solver n
    Pop n -> const (CmdGenResponse Success) <$> pop solver n
    DeclareSort name arity -> const (CmdGenResponse Success) <$> declareSort solver name arity
    DefineSort name xs body -> const (CmdGenResponse Success) <$> defineSort solver name xs body
    DeclareFun name xs y -> const (CmdGenResponse Success) <$> declareFun solver name xs y
    DefineFun name xs y body -> const (CmdGenResponse Success) <$> defineFun solver name xs y body
    Assert tm -> const (CmdGenResponse Success) <$> assert solver tm
    GetAssertions -> CmdGetAssertionsResponse <$> getAssertions solver
    CheckSat -> CmdCheckSatResponse <$> checkSat solver
    GetValue ts -> CmdGetValueResponse <$> getValue solver ts
    GetAssignment -> CmdGetAssignmentResponse <$> getAssignment solver
    GetProof -> CmdGetProofResponse <$> getProof solver
    GetUnsatCore -> CmdGetUnsatCoreResponse <$> getUnsatCore solver
    Exit -> const (CmdGenResponse Success) <$> exit solver
  where
    h SMT.Unsupported = return (CmdGenResponse Unsupported)
    h (SMT.Error s) = return $ CmdGenResponse $
     -- GenResponse type uses strings in printed form.
     Error $ "\"" ++ concat [if c == '"' then "\"\"" else [c] | c <- s] ++ "\""

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
    InteractiveMode _b -> do
      -- interactive-mode is the old name for produce-assertions. Deprecated.
      if mode /= ModeStart then
        E.throwIO $ SMT.Error "interactive-mode option can be set only in start mode"
      else
        E.throwIO SMT.Unsupported
    ProduceProofs b -> do
      if mode /= ModeStart then
        E.throwIO $ SMT.Error "produce-proofs option can be set only in start mode"
      else if b then
        E.throwIO SMT.Unsupported
      else
        return ()
    ProduceUnsatCores b ->
      if mode /= ModeStart then
        E.throwIO $ SMT.Error "produce-unsat-cores option can be set only in start mode"
      else if b then
        E.throwIO SMT.Unsupported
      else
        return ()
    ProduceModels b ->
      if mode /= ModeStart then
        E.throwIO $ SMT.Error "produce-models option can be set only in start mode"
      else if b then
        E.throwIO SMT.Unsupported
      else
        return ()
    ProduceAssignments b ->
      if mode /= ModeStart then
        E.throwIO $ SMT.Error "produce-assignments option can be set only in start mode"
      else if b then
        E.throwIO SMT.Unsupported
      else
        return ()
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
        E.throwIO $ SMT.Error "produce-assignments option can be set only in start mode"
      else
        E.throwIO SMT.Unsupported
    Verbosity _lv -> E.throwIO SMT.Unsupported
    OptionAttr (AttributeVal "produce-assertions" _) -> do
      if mode /= ModeStart then
        E.throwIO $ SMT.Error "produce-assertions option can be set only in start mode"
      else
        E.throwIO SMT.Unsupported
    OptionAttr (AttributeVal "produce-unsat-assumptions" _) -> do
      if mode /= ModeStart then
        E.throwIO $ SMT.Error "produce-unsat-assumptions option can be set only in start mode"
      else
        E.throwIO SMT.Unsupported
    OptionAttr (AttributeVal "global-declarations" _) -> do
      if mode /= ModeStart then
        E.throwIO $ SMT.Error "global-declarations option can be set only in start mode"
      else
        E.throwIO SMT.Unsupported
    OptionAttr (AttributeVal "reproducible-resource-limit" _) -> do
      if mode /= ModeStart then
        E.throwIO $ SMT.Error "reproducible-resource-limit option can be set only in start mode"
      else
        E.throwIO SMT.Unsupported
    OptionAttr _attr -> E.throwIO SMT.Unsupported

getOption :: Solver -> String -> IO GetOptionResponse
getOption solver opt =
  case opt of
    "expand-definitions" -> do
      -- expand-definitions has been removed in SMT-LIB 2.5.
      E.throwIO SMT.Unsupported -- FIXME?
    "global-declarations" ->
      return $ AttrValueSymbol "false" -- default value
    "interactive-mode" -> do
      return $ AttrValueSymbol "false" -- default value
    "print-success" -> do
      b <- readIORef (svPrintSuccessRef solver)
      return $ AttrValueSymbol $ if b then "true" else "false"
    "produce-assignments" -> do
      return $ AttrValueSymbol "false" -- default value
    "produce-models" -> do
      return $ AttrValueSymbol "false" -- default value
    "produce-proofs" -> do
      return $ AttrValueSymbol "false" -- default value
    "produce-unsat-cores" -> do
      return $ AttrValueSymbol "false" -- default value
    "produce-unsat-assumptions" -> do
      return $ AttrValueSymbol "false" -- default value
    "regular-output-channel" -> do
      (fname,_) <- readIORef (svRegularOutputChannelRef solver)
      return $ AttrValueConstant (SpecConstantString fname)
    "diagnostic-output-channel" -> do
      (fname,_) <- readIORef (svDiagnosticOutputChannelRef solver)
      return $ AttrValueConstant (SpecConstantString fname)
    "random-seed" -> do
      return $ AttrValueConstant (SpecConstantNumeral 0) -- default value
    "reproducible-resource-limit" -> do
      return $ AttrValueConstant (SpecConstantNumeral 0) -- default value
    "verbosity" -> do
      return $ AttrValueConstant (SpecConstantNumeral 0) -- default value
    _ -> do
      E.throwIO SMT.Unsupported

setInfo :: Solver -> Attribute -> IO ()
setInfo solver attr = do
  modifyIORef (svInfoRef solver) (attr : )

getInfo :: Solver -> InfoFlags -> IO GetInfoResponse
getInfo solver flags = do
  mode <- readIORef (svModeRef solver)
  case flags of
    ErrorBehavior -> return [ResponseErrorBehavior ImmediateExit]
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
    InfoFlags _s -> do
      E.throwIO SMT.Unsupported

push :: Solver -> Int -> IO ()
push solver n = do
  replicateM_ n $ do
    (env,senv) <- readIORef (svEnvRef solver)
    modifyIORef (svSavedContextsRef solver) ((env,senv) :)
    SMT.pushContext =<< readIORef (svSMTSolverRef solver)
    writeIORef (svModeRef solver) ModeAssert

pop :: Solver -> Int -> IO ()
pop solver n = do
  replicateM_ n $ do
    cs <- readIORef (svSavedContextsRef solver)
    case cs of
      [] -> E.throwIO $ SMT.Error "pop from empty context"
      ((env,senv) : cs) -> do
        writeIORef (svEnvRef solver) (env,senv)
        writeIORef (svSavedContextsRef solver) cs
        SMT.popContext =<< readIORef (svSMTSolverRef solver)
        writeIORef (svModeRef solver) ModeAssert

resetAssertions :: Solver -> IO ()
resetAssertions solver = do
  cs <- readIORef (svSavedContextsRef solver)
  pop solver (length cs)

echo :: Solver -> String -> IO ()
echo solver s = do
  (_,h) <- readIORef (svRegularOutputChannelRef solver)
  hPrint h s -- "simply prints back s as is—including the surrounding double-quotes"

declareSort :: Solver -> String -> Int -> IO ()
declareSort solver name arity = do
  smt <- readIORef (svSMTSolverRef solver)
  s <- SMT.declareSSym smt name arity
  modifyIORef (svEnvRef solver) $ (\(fenv, senv) -> (fenv, Map.insert name (SortSym s) senv))
  writeIORef (svModeRef solver) ModeAssert

defineSort :: Solver -> String -> [String] -> Sort -> IO ()
defineSort solver name xs body = do
  modifyIORef (svEnvRef solver) $ (\(fenv, senv) -> (fenv, Map.insert name (SortDef senv xs body) senv))
  writeIORef (svModeRef solver) ModeAssert

declareFun :: Solver -> String -> [Sort] -> Sort -> IO ()
declareFun solver name xs y = do
  smt <- readIORef (svSMTSolverRef solver)
  (_, senv) <- readIORef (svEnvRef solver)
  f <- SMT.declareFSym smt name (map (interpretSort senv) xs) (interpretSort senv y)
  modifyIORef (svEnvRef solver) $ \(fenv, senv) -> (Map.insert name (EFSym f) fenv, senv)
  writeIORef (svModeRef solver) ModeAssert

defineFun :: Solver -> String -> [SortedVar] -> Sort -> Term -> IO ()
defineFun solver name xs y body = do
  writeIORef (svModeRef solver) ModeAssert
  (_, senv) <- readIORef (svEnvRef solver)
  let xs' = map (\(SV x s) -> (x, interpretSort senv s)) xs
      y'  = interpretSort senv y
  if null xs' then do
    body' <- processNamed solver body
    -- use EExpr?
    modifyIORef (svEnvRef solver) $ \(fenv, senv) -> (Map.insert name (EFunDef fenv [] y' body') fenv, senv)
  else do
    modifyIORef (svEnvRef solver) $ \(fenv, senv) -> (Map.insert name (EFunDef fenv xs' y' body) fenv, senv)
  writeIORef (svModeRef solver) ModeAssert

assert :: Solver -> Term -> IO ()
assert solver tm = do
  tm' <- processNamed solver tm
  smt <- readIORef (svSMTSolverRef solver)
  (env,_) <- readIORef (svEnvRef solver)
  SMT.assert smt (interpretFun env tm')
  writeIORef (svModeRef solver) ModeAssert

getAssertions :: Solver -> IO GetAssertionsResponse
getAssertions solver = do
  mode <- readIORef (svModeRef solver)
  if mode == ModeStart then
    E.throwIO $ SMT.Error "get-assertions cannot be used in start mode"
  else
    E.throwIO SMT.Unsupported

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
  if mode /= ModeSat then
    E.throwIO $ SMT.Error "get-assignment can only be used in sat mode"
  else
    E.throwIO SMT.Unsupported

getProof :: Solver -> IO GetProofResponse
getProof solver = do
  mode <- readIORef (svModeRef solver)
  if mode /= ModeUnsat then
    E.throwIO $ SMT.Error "get-proof can only be used in unsat mode"
  else
    E.throwIO SMT.Unsupported

getUnsatCore :: Solver -> IO GetUnsatCoreResponse
getUnsatCore solver = do
  mode <- readIORef (svModeRef solver)
  if mode /= ModeUnsat then
    E.throwIO $ SMT.Error "get-unsat-core can only be used in unsat mode"
  else
    E.throwIO SMT.Unsupported

exit :: Solver -> IO ()
exit _solver = exitSuccess

-- ----------------------------------------------------------------------


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
                modifyIORef (svEnvRef solver) $ \(fenv, senv) -> (Map.insert name (EExpr e) fenv, senv)
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
