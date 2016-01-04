{-|
Module      : Smtlib.Parsers.CommandsParsers
Description : Parsers for Smtlib Commands
Copyright   : Rogério Pontes 2015
License     : WTFPL
Maintainer  : rogerp62@outlook.com
Stability   : stable

This module contains all the required individual parsers for each Smtlib command,
plus one parser to parse an entire SMTLib2 file, parseSource.

-}
module Smtlib.Parsers.CommandsParsers where

import           Control.Applicative           as Ctr hiding ((<|>))
import           Control.Monad
import           Data.Functor.Identity
import           Smtlib.Parsers.CommonParsers
import           Smtlib.Syntax.Syntax
import           Text.Parsec.Prim              as Prim
import           Text.ParserCombinators.Parsec as Pc



{-
   #########################################################################
   #                                                                       #
   #                       Parser for an SMTLib2 File                      #
   #                                                                       #
   #########################################################################
-}


parseSource :: ParsecT String u Identity Source
parseSource = emptySpace *> (Pc.many $ parseCommand <* Pc.try emptySpace)


{-
  "###################### Parser For Commands ###############################
-}
parseCommand :: ParsecT String u Identity Command
parseCommand = Pc.try parseSetLogic
           <|> Pc.try parseSetOption
           <|> Pc.try parseSetInfo
           <|> Pc.try parseDeclareSort
           <|> Pc.try parseDefineSort
           <|> Pc.try parseDeclareConst
           <|> Pc.try parseDeclareFun
           <|> Pc.try parseDefineFun
           <|> Pc.try parseDefineFunRec
           <|> Pc.try parseDefineFunsRec
           <|> Pc.try parsePush
           <|> Pc.try parsePop
           <|> Pc.try parseAssert
           <|> Pc.try parseCheckSat
           <|> Pc.try parseCheckSatAssuming
           <|> Pc.try parseGetAssertions
           <|> Pc.try parseGetModel
           <|> Pc.try parseGetProof
           <|> Pc.try parseGetUnsatCore
           <|> Pc.try parseGetUnsatAssumptions
           <|> Pc.try parseGetValue
           <|> Pc.try parseGetAssignment
           <|> Pc.try parseGetOption
           <|> Pc.try parseGetInfo
           <|> Pc.try parseReset
           <|> Pc.try parseResetAssertions
           <|> Pc.try parseEcho
           <|> parseExit



{-
   #########################################################################
   #                                                                       #
   #                       Parser for each command                         #
   #                                                                       #
   #########################################################################
-}




parseSetLogic :: ParsecT String u Identity Command
parseSetLogic = do
  _ <- aspO
  _ <- emptySpace
  _ <- string "set-logic"
  _ <- emptySpace
  symb <- symbol
  _ <- emptySpace
  _ <- aspC
  return $ SetLogic symb


parseSetOption :: ParsecT String u Identity Command
parseSetOption = do
  _ <- aspO
  _ <- emptySpace
  _ <- string "set-option"
  _ <- emptySpace
  attr <- parseOption
  _ <- emptySpace
  _ <- aspC
  return $ SetOption attr

parseSetInfo :: ParsecT String u Identity Command
parseSetInfo = do
  _ <- aspO
  _ <- emptySpace
  _ <- string "set-info"
  _ <- emptySpace <?> "foi aqui1?"
  attr <- parseAttribute <?> "foi aqui2?"
  _ <- emptySpace
  _ <- aspC
  return $ SetInfo attr


parseDeclareSort :: ParsecT String u Identity Command
parseDeclareSort = do
  _ <- aspO
  _ <- emptySpace
  _ <- string "declare-sort"
  _ <- emptySpace
  symb <- symbol
  _ <- emptySpace
  nume <- numeral
  _ <- emptySpace
  _ <- aspC
  return $ DeclareSort symb (read nume :: Int)

parseDefineSort :: ParsecT String u Identity Command
parseDefineSort = do
  _ <- aspO
  _ <- emptySpace
  _ <- string "define-sort"
  _ <- emptySpace
  symb <- symbol
  _ <- emptySpace
  _ <- aspO
  symbs <- Pc.many $ symbol <* Pc.try emptySpace
  _ <- aspC
  _ <- emptySpace
  sort <- parseSort
  _ <- emptySpace
  _ <- aspC
  return $ DefineSort symb symbs sort


parseDeclareConst :: ParsecT String u Identity Command
parseDeclareConst = do
  _ <-aspO
  _ <- emptySpace
  _ <- string "declare-const"
  _ <- emptySpace
  symb <- symbol
  _ <- emptySpace
  sort <- parseSort
  _ <- emptySpace
  _ <- aspC
  return $ DeclareConst symb sort


parseDeclareFun :: ParsecT String u Identity Command
parseDeclareFun = do
  _ <-aspO
  _ <- emptySpace
  _ <- string "declare-fun"
  _ <- emptySpace
  symb <- symbol
  _ <- emptySpace
  _ <- aspO
  _ <- emptySpace
  sorts <- Pc.many $ parseSort <* Pc.try emptySpace
  _ <- aspC
  _ <- emptySpace
  sort <- parseSort
  _ <- emptySpace
  _ <- aspC
  return $ DeclareFun symb sorts sort


parseDefineFun :: ParsecT String u Identity Command
parseDefineFun = do
  _ <- aspO
  _ <- emptySpace
  _ <- string "define-fun"
  _ <- emptySpace
  symb <- symbol
  _ <- emptySpace
  _ <- aspO
  sVars <- Pc.many $ parseSortedVar <* Pc.try emptySpace
  _ <- aspC
  _ <- emptySpace
  sort <- parseSort
  _ <- emptySpace
  term <- parseTerm
  _ <- emptySpace
  _ <- aspC
  return $ DefineFun symb sVars sort term


parseDefineFunRec :: ParsecT String u Identity Command
parseDefineFunRec = do
  _ <- aspO
  _ <- emptySpace
  _ <- string "define-fun-rec"
  _ <- emptySpace
  symb <- symbol
  _ <- emptySpace
  _ <- aspO
  sVars <- Pc.many $ parseSortedVar <* Pc.try emptySpace
  _ <- aspC
  _ <- emptySpace
  sort <- parseSort
  _ <- emptySpace
  term <- parseTerm
  _ <- emptySpace
  _ <- aspC
  return $ DefineFunRec symb sVars sort term


parseDefineFunsRec :: ParsecT String u Identity Command
parseDefineFunsRec = do
  _ <- aspO
  _ <- emptySpace
  _ <- string "define-funs-rec"
  _ <- emptySpace
  _ <- aspO
  _ <- emptySpace
  fundecs <- Pc.many $ parseFunDec <* Pc.try emptySpace
  _ <- aspC
  _ <- emptySpace
  _ <- aspO
  _ <- emptySpace
  terms <- Pc.many $ parseTerm <* Pc.try emptySpace
  _ <- aspC
  _ <- emptySpace
  _ <- aspC
  return $ DefineFunsRec fundecs terms

parseFunDec :: ParsecT String u Identity FunDec
parseFunDec = do
  _ <- aspO
  _ <- emptySpace
  symb <- symbol
  _ <- emptySpace
  _ <- aspO
  _ <- emptySpace
  sVars <- Pc.many $ parseSortedVar <* Pc.try emptySpace
  _ <- aspC
  _ <- emptySpace
  sort <- parseSort
  _ <- emptySpace
  _ <- aspC
  return (FunDec symb sVars sort)


parsePush :: ParsecT String u Identity Command
parsePush = do
  _ <- aspO
  _ <- emptySpace
  _ <- string "push"
  _ <- emptySpace
  nume <- option 1 $ do
    nume <- numeral
    _ <- emptySpace
    return (read nume :: Int)
  _ <- aspC
  return $ Push nume


parsePop :: ParsecT String u Identity Command
parsePop = do
  _ <- aspO
  _ <- emptySpace
  _ <- string "pop"
  _ <- emptySpace
  nume <- option 1 $ do
    nume <- numeral
    _ <- emptySpace
    return (read nume :: Int)
  _ <- aspC
  return $ Pop nume



parseAssert :: ParsecT String u Identity Command
parseAssert = do
  _ <- aspO
  _ <- emptySpace
  _ <- string "assert"
  _ <- emptySpace
  term <- parseTerm
  _ <- emptySpace
  _ <- aspC
  return $ Assert term


parseCheckSat :: ParsecT String u Identity Command
parseCheckSat = do
  _ <- aspO
  _ <- emptySpace
  _ <- string "check-sat"
  _ <- emptySpace
  _ <- aspC
  return CheckSat

parseCheckSatAssuming :: ParsecT String u Identity Command
parseCheckSatAssuming = do
  _ <- aspO
  _ <- emptySpace
  _ <- string "check-sat-assuming"
  _ <- emptySpace
  _ <- aspO
  terms <- Pc.many1 $ parseTerm <* Pc.try emptySpace
  _ <- aspC
  _ <- emptySpace
  _ <- aspC
  return (CheckSatAssuming terms)


parseGetAssertions :: ParsecT String u Identity Command
parseGetAssertions = do
  _ <- aspO
  _ <-emptySpace
  _ <- string "get-assertions"
  _ <- emptySpace
  _ <- aspC
  return GetAssertions

parseGetModel :: ParsecT String u Identity Command
parseGetModel = do
  _ <- aspO
  _ <- emptySpace
  _ <- string "get-model"
  _ <- emptySpace
  _ <-aspC
  return GetModel

parseGetProof :: ParsecT String u Identity Command
parseGetProof = do
  _ <- aspO
  _ <- emptySpace
  _ <- string "get-proof"
  _ <- emptySpace
  _ <-aspC
  return GetProof

parseGetUnsatCore :: ParsecT String u Identity Command
parseGetUnsatCore = do
  _ <- aspO
  _ <- emptySpace
  _ <- string "get-unsat-core"
  _ <- emptySpace
  _ <- aspC
  return GetUnsatCore

parseGetUnsatAssumptions :: ParsecT String u Identity Command
parseGetUnsatAssumptions = do
  _ <- aspO
  _ <- emptySpace
  _ <- string "get-unsat-assumptions"
  _ <- emptySpace
  _ <- aspC
  return GetUnsatAssumptions

parseGetValue :: ParsecT String u Identity Command
parseGetValue = do
  _ <- aspO
  _ <- emptySpace
  _ <- string "get-value"
  _ <- emptySpace
  _ <- aspO
  terms <- Pc.many1 $ parseTerm <* Pc.try emptySpace
  _ <- aspC
  _ <- emptySpace
  _ <- aspC
  return $ GetValue terms

parseGetAssignment :: ParsecT String u Identity Command
parseGetAssignment = do
  _ <- aspO
  _ <- emptySpace
  _ <- string "get-assignment"
  _ <- emptySpace
  _ <- aspC
  return GetAssignment


parseGetOption :: ParsecT String u Identity Command
parseGetOption = do
  _ <- aspO
  _ <- emptySpace
  _ <- string "get-option"
  _ <- emptySpace
  word <- keyword
  _ <- emptySpace
  _ <- aspC
  return $ GetOption word


parseGetInfo :: ParsecT String u Identity Command
parseGetInfo = do
  _ <- aspO
  _ <- emptySpace
  _ <- string "get-info"
  _ <- emptySpace
  flag <- parseInfoFlags
  _ <- emptySpace
  _ <- aspC
  return $ GetInfo flag


parseEcho :: ParsecT String u Identity Command
parseEcho = do
  _ <- aspO
  _ <- emptySpace
  _ <- string "echo"
  _ <- emptySpace
  s <- str
  _ <- emptySpace  
  _ <- aspC
  return $ Echo s


parseExit :: ParsecT String u Identity Command
parseExit = do
  _ <- aspO
  _ <- emptySpace
  _ <- string "exit"
  _ <- emptySpace
  _ <- aspC
  return Exit


parseReset :: ParsecT String u Identity Command
parseReset = do
  _ <- aspO
  _ <- emptySpace
  _ <- string "reset"
  _ <- emptySpace
  _ <- aspC
  return Reset


parseResetAssertions :: ParsecT String u Identity Command
parseResetAssertions = do
  _ <- aspO
  _ <- emptySpace
  _ <- string "reset-assertions"
  _ <- emptySpace
  _ <- aspC
  return ResetAssertions


{-
   #########################################################################
   #                                                                       #
   #                       Parse Command Options                           #
   #                                                                       #
   #########################################################################
-}

parseOption :: ParsecT String u Identity Option
parseOption = Pc.try parsePrintSuccess
          <|> Pc.try parseExpandDefinitions
          <|> Pc.try parseInteractiveMode
          <|> Pc.try parseProduceProofs
          <|> Pc.try parseProduceUnsatCores
          <|> Pc.try parseProduceUnsatAssumptions
          <|> Pc.try parseProduceModels
          <|> Pc.try parseProduceAssignments
          <|> Pc.try parseProduceAssertions
          <|> Pc.try parseGlobalDeclarations
          <|> Pc.try parseRegularOutputChannel
          <|> Pc.try parseDiagnosticOutputChannel
          <|> Pc.try parseRandomSeed
          <|> Pc.try parseVerbosity
          <|> Pc.try parseReproducibleResourceLimit
          <|> Pc.try parseOptionAttribute


-- parse PrintSucess
parsePrintSuccess :: ParsecT String u Identity Option
parsePrintSuccess = do
  _ <- string ":print-success"
  _ <- spaces
  val <- parseBool
  return $ PrintSuccess val


parseExpandDefinitions :: ParsecT String u Identity Option
parseExpandDefinitions = do
  _ <- string ":expand-definitions"
  _ <- spaces
  val <- parseBool
  return $ ExpandDefinitions val


parseInteractiveMode :: ParsecT String u Identity Option
parseInteractiveMode = do
  _ <- string ":interactive-mode"
  _ <- spaces
  val <- parseBool
  return $ InteractiveMode val

parseProduceProofs :: ParsecT String u Identity Option
parseProduceProofs = do
  _ <- string ":produce-proofs"
  _ <- spaces
  val <- parseBool
  return $ ProduceProofs val


parseProduceUnsatCores :: ParsecT String u Identity Option
parseProduceUnsatCores = do
  _ <- string ":produce-unsat-cores"
  _ <- spaces
  val <- parseBool
  return $ ProduceUnsatCores val

parseProduceUnsatAssumptions :: ParsecT String u Identity Option
parseProduceUnsatAssumptions = do
  _ <- string ":produce-unsat-assumptions"
  _ <- spaces
  val <- parseBool
  return $ ProduceUnsatAssumptions val

parseProduceModels :: ParsecT String u Identity Option
parseProduceModels = do
  _ <- string ":produce-models"
  _ <- spaces
  val <- parseBool
  return $ ProduceModels val

parseProduceAssignments :: ParsecT String u Identity Option
parseProduceAssignments = do
  _ <- string ":produce-assignments"
  _ <- spaces
  val <- parseBool
  return $ ProduceAssignments val

parseProduceAssertions :: ParsecT String u Identity Option
parseProduceAssertions = do
  _ <- string ":produce-assertions"
  _ <- spaces
  val <- parseBool
  return $ ProduceAssertions val

parseGlobalDeclarations :: ParsecT String u Identity Option
parseGlobalDeclarations = do
  _ <- string ":global-declarations"
  _ <- spaces
  val <- parseBool
  return $ GlobalDeclarations val


parseRegularOutputChannel :: ParsecT String u Identity Option
parseRegularOutputChannel = do
  _ <- string ":regular-output-channel"
  _ <- spaces
  val <- str
  return $ RegularOutputChannel val


parseDiagnosticOutputChannel :: ParsecT String u Identity Option
parseDiagnosticOutputChannel = do
  _ <- string ":diagnostic-output-channel"
  _ <- spaces
  val <- str
  return $ DiagnosticOutputChannel val

parseRandomSeed :: ParsecT String u Identity Option
parseRandomSeed = do
  _ <- string ":random-seed"
  _ <- spaces
  val <- numeral
  return $ RandomSeed (read val :: Int)


parseVerbosity :: ParsecT String u Identity Option
parseVerbosity = do
  _ <- string ":verbosity"
  _ <- spaces
  val <- numeral
  return $ Verbosity (read val :: Int)


parseReproducibleResourceLimit :: ParsecT String u Identity Option
parseReproducibleResourceLimit = do
  _ <- string ":reproducible-resource-limit"
  _ <- spaces
  val <- numeral
  return $ ReproducibleResourceLimit (read val :: Int)


parseOptionAttribute :: ParsecT String u Identity Option
parseOptionAttribute = do
  attr <- parseAttribute
  return $ OptionAttr attr




{-
   #########################################################################
   #                                                                       #
   #                       Parsers for Info FLags                          #
   #                                                                       #
   #########################################################################
-}

parseInfoFlags :: ParsecT String u Identity InfoFlags
parseInfoFlags = Pc.try parseErrorBehaviour
             <|> Pc.try parseName
             <|> Pc.try parseAuthors
             <|> Pc.try parseVersion
             <|> Pc.try parseStatus
             <|> Pc.try parseReasonUnknown
             <|> Pc.try parseAllStatistics
             <|> Pc.try parseAssertionStackLevels
             <|> parseInfoKeyword


parseErrorBehaviour :: ParsecT String u Identity InfoFlags
parseErrorBehaviour = string ":error-behaviour" *> return ErrorBehavior


parseName :: ParsecT String u Identity InfoFlags
parseName = string ":name" *> return Name

parseAuthors :: ParsecT String u Identity InfoFlags
parseAuthors = string ":authors" *> return Authors

parseVersion :: ParsecT String u Identity InfoFlags
parseVersion = string ":version" *> return Version

parseStatus :: ParsecT String u Identity InfoFlags
parseStatus = string ":status" *> return Status

parseReasonUnknown :: ParsecT String u Identity InfoFlags
parseReasonUnknown = string ":reason-unknown" *> return  ReasonUnknown

parseAllStatistics :: ParsecT String u Identity InfoFlags
parseAllStatistics = string ":all-statistics" *> return AllStatistics

parseAssertionStackLevels :: ParsecT String u Identity InfoFlags
parseAssertionStackLevels = string ":assertion-stack-levels" *> return AssertionStackLevels

parseInfoKeyword :: ParsecT String u Identity InfoFlags
parseInfoKeyword = liftM InfoFlags keyword
