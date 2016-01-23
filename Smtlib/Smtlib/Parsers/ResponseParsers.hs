{-|
Module      : Smtlib.Parsers.ResponseParsers
Description : Parsers for Smtlib commands response.
Copyright   : Rogério Pontes 2015
License     : WTFPL
Maintainer  : rogerp62@outlook.com
Stability   : stable

This module contains all the required individual parsers for each reasponse to 
a Smtlib command, plus one parser to parse every result, parseCmdResult.

-}

module Smtlib.Parsers.ResponseParsers where

import           Control.Applicative           as Ctr hiding ((<|>))
import           Control.Monad
import           Data.Functor.Identity
import           Smtlib.Parsers.CommonParsers
import           Smtlib.Parsers.CommandsParsers
import           Smtlib.Syntax.Syntax        as CmdRsp
import           Text.Parsec.Prim              as Prim
import           Text.ParserCombinators.Parsec as Pc



parseCmdResult :: ParsecT String u Identity CmdResponse
parseCmdResult = Pc.try parseCmdGenResponse
             <|> Pc.try parseCmdCheckSatResponse
             <|> Pc.try parseCmdGetInfoResponse
             <|> Pc.try parseCmdGetAssertions
             <|> Pc.try parseCmdGetAssignment
             <|> Pc.try parseCmdGetProof
             <|> Pc.try parseCmdGetProof
             <|> Pc.try parseCmdGetValueResponse
             <|> Pc.try parseCmdGetModelResponse
             <|> Pc.try parseCmdGetOptionResponse
             <|> Pc.try parseCmdEchoResponse

{-
   #########################################################################
   #                                                                       #
   #                       Parser Cmd Gen Response                         #
   #                                                                       #
   #########################################################################
-}

parseCmdGenResponse :: ParsecT String u Identity CmdResponse
parseCmdGenResponse = liftM CmdGenResponse parseGenResponse

parseGenResponse :: ParsecT String u Identity GenResponse
parseGenResponse =  parseUnsupported <|> parseSuccess <|> parseGenError

parseSuccess :: ParsecT String u Identity GenResponse
parseSuccess = string "success" *> return Success

parseUnsupported :: ParsecT String u Identity GenResponse
parseUnsupported = string "unsupported" *> return Unsupported


parseGenError :: ParsecT String u Identity GenResponse
parseGenError = do
    _ <- aspO
    _ <- emptySpace
    _ <- string "error"
    _ <- emptySpace
    err <- str
    _ <- emptySpace
    _ <- aspC
    return $ CmdRsp.Error err






{-
   #########################################################################
   #                                                                       #
   #                       Parser get info response                        #
   #                                                                       #
   #########################################################################
-}

parseCmdGetInfoResponse :: ParsecT String u Identity CmdResponse
parseCmdGetInfoResponse = liftM CmdGetInfoResponse parseGetInfoResponse


parseGetInfoResponse :: ParsecT String u Identity [InfoResponse]
parseGetInfoResponse = do
    _ <-aspO
    _ <- emptySpace
    infoResp <- Pc.many $ parseInfoResponse <* Pc.try emptySpace
    _ <- aspC
    return infoResp



parseInfoResponse :: ParsecT String u Identity InfoResponse
parseInfoResponse =
    Pc.try parseResponseName <|>
    Pc.try parseResponseErrorBehavior <|>
    Pc.try parseResponseAuthors <|>
    Pc.try parseResponseVersion <|>
    Pc.try parseResponseReasonUnknown <|>
    Pc.try parseResponseAssertionStackLevels <|>
    parseResponseAttribute




parseResponseName :: ParsecT String u Identity InfoResponse
parseResponseName = string ":name"  *> emptySpace *> liftM ResponseName str


parseResponseErrorBehavior :: ParsecT String u Identity InfoResponse
parseResponseErrorBehavior = string ":error-behavior" *> emptySpace *>
                    liftM ResponseErrorBehavior parseErrorBehavior

parseErrorBehavior :: ParsecT String u Identity ErrorBehavior
parseErrorBehavior =
    (string "immediate-exit" >> return ImmediateExit) <|>
    (string "continued-execution" >> return ContinuedExecution)


parseResponseAuthors :: ParsecT String u Identity InfoResponse
parseResponseAuthors = string ":authors" *> emptySpace *>
    liftM ResponseAuthors str

parseResponseVersion :: ParsecT String u Identity InfoResponse
parseResponseVersion = string ":version" *> emptySpace *>
     liftM ResponseVersion str



parseResponseReasonUnknown :: ParsecT String u Identity InfoResponse
parseResponseReasonUnknown = string ":reason-unknown" *> emptySpace *>
    liftM ResponseReasonUnknown parseRReasonUnknown

parseRReasonUnknown :: ParsecT String u Identity ReasonUnknown
parseRReasonUnknown =
    (string "memout" >> return Memout) <|>
    (string "incomplete" >> return Incomplete)

parseResponseAssertionStackLevels :: ParsecT String u Identity InfoResponse
parseResponseAssertionStackLevels =
  string ":assertion-stack-levels" *> emptySpace *>
    liftM ResponseAssertionStackLevels (liftM read numeral)


parseResponseAttribute :: ParsecT String u Identity InfoResponse
parseResponseAttribute = liftM ResponseAttribute parseAttribute







{-
   #########################################################################
   #                                                                       #
   #                       Parser check sat response                       #
   #                                                                       #
   #########################################################################
-}



parseCmdCheckSatResponse :: ParsecT String u Identity CmdResponse
parseCmdCheckSatResponse = liftM  CmdCheckSatResponse parseCheckSatResponse



-- Parser for check sat response
parseCheckSatResponse :: ParsecT String u Identity CheckSatResponse
parseCheckSatResponse =
    (string "sat" >> return Sat) <|>
    Pc.try (string "unsat" >> return Unsat) <|>
    (string "unknown" >> return Unknown)




{-
   #########################################################################
   #                                                                       #
   #                       Parser get assertions cmd                       #
   #                                                                       #
   #########################################################################
-}


parseCmdGetAssertions :: ParsecT String u Identity CmdResponse
parseCmdGetAssertions =
  liftM CmdGetAssertionsResponse parseGetAssertionsResponse



-- parse Get Assertion Response
parseGetAssertionsResponse :: ParsecT String u Identity [Term]
parseGetAssertionsResponse = do
    _ <- aspO
    _ <- emptySpace
    terms <- Pc.many $ parseTerm <* Pc.try emptySpace
    _ <- aspC
    return terms

{-
   #########################################################################
   #                                                                       #
   #                       Parser get proof response                       #
   #                                                                       #
   #########################################################################
-}


parseCmdGetProof :: ParsecT String u Identity CmdResponse
parseCmdGetProof = liftM CmdGetProofResponse parseGetProofResponse

-- parse Get Proof response
parseGetProofResponse :: ParsecT String u Identity Sexpr
parseGetProofResponse = parseSexpr



{-
   #########################################################################
   #                                                                       #
   #                       Parser get unsat core response                  #
   #                                                                       #
   #########################################################################
-}


parseCmdGetUnsatCore :: ParsecT String u Identity CmdResponse
parseCmdGetUnsatCore =  liftM CmdGetUnsatCoreResponse parseGetUnsatCoreResp


-- parse Get unsat core response
parseGetUnsatCoreResp :: ParsecT String u Identity [String]
parseGetUnsatCoreResp = do
    _ <- aspO
    _ <- emptySpace
    symb <- Pc.many $ symbol <* Pc.try emptySpace
    _ <- aspC
    return symb


{-
   #########################################################################
   #                                                                       #
   #                       Parser Cmd Get value response                   #
   #                                                                       #
   #########################################################################
-}


parseCmdGetValueResponse :: ParsecT String u Identity CmdResponse
parseCmdGetValueResponse = liftM CmdGetValueResponse parseGetValueResponse



-- parse Get Value response
parseGetValueResponse :: ParsecT String u Identity [ValuationPair]
parseGetValueResponse =
    aspO *> (Pc.many $ parseValuationPair <* Pc.try emptySpace) <* aspC

parseValuationPair :: ParsecT String u Identity ValuationPair
parseValuationPair = do
    _ <- aspO
    _ <- emptySpace
    term1 <- parseTerm
    _ <- emptySpace
    term2 <- parseTerm
    _ <- emptySpace
    _ <- aspC
    return $ ValuationPair term1 term2


{-
   #########################################################################
   #                                                                       #
   #                       Parser Cmd get assignment Resp                  #
   #                                                                       #
   #########################################################################
-}


parseCmdGetAssignment :: ParsecT String u Identity CmdResponse
parseCmdGetAssignment = liftM CmdGetAssignmentResponse parseGetAssignmentResp

-- parse get Assignent Response
parseGetAssignmentResp :: ParsecT String u Identity [TValuationPair]
parseGetAssignmentResp = do
    _ <- aspO
    _ <- emptySpace
    pairs <- Pc.many $ parseTValuationPair <* Pc.try emptySpace
    _ <- aspC
    return pairs

-- parse t valuation pair
parseTValuationPair :: ParsecT String u Identity TValuationPair
parseTValuationPair = do
    _ <- aspO
    _ <- emptySpace
    symb <- symbol
    _ <- emptySpace
    bval <- parseBool
    _ <- emptySpace
    _ <-aspC
    return $ TValuationPair symb bval


{-
   #########################################################################
   #                                                                       #
   #                       Parser Cmd Get model response                   #
   #                                                                       #
   #########################################################################
-}


parseCmdGetModelResponse :: ParsecT String u Identity CmdResponse
parseCmdGetModelResponse = liftM CmdGetModelResponse parseGetModelResponse



-- parse Get Model response
parseGetModelResponse :: ParsecT String u Identity [Command]
parseGetModelResponse =
    aspO *> (Pc.many $ parseCommand <* Pc.try emptySpace) <* aspC


{-
   #########################################################################
   #                                                                       #
   #                       Parser Cmd get option response                  #
   #                                                                       #
   #########################################################################
-}


parseCmdGetOptionResponse :: ParsecT String u Identity CmdResponse
parseCmdGetOptionResponse = liftM CmdGetOptionResponse parseGetOptionResponse


-- parse Get Option Response
parseGetOptionResponse :: ParsecT String u Identity AttrValue
parseGetOptionResponse = parseAttributeValue

{-
   #########################################################################
   #                                                                       #
   #                       Parser Cmd get option response                  #
   #                                                                       #
   #########################################################################
-}


parseCmdEchoResponse :: ParsecT String u Identity CmdResponse
parseCmdEchoResponse = liftM CmdEchoResponse parseEchoResponse


-- parse Echo Response
parseEchoResponse :: ParsecT String u Identity EchoResponse
parseEchoResponse = str

{-
   #########################################################################
   #                                                                       #
   #                       Parser check-sat Alterg'os response             #
   #                                                                       #
   #########################################################################
-}
