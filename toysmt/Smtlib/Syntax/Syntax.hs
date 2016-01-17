{-|
Module      : Smtlib.Parsers.CommandsParsers
Description : Smtlib Syntax
Copyright   : Rogério Pontes 2015
License     : WTFPL
Maintainer  : rogerp62@outlook.com
Stability   : stable

This module contains The syntax to create commands and responses.

-}
module Smtlib.Syntax.Syntax where

{-
   #########################################################################
   #                                                                       #
   #                       Parser for an SMTLib2 File                      #
   #                                                                       #
   #########################################################################
-}


type Source = [Command]


data Command = SetLogic String
             | SetOption Option
             | SetInfo Attribute
             | DeclareSort String Int
             | DefineSort String [String] Sort
             | DeclareConst String Sort
             | DeclareFun String [Sort] Sort
             | DefineFun String [SortedVar] Sort Term
             | DefineFunRec String [SortedVar] Sort Term
             | DefineFunsRec [FunDec] [Term]
             | Push Int
             | Pop Int
             | Reset
             | ResetAssertions
             | Assert Term
             | CheckSat
             | CheckSatAssuming [Term]
             | GetAssertions
             | GetModel
             | GetProof
             | GetUnsatCore
             | GetUnsatAssumptions
             | GetValue [Term]
             | GetAssignment
             | GetOption String
             | GetInfo InfoFlags
             | Echo String
             | Exit
             deriving (Show,Eq)

data Option = PrintSuccess Bool
            | ExpandDefinitions Bool
            | InteractiveMode Bool
            | ProduceProofs Bool
            | ProduceUnsatCores Bool
            | ProduceUnsatAssumptions Bool
            | ProduceModels Bool
            | ProduceAssignments Bool
            | ProduceAssertions Bool
            | GlobalDeclarations Bool
            | RegularOutputChannel String
            | DiagnosticOutputChannel String
            | RandomSeed Int
            | Verbosity Int
            | ReproducibleResourceLimit Int -- fixme
            | OptionAttr Attribute
             deriving (Show,Eq)


data InfoFlags = ErrorBehavior
               | Name
               | Authors
               | Version
               | Status
               | ReasonUnknown
               | AllStatistics
               | AssertionStackLevels
               | InfoFlags String
                deriving (Show,Eq)

-- Terms

data Term = TermSpecConstant SpecConstant
          | TermQualIdentifier QualIdentifier
          | TermQualIdentifierT  QualIdentifier [Term]
          | TermLet [VarBinding] Term
          | TermForall [SortedVar] Term
          | TermExists [SortedVar] Term
          | TermAnnot Term [Attribute]
          deriving (Show,Eq)



data VarBinding = VB String Term deriving (Show,Eq)



data SortedVar = SV String Sort deriving (Show,Eq)



data QualIdentifier = QIdentifier Identifier
                    | QIdentifierAs Identifier Sort
                    deriving (Show,Eq)


data FunDec = FunDec String [SortedVar] Sort deriving (Show,Eq)





-- Attributes

data AttrValue = AttrValueConstant SpecConstant
               | AttrValueSymbol String
               | AttrValueSexpr [Sexpr]
               deriving (Show,Eq)



data Attribute = Attribute String
               | AttributeVal String AttrValue
               deriving (Show,Eq)

-- Identifiers

data Index = IndexNumeral Int
           | IndexSymbol String
           deriving (Show,Eq)

data Identifier = ISymbol String
                | I_Symbol String [Index] deriving (Show,Eq)

-- Sorts

data Sort = SortId Identifier | SortIdentifiers Identifier [Sort]
            deriving (Show,Eq)


-- S-expressions
data SpecConstant = SpecConstantNumeral Integer
                  | SpecConstantDecimal String
                  | SpecConstantHexadecimal String
                  | SpecConstantBinary String
                  | SpecConstantString String
                  deriving (Show, Eq)



data Sexpr = SexprSpecConstant SpecConstant
           | SexprSymbol String
           | SexprKeyword String
           | SexprSxp [Sexpr]
           deriving (Show, Eq)









{-
   #########################################################################
   #                                                                       #
   #                             Command Response                          #
   #                                                                       #
   #########################################################################
-}



-- CmdResponse

data CmdResponse = CmdGenResponse GenResponse
                 | CmdGetInfoResponse GetInfoResponse
                 | CmdCheckSatResponse CheckSatResponse
                 | CmdGetAssertionsResponse  GetAssertionsResponse
                 | CmdGetAssignmentResponse GetAssignmentResponse
                 | CmdGetProofResponse GetProofResponse
                 | CmdGetUnsatCoreResponse GetUnsatCoreResponse
                 | CmdGetUnsatAssumptionsResponse GetUnsatAssumptionsResponse
                 | CmdGetValueResponse GetValueResponse
                 | CmdGetModelResponse GetModelResponse
                 | CmdGetOptionResponse GetOptionResponse
                 | CmdEchoResponse EchoResponse
                 deriving (Show, Eq)


-- Command Responses


-- Gen Response

data GenResponse =  Unsupported |  Success | Error String deriving (Show, Eq)


-- Error behavior

data ErrorBehavior = ImmediateExit | ContinuedExecution deriving (Show, Eq)


-- Reason unknown

data ReasonUnknown = Memout | Incomplete deriving (Show, Eq)

-- Status

data CheckSatResponse = Sat | Unsat | Unknown deriving (Show, Eq)

-- Info Response

type GetInfoResponse = [InfoResponse]

data InfoResponse  = ResponseErrorBehavior ErrorBehavior
                   | ResponseName String
                   | ResponseAuthors String
                   | ResponseVersion String
                   | ResponseReasonUnknown ReasonUnknown
                   | ResponseAssertionStackLevels Int
                   | ResponseAttribute Attribute
                   deriving (Show, Eq)

-- Get Assertion Response

type GetAssertionsResponse = [Term]


-- Get Proof Response

type GetProofResponse = Sexpr


--Get Unsat Core Response

type GetUnsatCoreResponse = [String]

-- Get Unsat Assumptions Response

type GetUnsatAssumptionsResponse = [Term]

-- Get Valuation Pair

data ValuationPair = ValuationPair Term Term deriving (Show, Eq)


type GetValueResponse = [ValuationPair]

type GetModelResponse = [Command]


-- get Assignment Response

data TValuationPair = TValuationPair String Bool deriving (Show, Eq)

type GetAssignmentResponse = [TValuationPair]


-- Get Option Response

type GetOptionResponse = AttrValue

-- Echo Response

type EchoResponse = String
