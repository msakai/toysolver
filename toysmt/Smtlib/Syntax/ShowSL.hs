{-|
Module      : Smtlib.Syntax.ShowSL
Description : Instance to print the syntax.
Copyright   : Rogério Pontes 2015
License     : WTFPL
Maintainer  : rogerp62@outlook.com
Stability   : stable

Functions to print the syntax as a SMTLib.

-}
module Smtlib.Syntax.ShowSL where

import           Data.Char
import qualified Data.Set as Set
import           Data.List
import           Smtlib.Syntax.Syntax





joinA ::(ShowSL a) => [a] -> String
joinA = unwords.fmap showSL

joinNs :: [Int] -> String
joinNs = unwords.fmap show

showSymbol :: String -> String
showSymbol s
  | c:_ <- s, isDigit c = quoted
  | all p s && s `Set.notMember` reserved = s
  | otherwise = quoted
  where
    quoted = "|" ++ s ++ "|"
    p c = (isAscii c && isAlpha c) || isDigit c || c `elem` "~!@$%^&*_-+=<>.?/"
    reserved = Set.fromList $
      ["BINARY", "DECIMAL", "HEXADECIMAL", "NUMERAL", "STRING", "_", "!", "as", "let", "exists", "forall", "par"] ++
      ["set-logic", "set-option", "set-info", "declare-sort", "define-sort", "declare-const", "declare-fun", "declare-fun-rec", "declare-funs-rec", "push", "pop", "reset", "reset-assertions", "assert", "check-sat", "check-sat-assuming", "get-assertions", "get-model", "get-proof", "get-unsat-core", "get-unsat-assumptions", "get-value", "get-assignment", "get-option", "get-info", "echo", "exit"]


class ShowSL a where
  showSL :: a -> String



{-
   #########################################################################
   #                                                                       #
   #                       ShowSL for an SMTLib2 File                      #
   #                                                                       #
   #########################################################################
-}


instance ShowSL Command where
  showSL (SetLogic s) = "(set-logic " ++ showSymbol s ++ ")"
  showSL (SetOption opt) = "(set-option " ++ showSL opt ++ ")"
  showSL (SetInfo info) = "(set-info " ++ showSL info ++ ")"
  showSL (DeclareSort str val) =  "(declare-sort " ++ showSymbol str ++
    " " ++ show val ++ ")"
  showSL (DefineSort str strs sort) = "(define-sort " ++ showSymbol str ++
    " (" ++ unwords (map showSymbol strs) ++ ") " ++ showSL sort ++ ") "
  showSL (DeclareConst str sort) = "(declare-const  " ++ showSymbol str ++
    " " ++ showSL sort ++ ") "
  showSL (DeclareFun  str sorts sort) = "(declare-fun  " ++ showSymbol str ++
    " ("  ++ joinA sorts ++ ") " ++ showSL sort ++ ") "
  showSL (DefineFun str srvs sort term) = "(define-fun "   ++ showSymbol str ++
    " (" ++ joinA srvs ++ ") " ++ showSL sort ++ " " ++ showSL term ++ ")"
  showSL (DefineFunRec str srvs sort term) = "(define-fun-rec "   ++ showSymbol str ++
    " (" ++ joinA srvs ++ ") " ++ showSL sort ++ " " ++ showSL term ++ ")"
  showSL (DefineFunsRec fundecs terms) = "(define-funs-rec " ++
    " (" ++ joinA fundecs ++ ") (" ++ joinA terms ++ "))"
  showSL (Push n) = "(push " ++ show n ++ ")"
  showSL (Pop n) = "(pop " ++show n ++ ")"
  showSL (Assert term) = "(assert " ++ showSL term ++ ")"
  showSL CheckSat = "(check-sat)"
  showSL (CheckSatAssuming terms) = "(check-sat-assuming (" ++ joinA terms ++ "))"
  showSL GetAssertions = "(get-assertions)"
  showSL GetModel = "(get-model)"
  showSL GetProof = "(get-proof)"
  showSL GetUnsatCore = "(get-unsat-core)"
  showSL GetUnsatAssumptions = "(get-unsat-assumptions)"
  showSL (GetValue terms) = "(get-value (" ++ joinA terms ++ "))"
  showSL GetAssignment =  "(get-assignment)"
  showSL (GetOption opt) = "(get-option " ++ opt ++ ")"
  showSL (GetInfo info) = "(get-info " ++ showSL info ++ ")"
  showSL Reset = "(reset)"
  showSL ResetAssertions = "(reset-assertions)"
  showSL (Echo str) = "(echo " ++ str ++ ")"
  showSL Exit = "(exit)"


instance ShowSL Bool where
  showSL True = "true"
  showSL False = "false"

instance ShowSL Option where
  showSL (PrintSuccess b) = ":print-success " ++ showSL b
  showSL (ExpandDefinitions b) = ":expand-definitions " ++ showSL b
  showSL (InteractiveMode b) = ":interactive-mode " ++ showSL b
  showSL (ProduceProofs b) = ":produce-proofs " ++ showSL b
  showSL (ProduceUnsatCores b) = ":produce-unsat-cores " ++  showSL b
  showSL (ProduceUnsatAssumptions b) = ":produce-unsat-assumptions " ++  showSL b
  showSL (ProduceModels b) = ":produce-models " ++ showSL b
  showSL (ProduceAssignments b) = ":produce-assignments " ++ showSL b
  showSL (ProduceAssertions b) = ":produce-assertions " ++ showSL b
  showSL (GlobalDeclarations b) = ":global-declarations " ++ showSL b
  showSL (RegularOutputChannel s) = ":regular-output-channel " ++ s
  showSL (DiagnosticOutputChannel s) = ":diagnostic-output-channel " ++ s
  showSL (RandomSeed n) = ":random-seed " ++ show n
  showSL (Verbosity n) = ":verbosity " ++ show n
  showSL (ReproducibleResourceLimit n) = ":reproducible-resource-limit " ++ show n
  showSL (OptionAttr attr) = showSL attr

instance ShowSL InfoFlags where
  showSL ErrorBehavior = ":error-behavior"
  showSL Name = ":name"
  showSL Authors = ":authors"
  showSL Version = ":version"
  showSL Status = ":status"
  showSL ReasonUnknown = ":reason-unknown"
  showSL AllStatistics = ":all-statistics"
  showSL AssertionStackLevels = ":assertion-stack-levels"
  showSL (InfoFlags s) = s


instance ShowSL Term where
  showSL (TermSpecConstant sc) = showSL sc
  showSL (TermQualIdentifier qi) = showSL qi
  showSL (TermQualIdentifierT qi terms) =
    "(" ++ showSL qi ++ " " ++ joinA terms ++ ")"
  showSL (TermLet vb term) =
    "(let (" ++ joinA vb ++ ") " ++ showSL term ++ ")"
  showSL (TermForall svs term) =
    "(forall (" ++ joinA svs ++ " ) " ++ showSL term ++ ")"
  showSL (TermExists svs term) =
    "(exists (" ++ joinA svs ++ " ) " ++ showSL term ++ ")"
  showSL (TermAnnot term atts) =
    "(! " ++ showSL term ++ " " ++ joinA atts ++ ")"

instance ShowSL VarBinding where
  showSL (VB str term) = "("++ showSymbol str ++ " " ++ showSL term ++ ")"

instance ShowSL SortedVar where
  showSL (SV str sort)  = "(" ++ showSymbol str ++ " " ++ showSL sort ++ ")"

instance ShowSL QualIdentifier where
  showSL (QIdentifier iden) = showSL iden
  showSL (QIdentifierAs iden sort) =
    "(as " ++ showSL iden ++ " " ++ showSL sort ++ ")"

instance ShowSL FunDec where
  showSL (FunDec str srvs sort) =
    "(" ++ showSymbol str ++ " (" ++ joinA srvs ++ ") " ++ showSL sort ++ ")"

instance ShowSL AttrValue where
  showSL (AttrValueConstant spc) = showSL spc
  showSL (AttrValueSymbol str) = showSymbol str
  showSL (AttrValueSexpr sexprs) = "(" ++ joinA sexprs  ++ ")"

instance ShowSL Attribute where
  showSL (Attribute str) = str
  showSL (AttributeVal str attrVal) = str ++ " " ++ showSL attrVal

instance ShowSL Index where
  showSL (IndexNumeral i) = show i
  showSL (IndexSymbol str) = showSymbol str

instance ShowSL Identifier where
  showSL (ISymbol str) = showSymbol str
  showSL (I_Symbol str is) = "(_ " ++ showSymbol str ++ " " ++ joinA is  ++ ")"

instance ShowSL Sort where
  showSL (SortId iden) = showSL iden
  showSL (SortIdentifiers iden sorts) =
    "(" ++ showSL iden ++ " " ++ joinA sorts ++ ")"

instance ShowSL SpecConstant where
  showSL (SpecConstantNumeral n) = show n
  showSL (SpecConstantDecimal str) = str
  showSL (SpecConstantHexadecimal str) = "#x" ++ str
  showSL (SpecConstantBinary str)  = "#b" ++ str
  showSL (SpecConstantString str) = str

instance ShowSL Sexpr where
  showSL (SexprSpecConstant sc) = showSL sc
  showSL (SexprSymbol str) = showSymbol str
  showSL (SexprKeyword str) = str
  showSL (SexprSxp srps) = "(" ++ joinA srps ++ ")"


{-
   #########################################################################
   #                                                                       #
   #                             Command Response                          #
   #                                                                       #
   #########################################################################
-}

instance ShowSL CmdResponse where
  showSL (CmdGenResponse x) = showSL x
  showSL (CmdGetInfoResponse x) = "(" ++ joinA x ++ ")"
  showSL (CmdCheckSatResponse x) = showSL x
  showSL (CmdGetAssertionsResponse x) = "(" ++ joinA x ++ ")"
  showSL (CmdGetAssignmentResponse x) = "(" ++ joinA x ++ ")"
  showSL (CmdGetProofResponse x) = showSL x
  showSL (CmdGetUnsatCoreResponse x) = "(" ++ unwords (map showSymbol x) ++ ")"
  showSL (CmdGetUnsatAssumptionsResponse terms) = "(" ++  joinA terms ++ ")"
  showSL (CmdGetValueResponse x) = "(" ++ joinA x ++ ")"
  showSL (CmdGetModelResponse cmds) = "(" ++ joinA cmds ++ ")"
  showSL (CmdGetOptionResponse x) = showSL x
  showSL (CmdEchoResponse x) = x


instance ShowSL GenResponse where
  showSL Unsupported = "unsupported"
  showSL Success = "success"
  showSL (Error s) = "(error " ++ s ++ ")"

instance ShowSL ErrorBehavior where
  showSL ImmediateExit = "immediate-exit"
  showSL ContinuedExecution = "continued-execution"

instance ShowSL ReasonUnknown where
  showSL Memout = "memout"
  showSL Incomplete = "incomplete"

instance ShowSL CheckSatResponse where
  showSL Sat = "sat"
  showSL Unsat = "unsat"
  showSL Unknown = "unknown"

instance ShowSL InfoResponse where
  showSL (ResponseErrorBehavior x) = ":error-behavior " ++ showSL x
  showSL (ResponseName s) = ":name " ++ s
  showSL (ResponseAuthors s) = ":authors " ++ s
  showSL (ResponseVersion s) = ":version" ++ s
  showSL (ResponseReasonUnknown x) = ":reason-unknown " ++ showSL x
  showSL (ResponseAssertionStackLevels n) = ":assertion-stack-levels " ++ show n
  showSL (ResponseAttribute x)  = showSL x

instance ShowSL ValuationPair where
  showSL (ValuationPair term1 term2) =
    "(" ++ showSL term1 ++ " " ++ showSL term2 ++ ")"

instance ShowSL TValuationPair where
  showSL (TValuationPair str b) = "(" ++ showSymbol str ++ " " ++ showSL b ++ ")"
