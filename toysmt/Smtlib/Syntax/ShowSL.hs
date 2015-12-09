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

import           Data.List
import           Smtlib.Syntax.Syntax





joinA ::(ShowSL a) => [a] -> String
joinA = unwords.fmap showSL

joinNs :: [Int] -> String
joinNs = unwords.fmap show


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
  showSL (SetLogic s) = "(set-logic " ++ s ++ ")"
  showSL (SetOption opt) = "(set-option " ++ showSL opt ++ ")"
  showSL (SetInfo info) = "(set-info " ++ showSL info ++ ")"
  showSL (DeclareSort str val) =  "(declare-sort " ++ str ++
    " " ++ show val ++ ")"
  showSL (DefineSort str strs sort) = "(define-sort " ++ str ++
    " (" ++ unwords strs ++ ") " ++ showSL sort ++ ") "
  showSL (DeclareFun  str sorts sort) = "(declare-fun  " ++ str ++
    " ("  ++ joinA sorts ++ ") " ++ showSL sort ++ ") "
  showSL (DefineFun str srvs sort term) = "( define-fun "   ++ str ++
    " (" ++ joinA srvs ++ ") " ++ showSL sort ++ " " ++ showSL term ++ ")"
  showSL (Push n) = "(push " ++ show n ++ ")"
  showSL (Pop n) = "(pop " ++show n ++ ")"
  showSL (Assert term) = "(assert " ++ showSL term ++ ")"
  showSL CheckSat = "(check-sat)"
  showSL (CheckSatAssuming terms) = "(check-sat-assuming (" ++ joinA terms ++ "))"
  showSL GetAssertions = "(get-assertions)"
  showSL GetProof = "(get-proof)"
  showSL GetUnsatCore = "(get-unsat-core)"
  showSL GetUnsatAssumptions = "(get-unsat-assumptions)"
  showSL (GetValue terms) = "( (" ++ joinA terms ++ ") )"
  showSL GetAssignment =  "(get-assignment)"
  showSL (GetOption opt) = "(get-option " ++ opt ++ ")"
  showSL (GetInfo info) = "(get-info " ++ showSL info ++ ")"
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
  showSL (RegularOutputChannel s) = ":regular-output-channel " ++ s
  showSL (DiagnosticOutputChannel s) = ":diagnostic-output-channel " ++ s
  showSL (RandomSeed n) = ":random-seed " ++ show n
  showSL (Verbosity n) = ":verbosity'" ++ show n
  showSL (OptionAttr attr) = show attr

instance ShowSL InfoFlags where
  showSL ErrorBehavior = ":error-behavior"
  showSL Name = ":name"
  showSL Authors = ":authors"
  showSL Version = ":version"
  showSL Status = ":status"
  showSL ReasonUnknown = ":reason-unknown"
  showSL AllStatistics = ":all-statistics"
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
  showSL (VB str term) = "("++ str ++ " " ++ showSL term ++ ")"

instance ShowSL SortedVar where
  showSL (SV str sort)  = "(" ++ str ++ " " ++ showSL sort ++ ")"

instance ShowSL QualIdentifier where
  showSL (QIdentifier iden) = showSL iden
  showSL (QIdentifierAs iden sort) =
    "(as " ++ showSL iden ++ " " ++ showSL sort ++ ")"

instance ShowSL AttrValue where
  showSL (AttrValueConstant spc) = showSL spc
  showSL (AttrValueSymbol str) = str
  showSL (AttrValueSexpr sexprs) = "(" ++ joinA sexprs  ++ ")"

instance ShowSL Attribute where
  showSL (Attribute str) = str
  showSL (AttributeVal str attrVal) = str ++ " " ++ showSL attrVal

instance ShowSL Identifier where
  showSL (ISymbol str) = str
  showSL (I_Symbol str ns) = "( _ " ++ str ++ " " ++ joinNs ns  ++ ")"

instance ShowSL Sort where
  showSL (SortId iden) = showSL iden
  showSL (SortIdentifiers iden sorts) =
    "(" ++ showSL iden ++ " " ++ joinA sorts ++ ")"

instance ShowSL SpecConstant where
  showSL (SpecConstantNumeral n) = show n
  showSL (SpecConstantDecimal str) = str
  showSL (SpecConstantHexadecimal str) = str
  showSL (SpecConstantBinary str)  = str
  showSL (SpecConstantString str) = str

instance ShowSL Sexpr where
  showSL (SexprSpecConstant sc) = showSL sc
  showSL (SexprSymbol str) = str
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
  showSL (CmdGetUnsatCoreResponse x) = "(" ++ unwords x ++ ")"
  showSL (CmdGetUnsatAssumptionsResponse terms) = "(" ++  joinA terms ++ ")"
  showSL (CmdGetValueResponse x) = "(" ++ joinA x ++ ")"
  showSL (CmdGetOptionResponse x) = showSL x


instance ShowSL GenResponse where
  showSL Unsupported = "unsupported"
  showSL Success = "success"
  showSL (Error s) = "(error " ++ s ++ ")"

instance ShowSL ErrorBehavior where
  showSL ImmediateExit = "immediate-exit"
  showSL ContinuedExecution = "continued-execution"

instance ShowSL ReasonUnknown where
  showSL Memout = "memout"
  showSL Incomplete = "imcomplete"

instance ShowSL CheckSatResponse where
  showSL Sat = "sat"
  showSL Unsat = "unsat"
  showSL Unknown = "unknown"

instance ShowSL InfoResponse where
  showSL (ResponseErrorBehavior x) = ":error-behaviour " ++ showSL x
  showSL (ResponseName s) = ":name " ++ s
  showSL (ResponseAuthors s) = ":authors " ++ s
  showSL (ResponseVersion s) = ":version" ++ s
  showSL (ResponseReasonUnknown x) = ":reason-unknown " ++ showSL x
  showSL (ResponseAttribute x)  = showSL x

instance ShowSL ValuationPair where
  showSL (ValuationPair term1 term2) =
    "(" ++ showSL term1 ++ " " ++ showSL term2 ++ ")"

instance ShowSL TValuationPair where
  showSL (TValuationPair str b) = "(" ++ str ++ " " ++ showSL b ++ ")"
