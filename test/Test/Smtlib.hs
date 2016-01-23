{-# OPTIONS_GHC -Wall -fno-warn-orphans #-}
{-# LANGUAGE TemplateHaskell, ScopedTypeVariables #-}
module Test.Smtlib (smtlibTestGroup) where

import Control.Applicative
import Control.Monad
import qualified Data.Set as Set

import Test.Tasty
import Test.Tasty.QuickCheck hiding (Success)
import Test.Tasty.HUnit
import Test.Tasty.TH

import Smtlib.Syntax.Syntax
import Smtlib.Syntax.ShowSL
import Smtlib.Parsers.CommonParsers
import Smtlib.Parsers.CommandsParsers
import Smtlib.Parsers.ResponseParsers
import Text.Parsec (parse, ParseError)

import Debug.Trace

prop_parseTerm :: Property
prop_parseTerm = forAll arbitrary $ \(t :: Term) ->
  parse parseTerm "" (showSL t) == Right t

prop_parseAttribute :: Property
prop_parseAttribute = forAll arbitrary $ \a ->
  parse parseAttribute "" (showSL a) == Right a

prop_parseSort :: Property
prop_parseSort = forAll arbitrary $ \s ->
  parse parseSort "" (showSL s) == Right s

prop_parseIdentifier :: Property
prop_parseIdentifier = forAll arbitrary $ \a ->
  parse parseIdentifier "" (showSL a) == Right a

prop_parseSexpr :: Property
prop_parseSexpr = forAll arbitrary $ \a ->
  parse parseSexpr "" (showSL a) == Right a

prop_parseSpecConstant :: Property
prop_parseSpecConstant = forAll arbitrary $ \a ->
  parse parseSpecConstant "" (showSL a) == Right a

prop_parseCommand :: Property
prop_parseCommand = forAll arbitrary $ \a ->
  parse parseCommand "" (showSL a) == Right a

prop_parseOption :: Property
prop_parseOption = forAll arbitrary $ \a ->
  parse parseOption "" (showSL a) == Right a

prop_parseInfoFlags :: Property
prop_parseInfoFlags = forAll arbitrary $ \a ->
  parse parseOption "" (showSL a) == Right a

-- prop_parseCmdResult :: Property
-- prop_parseCmdResult = forAll arbitrary $ \a ->
--   parse parseCmdResult "" (showSL a) == Right a

prop_parseGenResponse :: Property
prop_parseGenResponse = forAll arbitrary $ \a ->
  parse parseGenResponse "" (showSL a) == Right a

prop_parseGetInfoResponse :: Property
prop_parseGetInfoResponse = forAll arbitrary $ \a ->  
  parse parseGetInfoResponse "" ("(" ++ joinA a ++ ")") == Right a

prop_parseCheckSatResponse :: Property
prop_parseCheckSatResponse = forAll arbitrary $ \a ->
  parse parseCheckSatResponse "" (showSL a) == Right a

prop_parseGetAssertionsResponse :: Property
prop_parseGetAssertionsResponse = forAll genGetAssertionsResponse $ \a ->
  parse parseGetAssertionsResponse "" ("(" ++ joinA a ++ ")") == Right a

prop_parseGetAssignmentResp :: Property
prop_parseGetAssignmentResp = forAll arbitrary $ \a ->
  parse parseGetAssignmentResp "" ("(" ++ joinA a ++ ")") == Right a

prop_parseGetProofResponse :: Property
prop_parseGetProofResponse = forAll arbitrary $ \a ->
  parse parseGetProofResponse "" (showSL a) == Right a

prop_parseGetUnsatCoreResp :: Property
prop_parseGetUnsatCoreResp = forAll genGetUnsatCoreResponse $ \a ->
  parse parseGetUnsatCoreResp "" ("(" ++ unwords (fmap showSymbol a) ++ ")") == Right a

prop_parseGetUnsatAssumptionsResp :: Property
prop_parseGetUnsatAssumptionsResp = forAll (listOf' genSymbol) $ \a ->
  parse parseGetUnsatCoreResp "" ("(" ++ unwords (fmap showSymbol a) ++ ")") == Right a

prop_parseGetValueResponse :: Property
prop_parseGetValueResponse = forAll genGetValueResponse $ \a ->
  parse parseGetValueResponse "" ("(" ++ joinA a ++ ")") == Right a

prop_parseGetModelResponse :: Property
prop_parseGetModelResponse = forAll genGetModelResponse $ \a ->
  parse parseGetModelResponse "" ("(" ++ joinA a ++ ")") == Right a

prop_parseGetOptionResponse :: Property
prop_parseGetOptionResponse = forAll arbitrary $ \a ->
  parse parseGetOptionResponse "" (showSL a) == Right a

prop_parseEchoResponse :: Property
prop_parseEchoResponse = forAll genEchoResponse $ \a ->
  parse parseEchoResponse "" a == Right a

case_bug_1 :: Assertion
case_bug_1 = do
  parse parseSort "" "(_a b)" @?= Right (SortIdentifiers (ISymbol "_a") [SortId (ISymbol "b")])
  parse parseTerm "" "(_a b)" @?= Right (TermQualIdentifierT (QIdentifier (ISymbol "_a")) [TermQualIdentifier (QIdentifier (ISymbol "b"))])

case_parse_string_literal_ascii :: Assertion
case_parse_string_literal_ascii = parse str "" s @?= Right s
  where
    s = showStringLiteral $ ['\t','\n','\r'] ++ [toEnum 32 .. toEnum 126]

prop_parse_string_literal :: Property
prop_parse_string_literal =
  forAll genStringLiteral $  \s ->
    parse str "" s == Right s

case_parseSexprKeyword_bug :: Assertion
case_parseSexprKeyword_bug = 
  parse parseSexprKeyword "" ":keyword" @?= Right (SexprKeyword ":keyword")

case_parseHexadecimal :: Assertion
case_parseHexadecimal = parse parseHexadecimal "" (showSL s) @?= Right s
  where
    s = SpecConstantHexadecimal "afbf00"

case_parseBinary :: Assertion
case_parseBinary = parse parseBinary "" (showSL s) @?= Right s
  where
    s = SpecConstantBinary "011001"

-- ---------------------------------------------------------------------

instance Arbitrary Term where
  arbitrary = sized $ \n -> oneof $
    [ TermSpecConstant <$> arbitrary
    , TermQualIdentifier <$> arbitrary
    ] ++ (if n > 0 then gs else [])
    where
      gs = 
        [ liftM2 TermQualIdentifierT arbitrary (listOf1' arbitrary')
        , liftM2 TermLet (listOf1' arbitrary) arbitrary'
        , liftM2 TermForall (listOf1' arbitrary) arbitrary'
        , liftM2 TermExists (listOf1' arbitrary) arbitrary'
        , liftM2 TermAnnot arbitrary' (listOf1' arbitrary)
        ]

instance Arbitrary VarBinding where
  arbitrary = liftM2 VB genSymbol arbitrary'

instance Arbitrary SortedVar where
  arbitrary = liftM2 SV genSymbol arbitrary

instance Arbitrary AttrValue where
  arbitrary = oneof
    [ AttrValueConstant <$> arbitrary
    , AttrValueSymbol <$> genSymbol
    , AttrValueSexpr <$> listOf' arbitrary
    ]
   
instance Arbitrary Attribute where
  arbitrary = oneof
    [ Attribute <$> genKeyword
    , liftM2 AttributeVal genKeyword arbitrary
    ]

instance Arbitrary QualIdentifier where
  arbitrary = oneof
    [ QIdentifier <$> arbitrary
    , liftM2 QIdentifierAs arbitrary arbitrary
    ]
   
instance Arbitrary Index where
  arbitrary = oneof
    [ IndexNumeral <$> abs <$> arbitrary
    , IndexSymbol <$> genSymbol
    ]

instance Arbitrary Identifier where
  arbitrary = oneof
    [ ISymbol <$> genSymbol
    , liftM2 I_Symbol genSymbol (listOf1' arbitrary)
    ]

instance Arbitrary Sort where
  arbitrary = oneof
    [ SortId <$> arbitrary
    , liftM2 SortIdentifiers arbitrary (listOf1' arbitrary')
    ]

instance Arbitrary SpecConstant where
  arbitrary = oneof
    [ SpecConstantNumeral <$> abs <$> arbitrary
    , liftM SpecConstantDecimal $ do
        a <- show <$> abs <$> (arbitrary :: Gen Int)
        b <- listOf $ return '0'
        c <- show <$> abs <$> (arbitrary :: Gen Int)
        return $ a ++ "." ++ b ++ c
    , SpecConstantHexadecimal <$> listOf1 (elements (['0'..'9'] ++ ['a'..'f'] ++ ['A'..'F']))
    , SpecConstantBinary <$> listOf1 (elements ['0','1'])
    , liftM SpecConstantString $ do
        let p c = c `elem` ['\t','\n','\r'] || (32 <= fromEnum c && fromEnum c <= 126) || 128 <= fromEnum c
        s <- listOf $ arbitrary `suchThat` p
        return $ "\"" ++ concat [if c == '"' then "\"\"" else [c] | c <- s] ++ "\""
    ]
   
instance Arbitrary Sexpr where
  arbitrary = sized $ \n -> oneof $
    [ SexprSpecConstant <$> arbitrary
    , SexprSymbol <$> genSymbol
    , SexprKeyword <$> genKeyword
    ] ++
    [ liftM SexprSxp $ listOf' arbitrary' | n > 0 ]

halve :: Gen a -> Gen a
halve g = sized (\n -> resize (n `div` 2) g)

arbitrary' :: Arbitrary a => Gen a
arbitrary' = halve arbitrary

listOf' :: Gen a -> Gen [a]
listOf' g = do
  n <- frequency [(6, return 0), (3, return 1), (1, return 2)]
  replicateM n g

listOf1' :: Gen a -> Gen [a]
listOf1' g = do
  n <- frequency [(10, return 1), (4, return 2), (1, return 3)]
  replicateM n g

-- ---------------------------------------------------------------------

type Symbol = String

genSymbol :: Gen Symbol
genSymbol = oneof [genSimpleSymbol, genQuotedSymbol]

genSimpleSymbol :: Gen Symbol
genSimpleSymbol = g `suchThat` (`Set.notMember` reserved)
  where
    xs = ['a'..'z']++['A'..'Z']++"~!@$%^&*_-+=<>.?/"
    g = liftM2 (:) (elements xs) (listOf1 $ elements $ ['0'..'9'] ++ xs)
    reserved = Set.fromList $
      ["BINARY", "DECIMAL", "HEXADECIMAL", "NUMERAL", "STRING", "_", "!", "as", "let", "exists", "forall", "par"] ++
      ["set-logic", "set-option", "set-info", "declare-sort", "define-sort", "declare-const", "declare-fun", "declare-fun-rec", "declare-funs-rec", "push", "pop", "reset", "reset-assertions", "assert", "check-sat", "check-sat-assuming", "get-assertions", "get-model", "get-proof", "get-unsat-core", "get-unsat-assumptions", "get-value", "get-assignment", "get-option", "get-info", "echo", "exit"]

genQuotedSymbol :: Gen Symbol
genQuotedSymbol = listOf1 g
  where
    g :: Gen Char
    g = oneof [elements (Set.toList xs), choose (toEnum 128, maxBound)]
    xs = Set.fromList (['\t','\n','\r'] ++ [' ' .. toEnum 126]) `Set.difference` Set.fromList ['\\', '|']    

genKeyword :: Gen String
genKeyword = (':':) <$> genSimpleSymbol

genStringLiteral :: Gen String
genStringLiteral = showStringLiteral <$> listOf genStringChar

showStringLiteral :: String -> String
showStringLiteral s = "\"" ++ concat [if c == '"' then "\"\"" else [c] | c <- s] ++ "\""

genStringChar :: Gen Char
genStringChar = arbitrary `suchThat` p
   where
    p c = c `elem` ['\t','\n','\r'] || (32 <= fromEnum c && fromEnum c <= 126) || 128 <= fromEnum c

-- ---------------------------------------------------------------------

instance Arbitrary Command where
  arbitrary = oneof
    [ SetLogic <$> genSymbol
    , SetOption <$> arbitrary
    , SetInfo <$> arbitrary
    , DeclareSort <$> genSymbol <*> (abs <$> arbitrary)
    , DefineSort <$> genSymbol <*> listOf' genSymbol <*> arbitrary
    , DeclareConst <$> genSymbol <*> arbitrary
    , DeclareFun <$> genSymbol <*> listOf' arbitrary <*> arbitrary
    , DefineFun <$> genSymbol <*> listOf' arbitrary <*> arbitrary <*> arbitrary
    , DefineFunRec <$> genSymbol <*> listOf' arbitrary <*> arbitrary <*> arbitrary
    , DefineFunsRec <$> listOf1' arbitrary <*> listOf1' arbitrary
    , Push <$> (abs <$> arbitrary)
    , Pop <$> (abs <$> arbitrary)
    , return Reset
    , return ResetAssertions
    , Assert <$> arbitrary
    , return CheckSat
    , CheckSatAssuming <$> listOf' arbitrary
    , return GetAssertions
    , return GetModel
    , return GetProof
    , return GetUnsatCore
    , return GetUnsatAssumptions
    , GetValue <$> listOf1' arbitrary
    , return GetAssignment
    , GetOption <$> genKeyword
    , GetInfo <$> arbitrary
    , Echo <$> genStringLiteral
    , return Exit
    ]

instance Arbitrary Option where
  arbitrary = oneof
    [ PrintSuccess <$> arbitrary
    , ExpandDefinitions <$> arbitrary
    , InteractiveMode <$> arbitrary
    , ProduceProofs <$> arbitrary
    , ProduceUnsatCores <$> arbitrary
    , ProduceUnsatAssumptions <$> arbitrary
    , ProduceModels <$> arbitrary
    , ProduceAssignments <$> arbitrary
    , ProduceAssertions <$> arbitrary
    , GlobalDeclarations <$> arbitrary
    , RegularOutputChannel <$> genStringLiteral
    , DiagnosticOutputChannel <$> genStringLiteral
    , RandomSeed <$> (abs <$> arbitrary)
    , Verbosity <$> abs <$> arbitrary
    , ReproducibleResourceLimit <$> abs <$> arbitrary
    , OptionAttr <$> arbitrary
    ]

instance Arbitrary InfoFlags where
  arbitrary = oneof
    [ return ErrorBehavior
    , return Name
    , return Authors
    , return Version
    , return Status
    , return ReasonUnknown
    , return AllStatistics
    , return AssertionStackLevels
    , InfoFlags <$> genKeyword
    ]

instance Arbitrary FunDec where
  arbitrary = FunDec <$> genSymbol <*> listOf' arbitrary <*> arbitrary

-- ---------------------------------------------------------------------

instance Arbitrary CmdResponse where
  arbitrary = oneof
    [ CmdGenResponse <$> arbitrary
    , CmdGetInfoResponse <$> arbitrary
    , CmdCheckSatResponse <$> arbitrary
    , CmdGetAssertionsResponse <$> genGetAssertionsResponse
    , CmdGetAssignmentResponse <$> arbitrary
    , CmdGetProofResponse <$> arbitrary
    , CmdGetUnsatCoreResponse <$> genGetUnsatCoreResponse
    , CmdGetUnsatAssumptionsResponse <$> arbitrary
    , CmdGetValueResponse <$> genGetValueResponse
    , CmdGetModelResponse <$> arbitrary
    , CmdGetOptionResponse <$> arbitrary
    , CmdEchoResponse <$> genEchoResponse
    ]

instance Arbitrary GenResponse where
  arbitrary = oneof 
    [ return Unsupported
    , return Success
    , Error <$> genStringLiteral
    ]

instance Arbitrary ErrorBehavior where
  arbitrary = elements [ImmediateExit, ContinuedExecution]

instance Arbitrary ReasonUnknown where
  arbitrary = elements [Memout, Incomplete]

instance Arbitrary CheckSatResponse where
  arbitrary = elements [Sat, Unsat, Unknown]

instance Arbitrary InfoResponse where 
  arbitrary = oneof
    [ ResponseErrorBehavior <$> arbitrary
    , ResponseName <$> genStringLiteral
    , ResponseAuthors <$> genStringLiteral
    , ResponseVersion <$> genStringLiteral
    , ResponseReasonUnknown <$> arbitrary
    , ResponseAssertionStackLevels <$> abs <$> arbitrary
    , ResponseAttribute <$> arbitrary
    ]

genGetAssertionsResponse :: Gen [Term]
genGetAssertionsResponse = listOf' arbitrary

genGetUnsatCoreResponse :: Gen [Symbol]
genGetUnsatCoreResponse = listOf' genSymbol

genGetValueResponse :: Gen [ValuationPair]
genGetValueResponse = listOf' arbitrary

genGetModelResponse :: Gen [Command]
genGetModelResponse = listOf1' $ oneof
  [ DefineFun <$> genSymbol <*> listOf' arbitrary <*> arbitrary <*> arbitrary
  , DefineFunRec <$> genSymbol <*> listOf' arbitrary <*> arbitrary <*> arbitrary
  , DefineFunsRec <$> listOf1' arbitrary <*> listOf1' arbitrary
  ]

genEchoResponse :: Gen String
genEchoResponse = genStringLiteral

instance Arbitrary ValuationPair where
  arbitrary = ValuationPair <$> arbitrary <*> arbitrary

instance Arbitrary TValuationPair where
  arbitrary = TValuationPair <$> genSymbol <*> arbitrary

-- ---------------------------------------------------------------------
-- Test harness

smtlibTestGroup :: TestTree
smtlibTestGroup = $(testGroupGenerator)
