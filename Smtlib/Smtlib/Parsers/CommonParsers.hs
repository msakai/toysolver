{-|
Module      : Smtlib.Parsers.CommandsParsers
Description : Common parsers for commands and responses.
Copyright   : Rogério Pontes 2015
License     : WTFPL
Maintainer  : rogerp62@outlook.com
Stability   : stable

This module contains some auxiliar parsers, used to parse commands or responses.
-}
module Smtlib.Parsers.CommonParsers where


{-
    In the String terminal, it does not parse C-style characters.
    Quoted Symbol does not parse all printable ASCII characters.
-}

import           Control.Applicative               as Ctr hiding ((<|>))
import           Data.Functor.Identity
import qualified Data.Set                          as Set
import           Text.Parsec.Prim                  as Prim
import           Text.ParserCombinators.Parsec     as Pc
import           Smtlib.Syntax.Syntax
import           Control.Monad

(<:>) :: Applicative f => f a -> f [a] -> f [a]
(<:>) a b = (:) <$> a <*> b

(<++>) :: Applicative f => f [a] -> f [a] -> f [a]
(<++>) a b = (++) <$> a <*> b

parseBool :: ParsecT String u Identity Bool
parseBool = (true *> return True) <|> (false *> return False)


-- Parse a Numeral

numeral :: ParsecT String u Identity String
numeral = many1 digit

num :: ParsecT String u Identity String
num = Pc.many digit
-- Parse a decimal

decimal :: ParsecT String u Identity String
decimal = numeral <++> dot <++> Pc.try zeros <++> num

zeros :: ParsecT String u Identity String
zeros = Pc.many $ char '0'


dot :: ParsecT String u Identity String
dot = string "."

-- parse a Hexadecimal

hexadecimal :: ParsecT String u Identity String
hexadecimal = string "#x" *> many1 hexDigit


--parsea a Binary
binary :: ParsecT String u Identity String
binary = string "#b" *> many1 bin

bin :: ParsecT String u Identity Char
bin = char '0' <|> char '1'


--parse a String
-- Dosent parse strings with escape characters
str :: ParsecT String u Identity String
str = string "\"" <++> liftM concat (Pc.many (liftM (\c -> [c]) strChar <|> Pc.try (string "\"\""))) <++> string "\""

strChar :: ParsecT String u Identity Char
strChar = (oneOf $ ['\t','\n','\r'] ++ [c | c <- [toEnum 32 .. toEnum 126], c /= '"']) <|> satisfy (toEnum 128 <=)


--parse a Symbol
symbol :: ParsecT String u Identity String
symbol = simpleSymbol <|> quotedSymbol

quotedSymbol :: ParsecT String u Identity String
quotedSymbol = char '|' *> Pc.many (noneOf "|")  <* char '|'

simpleSymbol :: ParsecT String u Identity String
simpleSymbol = Pc.try $ do
  s <- (letter <|> spcSymb) <:>  sq
  guard $ s `Set.notMember` reserved
  return s
  where
    sq = Pc.many (alphaNum <|> spcSymb)
    reserved = Set.fromList $
      ["BINARY", "DECIMAL", "HEXADECIMAL", "NUMERAL", "STRING", "_", "!", "as", "let", "exists", "forall", "par"] ++
      ["set-logic", "set-option", "set-info", "declare-sort", "define-sort", "declare-const", "declare-fun", "declare-fun-rec", "declare-funs-rec", "push", "pop", "reset", "reset-assertions", "assert", "check-sat", "check-sat-assuming", "get-assertions", "get-model", "get-proof", "get-unsat-core", "get-unsat-assumptions", "get-value", "get-assignment", "get-option", "get-info", "echo", "exit"]

spcSymb :: ParsecT String u Identity Char
spcSymb = oneOf  "+-/*=%?!.$_~^&<>@"

-- parse a key word
keyword :: ParsecT String u Identity String
keyword = char ':' <:> Pc.many (alphaNum<|> spcSymb)


aspO :: ParsecT String u Identity Char
aspO = char '('

aspC :: ParsecT String u Identity Char
aspC = char ')'

aspUS :: ParsecT String u Identity Char
aspUS = char '_'


true :: ParsecT String u Identity String
true = string "true"

false :: ParsecT String u Identity String
false = string "false"


emptySpace :: ParsecT String u Identity String
emptySpace = liftM concat $ Pc.try $ Pc.many emptySpaceSingle

emptySpace1 :: ParsecT String u Identity String
emptySpace1 = liftM concat $ Pc.try $ Pc.many1 emptySpaceSingle

emptySpaceSingle :: ParsecT String u Identity String
emptySpaceSingle = liftM (\c -> [c]) (char ' ' <|> char '\n' <|> char '\t' <|> char '\r') <|> comment

comment :: ParsecT String u Identity String
comment = char ';' <:> scan
  where
    scan  = do{ c <- char '\n' <|> char '\r'; return [c] }
          <|>
            do{ c <- anyChar; cs <- scan; return (c:cs) }

reservedWords :: ParsecT String u Identity String
reservedWords =  string "let"
             <|> string "par"
             <|> string "_"
             <|> string "!"
             <|> string "as"
             <|> string "forall"
             <|> string "exists"
             <|> string "NUMERAL"
             <|> string "DECIMAL"
             <|> string "STRING"




{-
   #########################################################################
   #                                                                       #
   #                          Parsers for Terms                            #
   #                                                                       #
   #########################################################################
-}


-- Term
parseTerm :: ParsecT String u Identity Term
parseTerm = parseTSPC
        <|> Pc.try parseTQID
        <|> Pc.try parseTQIT
        <|> Pc.try parseTermLet
        <|> Pc.try parseTermFA
        <|> Pc.try parseTermEX
        <|> parseTermAnnot

parseTSPC :: ParsecT String u Identity Term
parseTSPC = liftM TermSpecConstant parseSpecConstant

parseTQID :: ParsecT String u Identity Term
parseTQID = liftM TermQualIdentifier parseQualIdentifier

parseTQIT :: ParsecT String u Identity Term
parseTQIT = do
    _ <- aspO
    _ <- emptySpace
    iden <- parseQualIdentifier
    _ <- emptySpace
    terms <- Pc.many $ parseTerm <* Pc.try emptySpace
    _ <- aspC
    return $ TermQualIdentifierT iden terms

parseTermLet :: ParsecT String u Identity Term
parseTermLet = do
    _ <- aspO
    _ <- emptySpace
    _ <- string "let"
    _ <- emptySpace
    _ <- aspO
    _ <- emptySpace
    vb <- Pc.many $ parseVarBinding <* Pc.try emptySpace
    _ <- aspC
    _ <- emptySpace
    term <- parseTerm
    _ <- emptySpace
    _ <- aspC
    return $ TermLet vb term

parseTermFA :: ParsecT String u Identity Term
parseTermFA = do
    _ <- aspO
    _ <- emptySpace
    _ <- string "forall"
    _ <- emptySpace
    _ <- aspO
    sv <- Pc.many $ parseSortedVar <* Pc.try emptySpace
    _ <- aspC
    _ <- emptySpace
    term <- parseTerm
    _ <- emptySpace
    _ <- aspC
    return $ TermForall sv term


parseTermEX :: ParsecT String u Identity Term
parseTermEX = do
    _ <- aspO
    _ <- emptySpace
    _ <- string "exists"
    _ <- emptySpace
    _ <- aspO
    sv <- Pc.many $ parseSortedVar <* Pc.try emptySpace
    _ <- aspC
    _ <- emptySpace
    term <- parseTerm
    _ <- emptySpace
    _ <- aspC
    return $ TermExists sv term

parseTermAnnot :: ParsecT String u Identity Term
parseTermAnnot = do
  _ <- aspO
  _ <- emptySpace
  _ <- char '!'
  _ <- emptySpace
  term <- parseTerm
  _ <- emptySpace
  attr <- Pc.many $ parseAttribute <* Pc.try emptySpace
  _ <- aspC
  return $ TermAnnot term attr


-- -- Parse Sorted Var
parseSortedVar :: ParsecT String u Identity SortedVar
parseSortedVar = do
    _ <- aspO
    _ <- emptySpace
    symb <- symbol
    _ <- emptySpace
    sort <- parseSort
    _ <- emptySpace
    _ <- aspC
    return $ SV symb sort

-- -- Parse Qual identifier
parseQualIdentifier :: ParsecT String u Identity QualIdentifier
parseQualIdentifier = Pc.try parseQID <|> parseQIAs

parseQID :: ParsecT String u Identity QualIdentifier
parseQID = liftM QIdentifier parseIdentifier




parseQIAs :: ParsecT String u Identity QualIdentifier
parseQIAs = do
  _ <- aspO
  _ <- emptySpace
  _ <- string "as"
  _ <- emptySpace
  ident <- parseIdentifier
  _ <- emptySpace
  sort <- parseSort
  _ <- emptySpace
  _ <- aspC
  return $ QIdentifierAs ident sort


-- -- Parse Var Binding
parseVarBinding :: ParsecT String u Identity VarBinding
parseVarBinding = do
    _ <- aspO
    _ <- emptySpace
    symb <- symbol
    _ <- emptySpace
    term <- parseTerm
    _ <- emptySpace
    _ <- aspC
    return $ VB symb term





{-
   #########################################################################
   #                                                                       #
   #                          Parsers for Attributes                       #
   #                                                                       #
   #########################################################################
-}

--Parse Attribute Value
parseAttributeValue :: ParsecT String u Identity AttrValue
parseAttributeValue = parseAVSC <|> parseAVS <|> parseAVSexpr

parseAVSC :: ParsecT String u Identity AttrValue
parseAVSC = liftM AttrValueConstant parseSpecConstant

parseAVS :: ParsecT String u Identity AttrValue
parseAVS = liftM AttrValueSymbol symbol

parseAVSexpr :: ParsecT String u Identity AttrValue
parseAVSexpr = do
    _ <- aspO
    _ <- emptySpace
    expr <- Pc.many $ parseSexpr <* Pc.try emptySpace
    _ <- aspC
    return $ AttrValueSexpr expr



-- Parse Attribute

parseAttribute :: ParsecT String u Identity Attribute
parseAttribute =  Pc.try parseKeyAttAttribute <|> parseKeyAttribute


parseKeyAttribute :: ParsecT String u Identity Attribute
parseKeyAttribute = liftM  Attribute keyword

parseKeyAttAttribute :: ParsecT String u Identity Attribute
parseKeyAttAttribute = do
  kw <- keyword
  _ <- emptySpace
  atr <- parseAttributeValue
  return $ AttributeVal kw atr


{-
   #########################################################################
   #                                                                       #
   #                          Parsers Sort                                 #
   #                                                                       #
   #########################################################################
-}

-- Parse Sot

parseSort :: ParsecT String u Identity Sort
parseSort = Pc.try parseIdentifierS <|> parseIdentifierSort

parseIdentifierS :: ParsecT String u Identity Sort
parseIdentifierS = liftM SortId parseIdentifier

parseIdentifierSort :: ParsecT String u Identity Sort
parseIdentifierSort = do
    _ <- aspO
    _ <- emptySpace
    identifier <- parseIdentifier
    _ <- emptySpace
    sorts <- many1 (parseSort  <* Pc.try emptySpace)
    _ <- aspC
    return $ SortIdentifiers identifier sorts




{-
   #########################################################################
   #                                                                       #
   #                          Parsers Identifiers                          #
   #                                                                       #
   #########################################################################
-}


-- Parse Identifiers

parseIdentifier :: ParsecT String u Identity Identifier
parseIdentifier = parseOnlySymbol <|> parseNSymbol

parseOnlySymbol :: ParsecT String u Identity Identifier
parseOnlySymbol = liftM ISymbol symbol

parseNSymbol :: ParsecT String u Identity Identifier
parseNSymbol = do
       _ <- aspO
       _ <- emptySpace
       _ <- aspUS
       _ <- emptySpace1
       symb <- symbol
       _ <- emptySpace
       indexes <- many1 ((liftM (IndexNumeral . read) numeral <|> liftM IndexSymbol symbol) <* Pc.try spaces)
       _ <- aspC
       return $ I_Symbol symb indexes

{-
   #########################################################################
   #                                                                       #
   #                          Parsers S-exprs                              #
   #                                                                       #
   #########################################################################
-}


-- parse S-expressions

parseSexprConstant :: ParsecT String u Identity Sexpr
parseSexprConstant = liftM SexprSpecConstant parseSpecConstant

parseSexprSymbol :: ParsecT String u Identity Sexpr
parseSexprSymbol = liftM SexprSymbol symbol

parseSexprKeyword :: ParsecT String u Identity Sexpr
parseSexprKeyword = liftM SexprKeyword keyword

parseAtomSexpr :: ParsecT String u Identity Sexpr
parseAtomSexpr = parseSexprConstant
          <|> parseSexprSymbol
          <|> parseSexprKeyword


parseListSexpr :: ParsecT String u Identity Sexpr
parseListSexpr = do
    _ <- aspO
    list <- Pc.many parseSexpr
    _ <- aspC
    return $ SexprSxp  list



parseSexpr :: ParsecT String u Identity Sexpr
parseSexpr = do
  _ <- emptySpace
  expr <- parseAtomSexpr <|> parseListSexpr
  _ <- emptySpace
  return expr



-- parse Spec Constant
parseSpecConstant :: ParsecT String u Identity SpecConstant
parseSpecConstant = Pc.try parseDecimal
                <|> parseNumeral
                <|> Pc.try parseHexadecimal
                <|> parseBinary
                <|> parseString



parseNumeral :: ParsecT String u Identity SpecConstant
parseNumeral = liftM SpecConstantNumeral (read  <$> numeral)

parseDecimal :: ParsecT String u Identity SpecConstant
parseDecimal = liftM SpecConstantDecimal decimal

parseHexadecimal :: ParsecT String u Identity SpecConstant
parseHexadecimal = liftM SpecConstantHexadecimal hexadecimal

parseBinary :: ParsecT String u Identity SpecConstant
parseBinary = liftM SpecConstantBinary binary

parseString :: ParsecT String u Identity SpecConstant
parseString = liftM SpecConstantString str
