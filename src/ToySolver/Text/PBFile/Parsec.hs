{-# LANGUAGE BangPatterns #-}
{-# OPTIONS_GHC -Wall #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.Text.PBFile.Parsec
-- Copyright   :  (c) Masahiro Sakai 2011-2015
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Portability :  non-portable (BangPatterns)
--
-- A parser library for .opb file and .wbo files used by PB Competition.
-- 
-- References:
--
-- * Input/Output Format and Solver Requirements for the Competitions of
--   Pseudo-Boolean Solvers
--   <http://www.cril.univ-artois.fr/PB11/format.pdf>
--
-----------------------------------------------------------------------------

module ToySolver.Text.PBFile.Parsec
  (
  -- * Parsing .opb files
    parseOPBString
  , parseOPBFile

  -- * Parsing .wbo files
  , parseWBOString
  , parseWBOFile
  ) where

import Prelude hiding (sum)
import Control.Monad
import Data.Maybe
import Text.Parsec
import Text.Parsec.String
import ToySolver.Text.PBFile.Types
import ToySolver.Internal.TextUtil

-- <formula>::= <sequence_of_comments> [<objective>] <sequence_of_comments_or_constraints>
formula :: Parser Formula
formula = do
  h <- optionMaybe hint
  sequence_of_comments
  obj <- optionMaybe objective
  cs <- sequence_of_comments_or_constraints
  return $
    Formula
    { pbObjectiveFunction = obj
    , pbConstraints = cs
    , pbNumVars = fromMaybe (pbComputeNumVars obj cs) (fmap fst h)
    , pbNumConstraints = fromMaybe (length cs) (fmap snd h)
    }

hint :: Parser (Int,Int)
hint = try $ do
  _ <- char '*'
  zeroOrMoreSpace
  _ <- string "#variable="
  zeroOrMoreSpace
  nv <- unsigned_integer
  oneOrMoreSpace  
  _ <- string "#constraint="
  zeroOrMoreSpace
  nc <- unsigned_integer
  _ <- manyTill anyChar eol
  return (fromIntegral nv, fromIntegral nc)

-- <sequence_of_comments>::= <comment> [<sequence_of_comments>]
sequence_of_comments :: Parser ()
sequence_of_comments = skipMany comment -- XXX: we allow empty sequence

-- <comment>::= "*" <any_sequence_of_characters_other_than_EOL> <EOL>
comment :: Parser ()
comment = do
  _ <- char '*' 
  _ <- manyTill anyChar eol
  return ()

-- <sequence_of_comments_or_constraints>::= <comment_or_constraint> [<sequence_of_comments_or_constraints>]
sequence_of_comments_or_constraints :: Parser [Constraint]
sequence_of_comments_or_constraints = do
  xs <- many1 comment_or_constraint
  return $ catMaybes xs

-- <comment_or_constraint>::= <comment>|<constraint>
comment_or_constraint :: Parser (Maybe Constraint)
comment_or_constraint =
  (comment >> return Nothing) <|> (liftM Just constraint)

-- <objective>::= "min:" <zeroOrMoreSpace> <sum> ";"
objective :: Parser Sum
objective = do
  _ <- string "min:"
  zeroOrMoreSpace
  obj <- sum
  _ <- char ';'
  eol
  return obj

-- <constraint>::= <sum> <relational_operator> <zeroOrMoreSpace> <integer> <zeroOrMoreSpace> ";"
constraint :: Parser Constraint
constraint = do
  lhs <- sum
  op <- relational_operator
  zeroOrMoreSpace
  rhs <- integer
  zeroOrMoreSpace
  semi
  return (lhs, op, rhs)

-- <sum>::= <weightedterm> | <weightedterm> <sum>
sum :: Parser Sum
sum = many1 weightedterm

-- <weightedterm>::= <integer> <oneOrMoreSpace> <term> <oneOrMoreSpace>
weightedterm :: Parser WeightedTerm
weightedterm = do
  w <- integer
  oneOrMoreSpace
  t <- term
  oneOrMoreSpace
  return (w,t)

-- <integer>::= <unsigned_integer> | "+" <unsigned_integer> | "-" <unsigned_integer>
integer :: Parser Integer
integer = msum
  [ unsigned_integer
  , char '+' >> unsigned_integer
  , char '-' >> liftM negate unsigned_integer
  ]

-- <unsigned_integer>::= <digit> | <digit><unsigned_integer>
unsigned_integer :: Parser Integer
unsigned_integer = do
  ds <- many1 digit
  return $! readUnsignedInteger ds

-- <relational_operator>::= ">=" | "="
relational_operator :: Parser Op
relational_operator = (string ">=" >> return Ge) <|> (string "=" >> return Eq)

-- <variablename>::= "x" <unsigned_integer>
variablename :: Parser Var
variablename = do
  _ <- char 'x'
  i <- unsigned_integer
  return $! fromIntegral i

-- <oneOrMoreSpace>::= " " [<oneOrMoreSpace>]
oneOrMoreSpace :: Parser ()
oneOrMoreSpace  = skipMany1 (char ' ')

-- <zeroOrMoreSpace>::= [" " <zeroOrMoreSpace>]
zeroOrMoreSpace :: Parser ()
zeroOrMoreSpace = skipMany (char ' ')

eol :: Parser ()
eol = char '\n' >> return ()

semi :: Parser ()
semi = char ';' >> eol

{-
For linear pseudo-Boolean instances, <term> is defined as
<term>::=<variablename>

For non-linear instances, <term> is defined as
<term>::= <oneOrMoreLiterals>
-}
term :: Parser Term
term = oneOrMoreLiterals

-- <oneOrMoreLiterals>::= <literal> | <literal> <oneOrMoreSpace> <oneOrMoreLiterals>
oneOrMoreLiterals :: Parser [Lit]
oneOrMoreLiterals = do
  l <- literal
  mplus (try $ oneOrMoreSpace >> liftM (l:) (oneOrMoreLiterals)) (return [l])
-- Note that we cannot use sepBy1.
-- In "p `sepBy1` q", p should success whenever q success.
-- But it's not the case here.

-- <literal>::= <variablename> | "~"<variablename>
literal :: Parser Lit
literal = variablename <|> (char '~' >> liftM negate variablename)

-- | Parse a .opb file containing pseudo boolean problem.
parseOPBString :: SourceName -> String -> Either ParseError Formula
parseOPBString = parse formula

-- | Parse a .opb format string containing pseudo boolean problem.
parseOPBFile :: FilePath -> IO (Either ParseError Formula)
parseOPBFile = parseFromFile formula


-- <softformula>::= <sequence_of_comments> <softheader> <sequence_of_comments_or_constraints>
softformula :: Parser SoftFormula
softformula = do
  h <- optionMaybe hint
  sequence_of_comments
  top <- softheader
  cs <- wbo_sequence_of_comments_or_constraints
  return $
    SoftFormula
    { wboTopCost = top
    , wboConstraints = cs
    , wboNumVars = fromMaybe (wboComputeNumVars cs) (fmap fst h)
    , wboNumConstraints = fromMaybe (length cs) (fmap snd h)
    }

-- <softheader>::= "soft:" [<unsigned_integer>] ";"
softheader :: Parser (Maybe Integer)
softheader = do
  _ <- string "soft:"
  zeroOrMoreSpace -- XXX
  top <- optionMaybe unsigned_integer
  zeroOrMoreSpace -- XXX
  semi
  return top

-- <sequence_of_comments_or_constraints>::= <comment_or_constraint> [<sequence_of_comments_or_constraints>]
wbo_sequence_of_comments_or_constraints :: Parser [SoftConstraint]
wbo_sequence_of_comments_or_constraints = do
  xs <- many1 wbo_comment_or_constraint
  return $ catMaybes xs

-- <comment_or_constraint>::= <comment>|<constraint>|<softconstraint>
wbo_comment_or_constraint :: Parser (Maybe SoftConstraint)
wbo_comment_or_constraint = (comment >> return Nothing) <|> m
  where
    m = liftM Just $ (constraint >>= \c -> return (Nothing, c)) <|> softconstraint

-- <softconstraint>::= "[" <zeroOrMoreSpace> <unsigned_integer> <zeroOrMoreSpace> "]" <constraint>
softconstraint :: Parser SoftConstraint
softconstraint = do
  _ <- char '['
  zeroOrMoreSpace
  cost <- unsigned_integer
  zeroOrMoreSpace
  _ <- char ']'
  zeroOrMoreSpace -- XXX
  c <- constraint
  return (Just cost, c)

-- | Parse a .wbo file containing weighted boolean optimization problem.
parseWBOString :: SourceName -> String -> Either ParseError SoftFormula
parseWBOString = parse softformula

-- | Parse a .wbo format string containing weighted boolean optimization problem.
parseWBOFile :: FilePath -> IO (Either ParseError SoftFormula)
parseWBOFile = parseFromFile softformula
