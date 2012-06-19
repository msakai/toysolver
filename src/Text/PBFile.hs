{-# LANGUAGE BangPatterns #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Text.PBFile
-- Copyright   :  (c) Masahiro Sakai 2011
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Portability :  portable
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

module Text.PBFile
  (
  -- * Abstract Syntax
    Formula
  , Constraint
  , Op (..)
  , SoftFormula
  , SoftConstraint
  , Sum
  , WeightedTerm
  , Term
  , Lit (..)
  , Var

  -- * Parsing .opb files
  , parseOPBString
  , parseOPBFile

  -- * Parsing .wbo files
  , parseWBOString
  , parseWBOFile

  -- * Show .opb files
  , showOPB

  -- * Show .wbo files
  , showWBO
  ) where

import Prelude hiding (sum)
import Control.Monad
import Data.Maybe
import Data.List hiding (sum)
import Text.ParserCombinators.Parsec
import Data.Word
import Control.Exception (assert)
import Text.Printf

-- | Pair of /objective function/ and a list of constraints.
type Formula = (Maybe Sum, [Constraint])

-- | Lhs, relational operator and rhs.
type Constraint = (Sum, Op, Integer)

-- | Relational operators
data Op
  = Ge -- ^ /greater than or equal/
  | Eq -- ^ /equal/
  deriving (Eq, Ord, Show, Enum, Bounded)

-- | A pair of /top cost/ and a list of soft constraints.
type SoftFormula = (Maybe Integer, [SoftConstraint])

-- | A pair of weight and constraint.
type SoftConstraint = (Maybe Integer, Constraint)

-- | Sum of 'WeightedTerm'
type Sum = [WeightedTerm]

-- | Coefficient and 'Term'
type WeightedTerm = (Integer, Term)

-- | List of variables interpreted as products
type Term = [Lit]

-- | Positive (resp. negative) literal is represented as a positive (resp. negative) integer.
type Lit = Int

-- | Variable are repserented positive integer.
type Var = Int

-- <formula>::= <sequence_of_comments> [<objective>] <sequence_of_comments_or_constraints>
formula :: Parser Formula
formula = do
  sequence_of_comments
  obj <- optionMaybe objective
  cs <- sequence_of_comments_or_constraints
  return (obj, cs)

-- <sequence_of_comments>::= <comment> [<sequence_of_comments>]
sequence_of_comments :: Parser ()
sequence_of_comments = skipMany1 comment

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

-- | 'read' allocate too many intermediate 'Integer'.
-- Therefore we use this optimized implementation instead.
-- Many intermediate values in this implementation will be optimized
-- away by worker-wrapper transformation and unboxing.
readUnsignedInteger :: String -> Integer 
readUnsignedInteger str = assert (result == read str) $ result
  where
    result :: Integer
    result = go 0 str

    lim :: Word
    lim = maxBound `div` 10
  
    go :: Integer -> [Char] -> Integer 
    go !r [] = r
    go !r ds =
      case go2 0 1 ds of
        (r2,b,ds2) -> go (r * fromIntegral b + fromIntegral r2) ds2

    go2 :: Word -> Word -> [Char] -> (Word, Word, [Char])
    go2 !r !b dds | assert (b > r) (b > lim) = (r,b,dds)
    go2 !r !b []     = (r, b, [])
    go2 !r !b (d:ds) = go2 (r*10 + charToWord d) (b*10) ds

    charToWord :: Char -> Word
    charToWord '0' = 0
    charToWord '1' = 1
    charToWord '2' = 2
    charToWord '3' = 3
    charToWord '4' = 4
    charToWord '5' = 5
    charToWord '6' = 6
    charToWord '7' = 7
    charToWord '8' = 8
    charToWord '9' = 9

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
  sequence_of_comments
  top <- softheader
  cs <- wbo_sequence_of_comments_or_constraints
  return (top, cs)

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


showOPB :: Formula -> ShowS
showOPB opb@(obj, cs) = (size . part1 . part2)
  where
    nv = pbNumVars opb
    nc = length cs
    size = showString (printf "* #variable= %d #constraint= %d\n" nv nc)
    part1 = 
      case obj of
        Nothing -> id
        Just o -> showString "min: " . showSum o . showString ";\n"
    part2 = foldr (.) id (map showConstraint cs)

showWBO :: SoftFormula -> ShowS
showWBO wbo@(top, cs) = size . part1 . part2
  where
    nv = wboNumVars wbo
    nc = length cs
    size = showString (printf "* #variable= %d #constraint= %d\n" nv nc)
    part1 = 
      case top of
        Nothing -> showString "soft: "
        Just t -> showString "soft: " . showsPrec 0 t . showString ";\n"
    part2 = foldr (.) id (map showSoftConstraint cs)

showSum :: Sum -> ShowS
showSum = foldr (.) id . map showWeightedTerm

showWeightedTerm :: WeightedTerm -> ShowS
showWeightedTerm (c, lits) = foldr (\f g -> f . showChar ' ' . g) id (x:xs)
  where
    x = if c >= 0 then showChar '+' . showsPrec 0 c else showsPrec 0 c
    xs = map showLit lits

showLit :: Lit -> ShowS
showLit lit =   if lit > 0 then v else showChar '~' . v
  where
    v = showChar 'x' . showsPrec 0 (abs lit)

showConstraint :: Constraint -> ShowS
showConstraint (lhs, op, rhs) =
  showSum lhs . f op .  showChar ' ' . showsPrec 0 rhs . showString ";\n"
  where
    f Eq = showString "="
    f Ge = showString ">="

showSoftConstraint :: SoftConstraint -> ShowS
showSoftConstraint (cost, constr) =
  case cost of
    Nothing -> showConstraint constr
    Just c -> showChar '[' . showsPrec 0 c . showChar ']' . showChar ' ' . showConstraint constr

pbNumVars :: Formula -> Int
pbNumVars (m, cs) = maximum (0 : vs)
  where
    vs = do
      s <- maybeToList m ++ [s | (s,_,_) <- cs]
      (_, tm) <- s
      lit <- tm
      return $ abs lit

wboNumVars :: SoftFormula -> Int
wboNumVars (_, cs) = maximum vs
  where
    vs = do
      s <- [s | (_, (s,_,_)) <- cs]
      (_, tm) <- s
      lit <- tm
      return $ abs lit


exampleLIN :: String
exampleLIN = unlines
  [ "* #variable= 5 #constraint= 4"
  , "*"
  , "* this is a dummy instance"
  , "*"
  , "min: 1 x2 -1 x3 ;"
  , "1 x1 +4 x2 -2 x5 >= 2;"
  , "-1 x1 +4 x2 -2 x5 >= +3;"
  , "12345678901234567890 x4 +4 x3 >= 10;"
  , "* an equality constraint"
  , "2 x2 +3 x4 +2 x1 +3 x5 = 5;"
  ]

exampleNLC1 :: String
exampleNLC1 = unlines
  [ "* #variable= 5 #constraint= 4 #product= 5 sizeproduct= 13"
  , "*"
  , "* this is a dummy instance"
  , "*"
  , "min: 1 x2 x3 -1 x3 ;"
  , "1 x1 +4 x1 ~x2 -2 x5 >= 2;"
  , "-1 x1 +4 x2 -2 x5 >= 3;"
  , "12345678901234567890 x4 +4 x3 >= 10;"
  , "2 x2 x3 +3 x4 ~x5 +2 ~x1 x2 +3 ~x1 x2 x3 ~x4 ~x5 = 5 ;"
  ]

exampleNLC2 :: String
exampleNLC2 = unlines
  [ "* #variable= 6 #constraint= 3 #product= 9 sizeproduct= 18"
  , "*"
  , "* Factorization problem: find the smallest P such that P*Q=N"
  , "* P is a 3 bits number (x3 x2 x1)"
  , "* Q is a 3 bits number (x6 x5 x4)"
  , "* N=35"
  , "* "
  , "* minimize the value of P"
  , "min: +1 x1 +2 x2 +4 x3 ;"
  , "* P>=2 (to avoid trivial factorization)"
  , "+1 x1 +2 x2 +4 x3 >=2;"
  , "* Q>=2 (to avoid trivial factorization)"
  , "+1 x4 +2 x5 +4 x6 >=2;"
  , "*"
  , "* P*Q=N"
  , "+1 x1 x4 +2 x1 x5 +4 x1 x6 +2 x2 x4 +4 x2 x5 +8 x2 x6 +4 x3 x4 +8 x3 x5 +16 x3 x6 = 35;"
  ]

exampleWBO1 :: String
exampleWBO1 = unlines $
  [ "* #variable= 1 #constraint= 2 #soft= 2 mincost= 2 maxcost= 3 sumcost= 5"
  , "soft: 6 ;"
  , "[2] +1 x1 >= 1 ;"
  , "[3] -1 x1 >= 0 ;"
  ]

exampleWBO2 :: String
exampleWBO2 = unlines $
  [ "* #variable= 2 #constraint= 3 #soft= 2 mincost= 2 maxcost= 3 sumcost= 5"
  , "soft: 6 ;"
  , "[2] +1 x1 >= 1 ;"
  , "[3] +1 x2 >= 1 ;"
  , "-1 x1 -1 x2 >= -1 ;"
  ]

exampleWBO3 :: String
exampleWBO3 = unlines $
  [ "* #variable= 4 #constraint= 6 #soft= 4 mincost= 2 maxcost= 5 sumcost= 14"
  , "soft: 6 ;"
  , "[2] +1 x1 >= 1;"
  , "[3] +1 x2 >= 1;"
  , "[4] +1 x3 >= 1;"
  , "[5] +1 x4 >= 1;"
  , "-1 x1 -1 x2 >= -1 ;"
  , "-1 x3 -1 x4 >= -1 ;"
  ]

testOPB :: String -> Bool
testOPB s = sf == sf2
  where
    Right sf  = parseOPBString "-" s
    s2 = showOPB sf ""
    Right sf2 = parseOPBString "-" s2

testWBO :: String -> Bool
testWBO s = sf == sf2
  where
    Right sf  = parseWBOString "-" s
    s2 = showWBO sf ""
    Right sf2 = parseWBOString "-" s2
