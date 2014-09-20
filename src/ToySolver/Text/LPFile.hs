{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wall -fno-warn-unused-do-bind #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.Text.LPFile
-- Copyright   :  (c) Masahiro Sakai 2011-2014
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  portable
--
-- A CPLEX .lp format parser library.
-- 
-- References:
-- 
-- * <http://publib.boulder.ibm.com/infocenter/cosinfoc/v12r2/index.jsp?topic=/ilog.odms.cplex.help/Content/Optimization/Documentation/CPLEX/_pubskel/CPLEX880.html>
-- 
-- * <http://www.gurobi.com/doc/45/refman/node589.html>
-- 
-- * <http://lpsolve.sourceforge.net/5.5/CPLEX-format.htm>
--
-----------------------------------------------------------------------------
module ToySolver.Text.LPFile
  ( parseString
  , parseFile
  , render
  ) where

import Control.Monad
import Control.Monad.Writer
import Data.Char
import Data.List
import Data.Maybe
import Data.Ratio
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.OptDir
import Text.Parsec hiding (label)
import Text.Parsec.String

import qualified ToySolver.Data.MIP as MIP
import ToySolver.Internal.Util (combineMaybe)
import ToySolver.Internal.TextUtil (readUnsignedInteger)

-- ---------------------------------------------------------------------------

-- | Parse a string containing LP file data.
-- The source name is only | used in error messages and may be the empty string.
parseString :: SourceName -> String -> Either ParseError MIP.Problem
parseString = parse lpfile

-- | Parse a file containing LP file data.
parseFile :: FilePath -> IO (Either ParseError MIP.Problem)
parseFile = parseFromFile lpfile

-- ---------------------------------------------------------------------------

char' :: Char -> Parser Char
char' c = (char c <|> char (toUpper c)) <?> show c

string' :: String -> Parser ()
string' s = mapM_ char' s <?> show s

sep :: Parser ()
sep = skipMany ((comment >> return ()) <|> (space >> return ()))

comment :: Parser String
comment = do
  char '\\'
  manyTill anyChar (try newline)

tok :: Parser a -> Parser a
tok p = do
  x <- p
  sep
  return x

ident :: Parser String
ident = tok $ do
  x <- letter <|> oneOf syms1 
  xs <- many (alphaNum <|> oneOf syms2)
  let s = x:xs 
  guard $ map toLower s `Set.notMember` reserved
  return s
  where
    syms1 = "!\"#$%&()/,;?@_`'{}|~"
    syms2 = '.' : syms1

variable :: Parser MIP.Var
variable = liftM MIP.toVar ident

label :: Parser MIP.Label
label = do
  name <- ident
  tok $ char ':'
  return name

reserved :: Set String
reserved = Set.fromList
  [ "bound", "bounds"
  , "gen", "general", "generals"
  , "bin", "binary", "binaries"
  , "semi", "semi-continuous", "semis"
  , "sos"
  , "end"
  , "subject"
  ]

-- ---------------------------------------------------------------------------

lpfile :: Parser MIP.Problem
lpfile = do
  sep
  (flag, obj) <- problem

  cs <- liftM concat $ many $ msum $
    [ liftM (map Left) constraintSection
    , liftM (map Left) lazyConstraintsSection
    , liftM (map Right) userCutsSection
    ]

  bnds <- option Map.empty (try boundsSection)
  exvs <- many (liftM Left generalSection <|> liftM Right binarySection)
  let ints = Set.fromList $ concat [x | Left  x <- exvs]
      bins = Set.fromList $ concat [x | Right x <- exvs]
  bnds2 <- return $ Map.unionWith MIP.intersectBounds
            bnds (Map.fromAscList [(v, (MIP.Finite 0, MIP.Finite 1)) | v <- Set.toAscList bins])
  scs <- liftM Set.fromList $ option [] (try semiSection)

  ss <- option [] (try sosSection)
  end
  let vs = Set.unions $ map MIP.vars cs ++
           [ Map.keysSet bnds2
           , ints
           , bins
           , scs
           , MIP.vars (snd obj)
           , MIP.vars ss
           ]
      isInt v  = v `Set.member` ints || v `Set.member` bins
      isSemi v = v `Set.member` scs
  return $
    MIP.Problem
    { MIP.dir               = flag
    , MIP.objectiveFunction = obj
    , MIP.constraints       = [c | Left c <- cs]
    , MIP.userCuts          = [c | Right c <- cs]
    , MIP.sosConstraints    = ss
    , MIP.varInfo           =
        Map.fromAscList
        [ ( v
          , MIP.VarInfo
            { MIP.varBounds = Map.findWithDefault MIP.defaultBounds v bnds2
            , MIP.varType   =
                if isInt v then
                  if isSemi v then MIP.SemiIntegerVariable
                  else MIP.IntegerVariable
                else
                  if isSemi v then MIP.SemiContinuousVariable
                  else MIP.ContinuousVariable
            }
          )
        | v <- Set.toAscList vs
        ]
    }

problem :: Parser (OptDir, MIP.ObjectiveFunction)
problem = do
  flag <-  (try minimize >> return OptMin)
       <|> (try maximize >> return OptMax)
  name <- optionMaybe (try label)
  obj <- expr
  return (flag, (name, obj))

minimize, maximize :: Parser ()
minimize = tok $ string' "min" >> optional (string' "imize")
maximize = tok $ string' "max" >> optional (string' "imize")

end :: Parser ()
end = tok $ string' "end"

-- ---------------------------------------------------------------------------

constraintSection :: Parser [MIP.Constraint]
constraintSection = subjectTo >> many (try (constraint False))

subjectTo :: Parser ()
subjectTo = msum
  [ try $ tok (string' "subject") >> tok (string' "to")
  , try $ tok (string' "such") >> tok (string' "that")
  , try $ tok (string' "st")
  , try $ tok (string' "s") >> optional (tok (char '.')) >> tok (string' "t")
        >> tok (char '.') >> return ()
  ]

constraint :: Bool -> Parser MIP.Constraint
constraint isLazy = do
  name <- optionMaybe (try label)

  g <- optionMaybe $ try $ do
    var <- variable
    tok (char '=')
    val <- tok ((char '0' >> return 0) <|> (char '1' >> return 1))
    tok $ string "->"
    return (var, val)

  -- It seems that CPLEX allows empty lhs, but GLPK rejects it.
  e <- expr
  op <- relOp
  s <- option 1 sign
  rhs <- number
  return $ MIP.Constraint
    { MIP.constrLabel     = name
    , MIP.constrIndicator = g
    , MIP.constrBody      = (e, op, s*rhs)
    , MIP.constrIsLazy    = isLazy
    }

relOp :: Parser MIP.RelOp
relOp = tok $ msum
  [ char '<' >> optional (char '=') >> return MIP.Le
  , char '>' >> optional (char '=') >> return MIP.Ge
  , char '=' >> msum [ char '<' >> return MIP.Le
                     , char '>' >> return MIP.Ge
                     , return MIP.Eql
                     ]
  ]

lazyConstraintsSection :: Parser [MIP.Constraint]
lazyConstraintsSection = do
  tok $ string' "lazy"
  tok $ string' "constraints"
  many $ try $ constraint True

userCutsSection :: Parser [MIP.Constraint]
userCutsSection = do
  tok $ string' "user"
  tok $ string' "cuts"
  many $ try $ constraint False

type Bounds2 = (Maybe MIP.BoundExpr, Maybe MIP.BoundExpr)

boundsSection :: Parser (Map MIP.Var MIP.Bounds)
boundsSection = do
  tok $ string' "bound" >> optional (char' 's')
  liftM (Map.map g . Map.fromListWith f) $ many (try bound)
  where
    f (lb1,ub1) (lb2,ub2) = (combineMaybe max lb1 lb2, combineMaybe min ub1 ub2)
    g (lb, ub) = ( fromMaybe MIP.defaultLB lb
                 , fromMaybe MIP.defaultUB ub
                 )

bound :: Parser (MIP.Var, Bounds2)
bound = msum
  [ try $ do
      v <- try variable
      msum
        [ do
            op <- relOp
            b <- boundExpr
            return
              ( v
              , case op of
                  MIP.Le -> (Nothing, Just b)
                  MIP.Ge -> (Just b, Nothing)
                  MIP.Eql -> (Just b, Just b)
              )
        , do
            tok $ string' "free"
            return (v, (Just MIP.NegInf, Just MIP.PosInf))
        ]
  , do
      b1 <- liftM Just boundExpr
      op1 <- relOp
      guard $ op1 == MIP.Le
      v <- variable
      b2 <- option Nothing $ do
        op2 <- relOp
        guard $ op2 == MIP.Le
        liftM Just boundExpr
      return (v, (b1, b2))
  ]

boundExpr :: Parser MIP.BoundExpr
boundExpr = msum 
  [ try (tok (char '+') >> inf >> return MIP.PosInf)
  , try (tok (char '-') >> inf >> return MIP.NegInf)
  , do
      s <- option 1 sign
      x <- number
      return $ MIP.Finite (s*x)
  ]

inf :: Parser ()
inf = tok (string "inf" >> optional (string "inity"))

-- ---------------------------------------------------------------------------

generalSection :: Parser [MIP.Var]
generalSection = do
  tok $ string' "gen" >> optional (string' "eral" >> optional (string' "s"))
  many (try variable)

binarySection :: Parser [MIP.Var]
binarySection = do
  tok $ string' "bin" >> optional (string' "ar" >> (string' "y" <|> string' "ies"))
  many (try variable)

semiSection :: Parser [MIP.Var]
semiSection = do
  tok $ string' "semi" >> optional (string' "-continuous" <|> string' "s")
  many (try variable)

sosSection :: Parser [MIP.SOSConstraint]
sosSection = do
  tok $ string' "sos"
  many $ try $ do
    (l,t) <- try (do{ l <- label; t <- typ; return (Just l, t) })
          <|> (do{ t <- typ; return (Nothing, t) })
    xs <- many $ try $ do
      v <- variable
      tok $ char ':'
      w <- number
      return (v,w)
    return $ MIP.SOSConstraint l t xs
  where
    typ = do
      t <- tok $ (char' 's' >> ((char '1' >> return MIP.S1) <|> (char '2' >> return MIP.S2)))
      tok (string "::")
      return t

-- ---------------------------------------------------------------------------

expr :: Parser MIP.Expr
expr = try expr1 <|> return []
  where
    expr1 :: Parser MIP.Expr
    expr1 = do
      t <- term True
      ts <- many (term False)
      return $ concat (t : ts)

sign :: Num a => Parser a
sign = tok ((char '+' >> return 1) <|> (char '-' >> return (-1)))

term :: Bool -> Parser MIP.Expr
term flag = do
  s <- if flag then optionMaybe sign else liftM Just sign
  c <- optionMaybe number
  e <- liftM (\s' -> [MIP.Term 1 [s']]) variable <|> qexpr
  return $ case combineMaybe (*) s c of
    Nothing -> e
    Just d -> [MIP.Term (d*c') vs | MIP.Term c' vs <- e]

qexpr :: Parser MIP.Expr
qexpr = do
  tok (char '[')
  t <- qterm True
  ts <- many (qterm False)
  tok (char ']')
  -- Gurobi allows ommiting "/2"
  (do mapM_ (tok . char) "/2"
      return [MIP.Term (r / 2) vs | MIP.Term r vs <- t:ts])
   <|> return (t:ts)

qterm :: Bool -> Parser MIP.Term
qterm flag = do
  s <- if flag then optionMaybe sign else liftM Just sign
  c <- optionMaybe number
  es <- qfactor `chainl1`  (tok (char '*') >> return (++))
  return $ case combineMaybe (*) s c of
    Nothing -> MIP.Term 1 es
    Just d -> MIP.Term d es

qfactor :: Parser [MIP.Var]
qfactor = do
  v <- variable
  msum [ tok (char '^') >> tok (char '2') >> return [v,v]
       , return [v]
       ]

number :: Parser Rational
number = tok $ do
  b <- (do{ x <- nat; y <- option 0 frac; return (fromInteger x + y) })
    <|> frac
  c <- option 0 e
  return (b*10^^c)
  where
    digits = many1 digit

    nat :: Parser Integer
    nat = liftM readUnsignedInteger digits

    frac :: Parser Rational
    frac = do
      char '.'
      s <- digits
      return (readUnsignedInteger s % 10^(length s))

    e :: Parser Integer
    e = do
      oneOf "eE"
      f <- msum [ char '+' >> return id
                , char '-' >> return negate
                , return id
                ]
      liftM f nat

-- ---------------------------------------------------------------------------

type M a = Writer ShowS a

execM :: M a -> String
execM m = execWriter m ""

writeString :: String -> M ()
writeString s = tell $ showString s

writeChar :: Char -> M ()
writeChar c = tell $ showChar c

-- ---------------------------------------------------------------------------

-- | Render a problem into a string.
render :: MIP.Problem -> Maybe String
render mip = Just $ execM $ render' $ removeEmptyExpr mip

writeVar :: MIP.Var -> M ()
writeVar v = writeString $ MIP.fromVar v

render' :: MIP.Problem -> M ()
render' mip = do
  writeString $
    case MIP.dir mip of
      OptMin -> "MINIMIZE"
      OptMax -> "MAXIMIZE"
  writeChar '\n'

  do
    let (l, obj) = MIP.objectiveFunction mip
    renderLabel l
    renderExpr True obj
    writeChar '\n'

  writeString "SUBJECT TO\n"
  forM_ (MIP.constraints mip) $ \c -> do
    unless (MIP.constrIsLazy c) $ do
      renderConstraint c
      writeChar '\n'

  let lcs = [c | c <- MIP.constraints mip, MIP.constrIsLazy c]
  unless (null lcs) $ do
    writeString "LAZY CONSTRAINTS\n"
    forM_ lcs $ \c -> do
      renderConstraint c
      writeChar '\n'

  let cuts = [c | c <- MIP.userCuts mip]
  unless (null cuts) $ do
    writeString "USER CUTS\n"
    forM_ cuts $ \c -> do
      renderConstraint c
      writeChar '\n'

  let ivs = MIP.integerVariables mip `Set.union` MIP.semiIntegerVariables mip
      (bins,gens) = Set.partition (\v -> MIP.getBounds mip v == (MIP.Finite 0, MIP.Finite 1)) ivs
      scs = MIP.semiContinuousVariables mip `Set.union` MIP.semiIntegerVariables mip

  writeString "BOUNDS\n"
  forM_ (Map.toAscList (MIP.varInfo mip)) $ \(v, MIP.VarInfo{ MIP.varBounds = (lb,ub) }) -> do
    unless (v `Set.member` bins) $ do
      renderBoundExpr lb
      writeString " <= "
      writeVar v
      writeString " <= "
      renderBoundExpr ub
      writeChar '\n'

  unless (Set.null gens) $ do
    writeString "GENERALS\n"
    renderVariableList $ Set.toList gens

  unless (Set.null bins) $ do
    writeString "BINARIES\n"
    renderVariableList $ Set.toList bins

  unless (Set.null scs) $ do
    writeString "SEMI-CONTINUOUS\n"
    renderVariableList $ Set.toList scs

  unless (null (MIP.sosConstraints mip)) $ do
    writeString "SOS\n"
    forM_ (MIP.sosConstraints mip) $ \(MIP.SOSConstraint l typ xs) -> do
      renderLabel l
      writeString $ show typ
      writeString " ::"
      forM_ xs $ \(v, r) -> do
        writeString "  "
        writeVar v
        writeString " : "
        writeString $ showValue r
      writeChar '\n'

  writeString "END\n"

-- FIXME: Gurobi は quadratic term が最後に一つある形式でないとダメっぽい
renderExpr :: Bool -> MIP.Expr -> M ()
renderExpr isObj e = fill 80 (ts1 ++ ts2)
  where
    (ts,qts) = partition isLin e 
    isLin (MIP.Term _ [])  = True
    isLin (MIP.Term _ [_]) = True
    isLin _ = False

    ts1 = map f ts
    ts2
      | null qts  = []
      | otherwise =
        -- マイナスで始めるとSCIP 2.1.1 は「cannot have '-' in front of quadratic part ('[')」というエラーを出す
        ["+ ["] ++ map g qts ++ [if isObj then "] / 2" else "]"]

    f :: MIP.Term -> String
    f (MIP.Term c [])  = showConstTerm c
    f (MIP.Term c [v]) = showCoeff c ++ MIP.fromVar v
    f _ = error "should not happen"

    g :: MIP.Term -> String
    g (MIP.Term c vs) = 
      (if isObj then showCoeff (2*c) else showCoeff c) ++
      intercalate " * " (map MIP.fromVar vs)

showValue :: Rational -> String
showValue c =
  if denominator c == 1
    then show (numerator c)
    else show (fromRational c :: Double)

showCoeff :: Rational -> String
showCoeff c =
  if c' == 1
    then s
    else s ++ showValue c' ++ " "
  where
    c' = abs c
    s = if c >= 0 then "+ " else "- "

showConstTerm :: Rational -> String
showConstTerm c = s ++ v
  where
    s = if c >= 0 then "+ " else "- "
    v = showValue (abs c)

renderLabel :: Maybe MIP.Label -> M ()
renderLabel l =
  case l of
    Nothing -> return ()
    Just s -> writeString s >> writeString ": "

renderOp :: MIP.RelOp -> M ()
renderOp MIP.Le = writeString "<="
renderOp MIP.Ge = writeString ">="
renderOp MIP.Eql = writeString "="

renderConstraint :: MIP.Constraint -> M ()
renderConstraint c@MIP.Constraint{ MIP.constrBody = (e,op,val) }  = do
  renderLabel (MIP.constrLabel c)
  case MIP.constrIndicator c of
    Nothing -> return ()
    Just (v,vval) -> do
      writeVar v
      writeString " = "
      writeString $ showValue vval
      writeString " -> "

  renderExpr False e
  writeChar ' '
  renderOp op
  writeChar ' '
  writeString $ showValue val

renderBoundExpr :: MIP.BoundExpr -> M ()
renderBoundExpr (MIP.Finite r) = writeString $ showValue r
renderBoundExpr MIP.NegInf = writeString "-inf"
renderBoundExpr MIP.PosInf = writeString "+inf"

renderVariableList :: [MIP.Var] -> M ()
renderVariableList vs = fill 80 (map MIP.fromVar vs) >> writeChar '\n'

fill :: Int -> [String] -> M ()
fill width str = go str 0
  where
    go [] _ = return ()
    go (x:xs) 0 = writeString x >> go xs (length x)
    go (x:xs) w =
      if w + 1 + length x <= width
        then writeChar ' ' >> writeString x >> go xs (w + 1 + length x)
        else writeChar '\n' >> go (x:xs) 0

-- ---------------------------------------------------------------------------

{-
compileExpr :: Expr -> Maybe (Map Var Rational)
compileExpr e = do
  xs <- forM e $ \(Term c vs) ->
    case vs of
      [v] -> return (v, c)
      _ -> mzero
  return (Map.fromList xs)
-}

-- ---------------------------------------------------------------------------

removeEmptyExpr :: MIP.Problem -> MIP.Problem
removeEmptyExpr prob =
  prob
  { MIP.objectiveFunction =
      case MIP.objectiveFunction prob of
        (label, e) -> (label, convertExpr e)
  , MIP.constraints = map convertConstr $ MIP.constraints prob
  , MIP.userCuts    = map convertConstr $ MIP.userCuts prob
  }
  where
    convertExpr [] = [MIP.Term 0 [MIP.toVar "x0"]]
    convertExpr e = e

    convertConstr constr =
      constr
      { MIP.constrBody =
          case MIP.constrBody constr of
            (lhs,op,rhs) -> (convertExpr lhs, op, rhs)
      }
