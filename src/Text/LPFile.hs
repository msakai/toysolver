{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wall -fno-warn-unused-do-bind #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Text.LPFile
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
module Text.LPFile
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
import qualified Data.MIP as MIP
import Text.ParserCombinators.Parsec hiding (label)

import ToySolver.Util (combineMaybe)
import Text.Util (readUnsignedInteger)

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
                if v `Set.member` ints || v `Set.member` bins then MIP.IntegerVariable
                else if v `Set.member` scs then MIP.SemiContinuousVariable
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

-- | Render a problem into a string.
render :: MIP.Problem -> Maybe String
render lp = fmap ($ "") $ execWriterT (render' lp)

render' :: MIP.Problem -> WriterT ShowS Maybe ()
render' lp = do
  tell $ showString $
    case MIP.dir lp of
      OptMin -> "MINIMIZE"
      OptMax -> "MAXIMIZE"
  tell $ showChar '\n'

  do
    let (l, obj) = MIP.objectiveFunction lp
    renderLabel l
    renderExpr True obj
    tell $ showChar '\n'

  tell $ showString "SUBJECT TO\n"
  forM_ (MIP.constraints lp) $ \c -> do
    unless (MIP.constrIsLazy c) $ do
      renderConstraint c
      tell $ showChar '\n'

  let lcs = [c | c <- MIP.constraints lp, MIP.constrIsLazy c]
  unless (null lcs) $ do
    tell $ showString "LAZY CONSTRAINTS\n"
    forM_ lcs $ \c -> do
      renderConstraint c
      tell $ showChar '\n'

  let cuts = [c | c <- MIP.userCuts lp]
  unless (null cuts) $ do
    tell $ showString "USER CUTS\n"
    forM_ cuts $ \c -> do
      renderConstraint c
      tell $ showChar '\n'

  let ivs = MIP.integerVariables lp
      (bins,gens) = Set.partition (\v -> MIP.getBounds lp v == (MIP.Finite 0, MIP.Finite 1)) ivs
      scs = MIP.semiContinuousVariables lp

  tell $ showString "BOUNDS\n"
  forM_ (Map.toAscList (MIP.varInfo lp)) $ \(v, MIP.VarInfo{ MIP.varBounds = (lb,ub) }) -> do
    unless (v `Set.member` bins) $ do
      renderBoundExpr lb
      tell $ showString " <= "
      tell $ showVar v
      tell $ showString " <= "
      renderBoundExpr ub
      tell $ showChar '\n'

  unless (Set.null gens) $ do
    tell $ showString "GENERALS\n"
    renderVariableList $ Set.toList gens

  unless (Set.null bins) $ do
    tell $ showString "BINARIES\n"
    renderVariableList $ Set.toList bins

  unless (Set.null scs) $ do
    tell $ showString "SEMI-CONTINUOUS\n"
    renderVariableList $ Set.toList scs

  unless (null (MIP.sosConstraints lp)) $ do
    tell $ showString "SOS\n"
    forM_ (MIP.sosConstraints lp) $ \(MIP.SOSConstraint l typ xs) -> do
      renderLabel l
      tell $ shows typ
      tell $ showString " ::"
      forM_ xs $ \(v, r) -> do
        tell $ showString "  "
        tell $ showVar v
        tell $ showString " : "
        tell $ showValue r
      tell $ showChar '\n'

  tell $ showString "END\n"

-- FIXME: Gurobi は quadratic term が最後に一つある形式でないとダメっぽい
renderExpr :: Bool -> MIP.Expr -> WriterT ShowS Maybe ()
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
    f (MIP.Term c [])  = showConstTerm c ""
    f (MIP.Term c [v]) = showCoeff c . showVar v $ ""
    f _ = error "should not happen"

    g :: MIP.Term -> String
    g (MIP.Term c vs) = 
      (if isObj then showCoeff (2*c) else showCoeff c)
      (intercalate " * " (map MIP.fromVar vs))

showVar :: MIP.Var -> ShowS
showVar = showString . MIP.fromVar

showValue :: Rational -> ShowS
showValue c =
  if denominator c == 1
    then shows (numerator c)
    else shows (fromRational c :: Double)

showCoeff :: Rational -> ShowS
showCoeff c = s . v
  where
    c' = abs c
    s = showString (if c >= 0 then "+ " else "- ")
    v = (if c' /= 1 then showValue c' . showChar ' ' else id)

showConstTerm :: Rational -> ShowS
showConstTerm c = s . v
  where
    s = showString (if c >= 0 then "+ " else "- ")
    v = showValue (abs c)

renderLabel :: Maybe MIP.Label -> WriterT ShowS Maybe ()
renderLabel l =
  case l of
    Nothing -> return ()
    Just s -> tell $ showString s . showString ": "

renderOp :: MIP.RelOp -> WriterT ShowS Maybe ()
renderOp MIP.Le = tell $ showString "<="
renderOp MIP.Ge = tell $ showString ">="
renderOp MIP.Eql = tell $ showString "="

renderConstraint :: MIP.Constraint -> WriterT ShowS Maybe ()
renderConstraint c@MIP.Constraint{ MIP.constrBody = (e,op,val) }  = do
  renderLabel (MIP.constrLabel c)
  case MIP.constrIndicator c of
    Nothing -> return ()
    Just (v,vval) -> do
      tell $ showVar v . showString " = "
      tell $ showValue vval
      tell $ showString " -> "

  renderExpr False e
  tell $ showChar ' '
  renderOp op
  tell $ showChar ' '
  tell $ showValue val

renderBoundExpr :: MIP.BoundExpr -> WriterT ShowS Maybe ()
renderBoundExpr (MIP.Finite r) = tell $ showValue r
renderBoundExpr MIP.NegInf = tell $ showString "-inf"
renderBoundExpr MIP.PosInf = tell $ showString "+inf"

renderVariableList :: [MIP.Var] -> WriterT ShowS Maybe ()
renderVariableList vs = fill 80 (map MIP.fromVar vs) >> tell (showChar '\n')

fill :: Int -> [String] -> WriterT ShowS Maybe ()
fill width str = go str 0
  where
    go [] _ = return ()
    go (x:xs) 0 = tell (showString x) >> go xs (length x)
    go (x:xs) w =
      if w + 1 + length x <= width
        then tell (showChar ' ' . showString x) >> go xs (w + 1 + length x)
        else tell (showChar '\n') >> go (x:xs) 0

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
