{-# OPTIONS_GHC -Wall -fno-warn-unused-do-bind #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Text.LPFile
-- Copyright   :  (c) Masahiro Sakai 2011
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
  ( LP (..)
  , Expr
  , Term (..)
  , OptDir (..)
  , ObjectiveFunction
  , ConstraintType (..)
  , Constraint (..)
  , Bounds
  , Label
  , Var
  , VarType (..)
  , VarInfo (..)
  , BoundExpr (..)
  , RelOp (..)
  , SOSType (..)
  , SOS
  , defaultBounds
  , defaultLB
  , defaultUB
  , toVar
  , fromVar
  , getVarInfo
  , getVarType
  , getBounds
  , integerVariables
  , semiContinuousVariables
  , parseString
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
import Text.ParserCombinators.Parsec hiding (label)

import ToySolver.Util (combineMaybe)

-- ---------------------------------------------------------------------------

-- | Problem
data LP
  = LP
  { variables :: Set Var
  , dir :: OptDir
  , objectiveFunction :: ObjectiveFunction
  , constraints :: [Constraint]
  , varInfo :: Map Var VarInfo
  , sos :: [SOS]
  }
  deriving (Show, Eq, Ord)

-- | expressions
type Expr = [Term]

-- | terms
data Term = Term Rational [Var]
  deriving (Eq, Ord, Show)

-- | objective function
type ObjectiveFunction = (Maybe Label, Expr)

data ConstraintType
  = NormalConstraint
  | LazyConstraint
  | UserDefinedCut
  deriving (Eq, Ord, Bounded, Enum, Show)

-- | constraint
data Constraint
  = Constraint
  { constrType      :: ConstraintType
  , constrLabel     :: Maybe Label
  , constrIndicator :: Maybe (Var, Rational)
  , constrBody      :: (Expr, RelOp, Rational)
  }
  deriving (Eq, Ord, Show)

data VarType
  = ContinuousVariable
  | IntegerVariable
-- 'nothaddock' is inserted not to confuse haddock
  -- nothaddock | BinaryVariable
  | SemiContinuousVariable
  -- nothaddock | SemiIntegerVariable
  deriving (Eq, Ord, Show)

data VarInfo
  = VarInfo
  { varName   :: Var
  , varType   :: VarType
  , varBounds :: Bounds
  }
 deriving (Eq, Ord, Show)

defaultVarInfo :: VarInfo
defaultVarInfo
  = VarInfo
  { varName   = ""
  , varType   = ContinuousVariable
  , varBounds = defaultBounds
  }

-- | type for representing lower/upper bound of variables
type Bounds = (BoundExpr, BoundExpr)

-- | label
type Label = String

-- | variable
type Var = String

-- | type for representing lower/upper bound of variables
data BoundExpr = NegInf | Finite Rational | PosInf
    deriving (Eq, Ord, Show)

-- | relational operators
data RelOp = Le | Ge | Eql
    deriving (Eq, Ord, Enum, Show)

-- | types of SOS (special ordered sets) constraints
data SOSType
  = S1 -- ^ Type 1 SOS constraint
  | S2 -- ^ Type 2 SOS constraint
    deriving (Eq, Ord, Enum, Show, Read)

-- | SOS (special ordered sets) constraints
type SOS = (Maybe Label, SOSType, [(Var, Rational)])

class Variables a where
  vars :: a -> Set Var

instance Variables a => Variables [a] where
  vars = Set.unions . map vars

instance Variables LP where
  vars = variables

instance Variables Term where
  vars (Term _ xs) = Set.fromList xs

instance Variables Constraint where
  vars Constraint{ constrIndicator = ind, constrBody = (lhs, _, _) } =
    vars lhs `Set.union` vs2
    where
      vs2 = maybe Set.empty (Set.singleton . fst) ind

-- | default bounds
defaultBounds :: Bounds
defaultBounds = (defaultLB, defaultUB)

-- | default lower bound (0)
defaultLB :: BoundExpr
defaultLB = Finite 0

-- | default upper bound (+∞)
defaultUB :: BoundExpr
defaultUB = PosInf

-- | convert a string into a variable
toVar :: String -> Var
toVar = id

-- | convert a variable into a string
fromVar :: Var -> String
fromVar = id

-- | looking up attributes for a variable
getVarInfo :: LP -> Var -> VarInfo
getVarInfo lp v = Map.findWithDefault defaultVarInfo v (varInfo lp)

-- | looking up bounds for a variable
getVarType :: LP -> Var -> VarType
getVarType lp v = varType $ getVarInfo lp v

-- | looking up bounds for a variable
getBounds :: LP -> Var -> Bounds
getBounds lp v = varBounds $ getVarInfo lp v

intersectBounds :: Bounds -> Bounds -> Bounds
intersectBounds (lb1,ub1) (lb2,ub2) = (max lb1 lb2, min ub1 ub2)

integerVariables :: LP -> Set Var
integerVariables lp = Map.keysSet $ Map.filter p (varInfo lp)
  where
    p VarInfo{ varType = vt } = vt == IntegerVariable

semiContinuousVariables :: LP -> Set Var
semiContinuousVariables lp = Map.keysSet $ Map.filter p (varInfo lp)
  where
    p VarInfo{ varType = vt } = vt == SemiContinuousVariable

-- ---------------------------------------------------------------------------

-- | Parse a string containing LP file data.
-- The source name is only | used in error messages and may be the empty string.
parseString :: SourceName -> String -> Either ParseError LP
parseString = parse lpfile

-- | Parse a file containing LP file data.
parseFile :: FilePath -> IO (Either ParseError LP)
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

variable :: Parser Var
variable = ident

label :: Parser Label
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

lpfile :: Parser LP
lpfile = do
  sep
  (flag, obj) <- problem

  cs <- liftM concat $ many $ msum $
    [ constraintSection
    , lazyConstraintsSection
    , userCutsSection
    ]

  bnds <- option Map.empty (try boundsSection)
  exvs <- many (liftM Left generalSection <|> liftM Right binarySection)
  let ints = Set.fromList $ concat [x | Left  x <- exvs]
      bins = Set.fromList $ concat [x | Right x <- exvs]
  bnds2 <- return $ Map.unionWith intersectBounds
            bnds (Map.fromAscList [(v, (Finite 0, Finite 1)) | v <- Set.toAscList bins])
  scs <- liftM Set.fromList $ option [] (try semiSection)

  ss <- option [] (try sosSection)
  end
  let vs = Set.unions $ map vars cs ++
           [ Map.keysSet bnds2
           , ints
           , bins
           , scs
           , vars (snd obj)
           ] ++
           [Set.fromList (map fst xs) | (_,_,xs) <- ss]
  return $
    LP
    { variables         = vs
    , dir               = flag
    , objectiveFunction = obj
    , constraints       = cs
    , sos               = ss
    , varInfo           =
        Map.fromAscList
        [ ( v
          , VarInfo
            { varName   = v
            , varBounds = Map.findWithDefault defaultBounds v bnds2
            , varType   =
                if v `Set.member` ints || v `Set.member` bins then IntegerVariable
                else if v `Set.member` scs then SemiContinuousVariable
                else ContinuousVariable
            }
          )
        | v <- Set.toAscList vs
        ]
    }

problem :: Parser (OptDir, ObjectiveFunction)
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

constraintSection :: Parser [Constraint]
constraintSection = subjectTo >> many (try (constraint NormalConstraint))

subjectTo :: Parser ()
subjectTo = msum
  [ try $ tok (string' "subject") >> tok (string' "to")
  , try $ tok (string' "such") >> tok (string' "that")
  , try $ tok (string' "st")
  , try $ tok (string' "s") >> optional (tok (char '.')) >> tok (string' "t")
        >> tok (char '.') >> return ()
  ]

constraint :: ConstraintType -> Parser Constraint
constraint t = do
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
  return $ Constraint
    { constrType      = t
    , constrLabel     = name
    , constrIndicator = g
    , constrBody      = (e, op, s*rhs)
    }

relOp :: Parser RelOp
relOp = tok $ msum
  [ char '<' >> optional (char '=') >> return Le
  , char '>' >> optional (char '=') >> return Ge
  , char '=' >> msum [ char '<' >> return Le
                     , char '>' >> return Ge
                     , return Eql
                     ]
  ]

lazyConstraintsSection :: Parser [Constraint]
lazyConstraintsSection = do
  tok $ string' "lazy"
  tok $ string' "constraints"
  many $ try $ constraint LazyConstraint

userCutsSection :: Parser [Constraint]
userCutsSection = do
  tok $ string' "user"
  tok $ string' "cuts"
  many $ try $ constraint $ UserDefinedCut

type Bounds2 = (Maybe BoundExpr, Maybe BoundExpr)

boundsSection :: Parser (Map Var Bounds)
boundsSection = do
  tok $ string' "bound" >> optional (char' 's')
  liftM (Map.map g . Map.fromListWith f) $ many (try bound)
  where
    f (lb1,ub1) (lb2,ub2) = (combineMaybe max lb1 lb2, combineMaybe min ub1 ub2)
    g (lb, ub) = ( fromMaybe defaultLB lb
                 , fromMaybe defaultUB ub
                 )

bound :: Parser (Var, Bounds2)
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
                  Le -> (Nothing, Just b)
                  Ge -> (Just b, Nothing)
                  Eql -> (Just b, Just b)
              )
        , do
            tok $ string' "free"
            return (v, (Just NegInf, Just PosInf))
        ]
  , do
      b1 <- liftM Just boundExpr
      op1 <- relOp
      guard $ op1 == Le
      v <- variable
      b2 <- option Nothing $ do
        op2 <- relOp
        guard $ op2 == Le
        liftM Just boundExpr
      return (v, (b1, b2))
  ]

boundExpr :: Parser BoundExpr
boundExpr = msum 
  [ try (tok (char '+') >> inf >> return PosInf)
  , try (tok (char '-') >> inf >> return NegInf)
  , do
      s <- option 1 sign
      x <- number
      return $ Finite (s*x)
  ]

inf :: Parser ()
inf = tok (string "inf" >> optional (string "inity"))

-- ---------------------------------------------------------------------------

generalSection :: Parser [Var]
generalSection = do
  tok $ string' "gen" >> optional (string' "eral" >> optional (string' "s"))
  many (try variable)

binarySection :: Parser [Var]
binarySection = do
  tok $ string' "bin" >> optional (string' "ar" >> (string' "y" <|> string' "ies"))
  many (try variable)

semiSection :: Parser [Var]
semiSection = do
  tok $ string' "semi" >> optional (string' "-continuous" <|> string' "s")
  many (try variable)

sosSection :: Parser [SOS]
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
    return (l,t,xs)
  where
    typ = do
      t <- tok $ (char' 's' >> ((char '1' >> return S1) <|> (char '2' >> return S2)))
      tok (string "::")
      return t

-- ---------------------------------------------------------------------------

expr :: Parser Expr
expr = try expr1 <|> return []
  where
    expr1 :: Parser Expr
    expr1 = do
      t <- term True
      ts <- many (term False)
      return $ concat (t : ts)

sign :: Num a => Parser a
sign = tok ((char '+' >> return 1) <|> (char '-' >> return (-1)))

term :: Bool -> Parser Expr
term flag = do
  s <- if flag then optionMaybe sign else liftM Just sign
  c <- optionMaybe number
  e <- liftM (\s' -> [Term 1 [s']]) variable <|> qexpr
  return $ case combineMaybe (*) s c of
    Nothing -> e
    Just d -> [Term (d*c') vs | Term c' vs <- e]

qexpr :: Parser Expr
qexpr = do
  tok (char '[')
  t <- qterm True
  ts <- many (qterm False)
  tok (char ']')
  -- Gurobi allows ommiting "/2"
  (do mapM_ (tok . char) "/2"
      return [Term (r / 2) vs | Term r vs <- t:ts])
   <|> return (t:ts)

qterm :: Bool -> Parser Term
qterm flag = do
  s <- if flag then optionMaybe sign else liftM Just sign
  c <- optionMaybe number
  es <- qfactor `chainl1`  (tok (char '*') >> return (++))
  return $ case combineMaybe (*) s c of
    Nothing -> Term 1 es
    Just d -> Term d es

qfactor :: Parser [Var]
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
    nat = liftM read digits

    frac :: Parser Rational
    frac = do
      char '.'
      s <- digits
      return (read s % 10^(length s))

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
render :: LP -> Maybe String
render lp = fmap ($ "") $ execWriterT (render' lp)

render' :: LP -> WriterT ShowS Maybe ()
render' lp = do
  tell $ showString $
    case dir lp of
      OptMin -> "MINIMIZE"
      OptMax -> "MAXIMIZE"
  tell $ showChar '\n'

  do
    let (l, obj) = objectiveFunction lp
    renderLabel l
    renderExpr True obj
    tell $ showChar '\n'

  tell $ showString "SUBJECT TO\n"
  forM_ (constraints lp) $ \c -> do
    when (constrType c == NormalConstraint) $ do
      renderConstraint c
      tell $ showChar '\n'

  let lcs = [c | c <- constraints lp, constrType c == LazyConstraint]
  unless (null lcs) $ do
    tell $ showString "LAZY CONSTRAINTS\n"
    forM_ lcs $ \c -> do
      renderConstraint c
      tell $ showChar '\n'

  let cuts = [c | c <- constraints lp, constrType c == UserDefinedCut]
  unless (null cuts) $ do
    tell $ showString "USER CUTS\n"
    forM_ cuts $ \c -> do
      renderConstraint c
      tell $ showChar '\n'

  let ivs = integerVariables lp
      (bins,gens) = Set.partition (\v -> getBounds lp v == (Finite 0, Finite 1)) ivs
      scs = semiContinuousVariables lp

  tell $ showString "BOUNDS\n"
  forM_ (Map.toAscList (varInfo lp)) $ \(v, VarInfo{ varBounds = (lb,ub) }) -> do
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

  unless (null (sos lp)) $ do
    tell $ showString "SOS\n"
    forM_ (sos lp) $ \(l, typ, xs) -> do
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
renderExpr :: Bool -> Expr -> WriterT ShowS Maybe ()
renderExpr isObj e = fill 80 (ts1 ++ ts2)
  where
    (ts,qts) = partition isLin e 
    isLin (Term _ [])  = True
    isLin (Term _ [_]) = True
    isLin _ = False

    ts1 = map f ts
    ts2
      | null qts  = []
      | otherwise =
        -- マイナスで始めるとSCIP 2.1.1 は「cannot have '-' in front of quadratic part ('[')」というエラーを出す
        ["+ ["] ++ map g qts ++ [if isObj then "] / 2" else "]"]

    f :: Term -> String
    f (Term c [])  = showConstTerm c ""
    f (Term c [v]) = showCoeff c . showVar v $ ""
    f _ = error "should not happen"

    g :: Term -> String
    g (Term c vs) = 
      (if isObj then showCoeff (2*c) else showCoeff c)
      (intercalate " * " (map fromVar vs))

showVar :: Var -> ShowS
showVar = showString . fromVar

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

renderLabel :: Maybe Label -> WriterT ShowS Maybe ()
renderLabel l =
  case l of
    Nothing -> return ()
    Just s -> tell $ showString s . showString ": "

renderOp :: RelOp -> WriterT ShowS Maybe ()
renderOp Le = tell $ showString "<="
renderOp Ge = tell $ showString ">="
renderOp Eql = tell $ showString "="

renderConstraint :: Constraint -> WriterT ShowS Maybe ()
renderConstraint c@Constraint{ constrBody = (e,op,val) }  = do
  renderLabel (constrLabel c)
  case constrIndicator c of
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

renderBoundExpr :: BoundExpr -> WriterT ShowS Maybe ()
renderBoundExpr (Finite r) = tell $ showValue r
renderBoundExpr NegInf = tell $ showString "-inf"
renderBoundExpr PosInf = tell $ showString "+inf"

renderVariableList :: [Var] -> WriterT ShowS Maybe ()
renderVariableList vs = fill 80 (map fromVar vs) >> tell (showChar '\n')

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
