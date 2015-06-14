{-# LANGUAGE OverloadedStrings, BangPatterns, ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wall -fno-warn-unused-do-bind #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.Data.MIP.LPFile
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
module ToySolver.Data.MIP.LPFile
  ( parseString
  , parseFile
  , parser
  , render
  ) where

import Control.Applicative ((<$>), (<*))
import Control.Monad
import Control.Monad.Writer
import Control.Monad.ST
import Data.Char
import Data.Default.Class
import Data.List
import Data.Maybe
import Data.Ratio
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.STRef
import Data.String
import Data.OptDir
import System.IO
import Text.Parsec hiding (label)
import Text.Parsec.String

import qualified ToySolver.Data.MIP.Base as MIP
import ToySolver.Internal.Util (combineMaybe)
import ToySolver.Internal.TextUtil (readUnsignedInteger)

-- ---------------------------------------------------------------------------

-- | Parse a string containing LP file data.
-- The source name is only | used in error messages and may be the empty string.
parseString :: (MIP.IsVar v, RealFrac c) => MIP.FileOptions -> SourceName -> String -> Either ParseError (MIP.Problem v c)
parseString _ = parse (parser <* eof)

-- | Parse a file containing LP file data.
parseFile :: (MIP.IsVar v, RealFrac c) => MIP.FileOptions -> FilePath -> IO (Either ParseError (MIP.Problem v c))
parseFile opt fname = do
  h <- openFile fname ReadMode
  case MIP.optFileEncoding opt of
    Nothing -> return ()
    Just enc -> hSetEncoding h enc
  parse (parser <* eof) fname <$> hGetContents h

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

variable :: IsString s => Parser s
variable = do
  s <- ident
  return $! fromString s

label :: IsString s => Parser s
label = do
  name <- ident
  tok $ char ':'
  return $! fromString name

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

-- | LP file parser
parser :: (MIP.IsVar v, RealFrac c) => Parser (MIP.Problem v c)
parser = do
  name <- optionMaybe $ try $ do
    spaces
    string' "\\* Problem: " 
    manyTill anyChar (try (string " *\\\n"))
  sep
  obj <- problem

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
           , MIP.vars obj
           , MIP.vars ss
           ]
      isInt v  = v `Set.member` ints || v `Set.member` bins
      isSemi v = v `Set.member` scs
  return $
    MIP.Problem
    { MIP.name              = name
    , MIP.objectiveFunction = obj
    , MIP.constraints       = [c | Left c <- cs]
    , MIP.userCuts          = [c | Right c <- cs]
    , MIP.sosConstraints    = ss
    , MIP.varType           = Map.fromAscList
       [ ( v
         , if isInt v then
             if isSemi v then MIP.SemiIntegerVariable
             else MIP.IntegerVariable
           else
             if isSemi v then MIP.SemiContinuousVariable
             else MIP.ContinuousVariable
         )
       | v <- Set.toAscList vs ]
    , MIP.varBounds         = Map.fromAscList [ (v, Map.findWithDefault MIP.defaultBounds v bnds2) | v <- Set.toAscList vs]
    }

problem :: (MIP.IsVar v, RealFrac c) => Parser (MIP.ObjectiveFunction v c)
problem = do
  flag <-  (try minimize >> return OptMin)
       <|> (try maximize >> return OptMax)
  name <- optionMaybe (try label)
  obj <- expr
  return def{ MIP.objLabel = name, MIP.objDir = flag, MIP.objExpr = obj }

minimize, maximize :: Parser ()
minimize = tok $ string' "min" >> optional (string' "imize")
maximize = tok $ string' "max" >> optional (string' "imize")

end :: Parser ()
end = tok $ string' "end"

-- ---------------------------------------------------------------------------

constraintSection :: (MIP.IsVar v, RealFrac c) => Parser [MIP.Constraint v c]
constraintSection = subjectTo >> many (try (constraint False))

subjectTo :: Parser ()
subjectTo = msum
  [ try $ tok (string' "subject") >> tok (string' "to")
  , try $ tok (string' "such") >> tok (string' "that")
  , try $ tok (string' "st")
  , try $ tok (string' "s") >> optional (tok (char '.')) >> tok (string' "t")
        >> tok (char '.') >> return ()
  ]

constraint :: (MIP.IsVar v, RealFrac c) => Bool -> Parser (MIP.Constraint v c)
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
  rhs <- liftM (s*) number

  let (lb,ub) =
        case op of
          MIP.Le -> (MIP.NegInf, MIP.Finite rhs)
          MIP.Ge -> (MIP.Finite rhs, MIP.PosInf)
          MIP.Eql -> (MIP.Finite rhs, MIP.Finite rhs)
         
  return $ MIP.Constraint
    { MIP.constrLabel     = name
    , MIP.constrIndicator = g
    , MIP.constrExpr      = e
    , MIP.constrLB        = lb
    , MIP.constrUB        = ub
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

lazyConstraintsSection :: (MIP.IsVar v, RealFrac c) => Parser [MIP.Constraint v c]
lazyConstraintsSection = do
  tok $ string' "lazy"
  tok $ string' "constraints"
  many $ try $ constraint True

userCutsSection :: (MIP.IsVar v, RealFrac c) => Parser [MIP.Constraint v c]
userCutsSection = do
  tok $ string' "user"
  tok $ string' "cuts"
  many $ try $ constraint False

type Bounds2 c = (Maybe (MIP.BoundExpr c), Maybe (MIP.BoundExpr c))

boundsSection :: (MIP.IsVar v, RealFrac c) => Parser (Map v (MIP.Bounds c))
boundsSection = do
  tok $ string' "bound" >> optional (char' 's')
  liftM (Map.map g . Map.fromListWith f) $ many (try bound)
  where
    f (lb1,ub1) (lb2,ub2) = (combineMaybe max lb1 lb2, combineMaybe min ub1 ub2)
    g (lb, ub) = ( fromMaybe MIP.defaultLB lb
                 , fromMaybe MIP.defaultUB ub
                 )

bound :: (MIP.IsVar v, RealFrac c) => Parser (v, Bounds2 c)
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

boundExpr :: (RealFrac c) => Parser (MIP.BoundExpr c)
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

generalSection :: MIP.IsVar v => Parser [v]
generalSection = do
  tok $ string' "gen" >> optional (string' "eral" >> optional (string' "s"))
  many (try variable)

binarySection :: MIP.IsVar v => Parser [v]
binarySection = do
  tok $ string' "bin" >> optional (string' "ar" >> (string' "y" <|> string' "ies"))
  many (try variable)

semiSection :: MIP.IsVar v => Parser [v]
semiSection = do
  tok $ string' "semi" >> optional (string' "-continuous" <|> string' "s")
  many (try variable)

sosSection :: (MIP.IsVar v, RealFrac c) => Parser [MIP.SOSConstraint v c]
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

expr :: forall v c. (MIP.IsVar v, RealFrac c) => Parser (MIP.Expr v c)
expr = try expr1 <|> return 0
  where
    expr1 :: Parser (MIP.Expr v c)
    expr1 = do
      t <- term True
      ts <- many (term False)
      return $ sum (t : ts)

sign :: Num a => Parser a
sign = tok ((char '+' >> return 1) <|> (char '-' >> return (-1)))

term :: (MIP.IsVar v, RealFrac c) => Bool -> Parser (MIP.Expr v c)
term flag = do
  s <- if flag then optionMaybe sign else liftM Just sign
  c <- optionMaybe number
  e <- liftM MIP.varExpr variable <|> qexpr
  return $ case combineMaybe (*) s c of
    Nothing -> e
    Just d -> MIP.constExpr d * e

qexpr :: (MIP.IsVar v, RealFrac c) => Parser (MIP.Expr v c)
qexpr = do
  tok (char '[')
  t <- qterm True
  ts <- many (qterm False)
  let e = MIP.Expr (t:ts)
  tok (char ']')
  -- Gurobi allows ommiting "/2"
  (do mapM_ (tok . char) ("/2" :: String) -- Explicit type signature is necessary because the type of mapM_ in GHC-7.10 is generalized for arbitrary Foldable
      return $ MIP.constExpr (1/2) * e)
   <|> return e

qterm :: (MIP.IsVar v, RealFrac c) => Bool -> Parser (MIP.Term v c)
qterm flag = do
  s <- if flag then optionMaybe sign else liftM Just sign
  c <- optionMaybe number
  es <- qfactor `chainl1`  (tok (char '*') >> return (++))
  return $ case combineMaybe (*) s c of
    Nothing -> MIP.Term 1 es
    Just d -> MIP.Term d es

qfactor :: (MIP.IsVar v) => Parser [v]
qfactor = do
  v <- variable
  msum [ tok (char '^') >> tok (char '2') >> return [v,v]
       , return [v]
       ]

number :: RealFrac c => Parser c
number = tok $ do
  b <- (do{ x <- nat; y <- option 0 frac; return (fromInteger x + y) })
    <|> frac
  c <- option 0 e
  return $ fromRational (b*10^^c)
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
render :: (MIP.IsVar v, RealFrac c) => MIP.FileOptions -> MIP.Problem v c -> Either String String
render _ mip = Right $ execM $ render' $ normalize mip

writeVar :: MIP.IsVar v => v -> M ()
writeVar v = writeString $ MIP.fromVar v

render' :: (MIP.IsVar v, RealFrac c) => MIP.Problem v c -> M ()
render' mip = do
  case MIP.name mip of
    Just name -> writeString $ "\\* Problem: " ++ name ++ " *\\\n"
    Nothing -> return ()

  let obj = MIP.objectiveFunction mip   
  
  writeString $
    case MIP.objDir obj of
      OptMin -> "MINIMIZE"
      OptMax -> "MAXIMIZE"
  writeChar '\n'

  renderLabel (MIP.objLabel obj)
  renderExpr True (MIP.objExpr obj)
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
  forM_ (Map.toAscList (MIP.varBounds mip)) $ \(v, (lb,ub)) -> do
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
renderExpr :: forall v c. (MIP.IsVar v, RealFrac c) => Bool -> MIP.Expr v c -> M ()
renderExpr isObj e = fill 80 (ts1 ++ ts2)
  where
    (ts,qts) = partition isLin (MIP.terms e)
    isLin (MIP.Term _ [])  = True
    isLin (MIP.Term _ [_]) = True
    isLin _ = False

    ts1 = map f ts
    ts2
      | null qts  = []
      | otherwise =
        -- マイナスで始めるとSCIP 2.1.1 は「cannot have '-' in front of quadratic part ('[')」というエラーを出す
        -- SCIP-3.1.0 does not allow spaces between '/' and '2'.
        ["+ ["] ++ map g qts ++ [if isObj then "] /2" else "]"]

    f :: MIP.Term v c -> String
    f (MIP.Term c [])  = showConstTerm c
    f (MIP.Term c [v]) = showCoeff c ++ MIP.fromVar v
    f _ = error "should not happen"

    g :: MIP.Term v c -> String
    g (MIP.Term c vs) = 
      (if isObj then showCoeff (2*c) else showCoeff c) ++
      intercalate " * " (map MIP.fromVar vs)

showValue :: (RealFrac c) => c -> String
showValue x =
  if denominator c == 1
    then show (numerator c)
    else show (fromRational c :: Double)
  where
    c = realToFrac x

showCoeff :: (RealFrac c) => c -> String
showCoeff c =
  if c' == 1
    then s
    else s ++ showValue c' ++ " "
  where
    c' = abs c
    s = if c >= 0 then "+ " else "- "

showConstTerm :: (RealFrac c) => c -> String
showConstTerm c = s ++ v
  where
    s = if c >= 0 then "+ " else "- "
    v = showValue (abs c)

renderLabel :: MIP.IsVar v => Maybe v -> M ()
renderLabel l =
  case l of
    Nothing -> return ()
    Just s -> writeString (MIP.fromVar s) >> writeString ": "

renderOp :: MIP.RelOp -> M ()
renderOp MIP.Le = writeString "<="
renderOp MIP.Ge = writeString ">="
renderOp MIP.Eql = writeString "="

renderConstraint :: (MIP.IsVar v, RealFrac c) => MIP.Constraint v c -> M ()
renderConstraint c@MIP.Constraint{ MIP.constrExpr = e, MIP.constrLB = lb, MIP.constrUB = ub } = do
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
  let (op, val) =
        case (lb, ub) of
          (MIP.NegInf, MIP.Finite x) -> (MIP.Le, x)
          (MIP.Finite x, MIP.PosInf) -> (MIP.Ge, x)
          (MIP.Finite x1, MIP.Finite x2) | x1==x2 -> (MIP.Eql, x1)
          _ -> error "ToySolver.Data.MIP.LPFile.renderConstraint: should not happen"
  renderOp op
  writeChar ' '
  writeString $ showValue val

renderBoundExpr :: (RealFrac c) => MIP.BoundExpr c -> M ()
renderBoundExpr (MIP.Finite r) = writeString $ showValue r
renderBoundExpr MIP.NegInf = writeString "-inf"
renderBoundExpr MIP.PosInf = writeString "+inf"

renderVariableList :: (MIP.IsVar v) => [v] -> M ()
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

normalize :: (MIP.IsVar v, RealFrac c) => MIP.Problem v c -> MIP.Problem v c
normalize = removeEmptyExpr . removeRangeConstraints

removeRangeConstraints :: (MIP.IsVar v, Real c) => MIP.Problem v c -> MIP.Problem v c
removeRangeConstraints prob = runST $ do
  vsRef <- newSTRef $ MIP.variables prob
  cntRef <- newSTRef (0::Int)
  newvsRef <- newSTRef []
            
  let gensym = do
        vs <- readSTRef vsRef
        let loop !c = do
              let v = fromString ("~r_" ++ show c)
              if v `Set.member` vs then
                loop (c+1)
              else do
                writeSTRef cntRef $! c+1
                modifySTRef vsRef (Set.insert v)
                return v
        loop =<< readSTRef cntRef

  cs2 <- forM (MIP.constraints prob) $ \c -> do
    case (MIP.constrLB c, MIP.constrUB c) of
      (MIP.NegInf, MIP.Finite _) -> return c
      (MIP.Finite _, MIP.PosInf) -> return c
      (MIP.Finite x1, MIP.Finite x2) | x1 == x2 -> return c
      (lb, ub) -> do
        v <- gensym
        modifySTRef newvsRef ((v, (lb,ub)) :)
        return $
          c
          { MIP.constrExpr = MIP.constrExpr c - MIP.varExpr v
          , MIP.constrLB = 0
          , MIP.constrUB = 0
          }

  newvs <- liftM reverse $ readSTRef newvsRef
  return $
    prob
    { MIP.constraints = cs2
    , MIP.varType = MIP.varType prob `Map.union` Map.fromList [(v, MIP.ContinuousVariable) | (v,_) <- newvs]
    , MIP.varBounds = MIP.varBounds prob `Map.union` (Map.fromList newvs)
    }
          
removeEmptyExpr :: (MIP.IsVar v, RealFrac c) => MIP.Problem v c -> MIP.Problem v c
removeEmptyExpr prob =
  prob
  { MIP.objectiveFunction = obj{ MIP.objExpr = convertExpr (MIP.objExpr obj) }
  , MIP.constraints = map convertConstr $ MIP.constraints prob
  , MIP.userCuts    = map convertConstr $ MIP.userCuts prob
  }
  where
    obj = MIP.objectiveFunction prob
    
    convertExpr (MIP.Expr []) = MIP.Expr [MIP.Term 0 [fromString "x0"]]
    convertExpr e = e

    convertConstr constr =
      constr
      { MIP.constrExpr = convertExpr $ MIP.constrExpr constr
      }
