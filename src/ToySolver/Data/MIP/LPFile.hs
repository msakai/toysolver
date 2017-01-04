{-# LANGUAGE ConstraintKinds, CPP, OverloadedStrings, BangPatterns, FlexibleContexts, ScopedTypeVariables, TypeFamilies #-}
{-# OPTIONS_GHC -Wall -fno-warn-unused-do-bind #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.Data.MIP.LPFile
-- Copyright   :  (c) Masahiro Sakai 2011-2014
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  non-portable (ConstraintKinds, CPP, OverloadedStrings, BangPatterns, FlexibleContexts, ScopedTypeVariables, TypeFamilies)
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

import Control.Applicative
import Control.Monad
import Control.Monad.Writer
import Control.Monad.ST
import Data.Char
import Data.Default.Class
import Data.Functor.Identity
import Data.Interned
import Data.List
import Data.Maybe
import Data.Monoid
import Data.Scientific (Scientific)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.STRef
import Data.String
import qualified Data.Text as T
import qualified Data.Text.Lazy as TL
import Data.Text.Lazy.Builder (Builder)
import qualified Data.Text.Lazy.Builder as B
import qualified Data.Text.Lazy.Builder.Scientific as B
import qualified Data.Text.Lazy.IO as TLIO
import Data.OptDir
import System.IO
import Text.Megaparsec hiding (label, string', char')
import qualified Text.Megaparsec.Lexer as P
import Text.Megaparsec.Prim (MonadParsec ())

import qualified ToySolver.Data.MIP.Base as MIP
import ToySolver.Internal.Util (combineMaybe)

-- ---------------------------------------------------------------------------

#if MIN_VERSION_megaparsec(5,0,0)
type C e s m = (MonadParsec e s m, Token s ~ Char)
#else
type C e s m = (MonadParsec s m Char)
#endif

-- | Parse a string containing LP file data.
-- The source name is only | used in error messages and may be the empty string.
#if MIN_VERSION_megaparsec(5,0,0)
parseString :: (Stream s, Token s ~ Char) => MIP.FileOptions -> String -> s -> Either (ParseError Char Dec) (MIP.Problem Scientific)
#else
parseString :: Stream s Char => MIP.FileOptions -> String -> s -> Either ParseError (MIP.Problem Scientific)
#endif
parseString _ = parse (parser <* eof)

-- | Parse a file containing LP file data.
#if MIN_VERSION_megaparsec(5,0,0)
parseFile :: MIP.FileOptions -> FilePath -> IO (Either (ParseError Char Dec) (MIP.Problem Scientific))
#else
parseFile :: MIP.FileOptions -> FilePath -> IO (Either ParseError (MIP.Problem Scientific))
#endif
parseFile opt fname = do
  h <- openFile fname ReadMode
  case MIP.optFileEncoding opt of
    Nothing -> return ()
    Just enc -> hSetEncoding h enc
  parse (parser <* eof) fname <$> TLIO.hGetContents h

-- ---------------------------------------------------------------------------

char' :: C e s m => Char -> m Char
char' c = (char c <|> char (toUpper c)) <?> show c

string' :: C e s m => String -> m ()
string' s = mapM_ char' s <?> show s

sep :: C e s m => m ()
sep = skipMany ((comment >> return ()) <|> (spaceChar >> return ()))

comment :: C e s m => m ()
comment = do
  char '\\'
  skipManyTill anyChar (try newline)

tok :: C e s m => m a -> m a
tok p = do
  x <- p
  sep
  return x

ident :: C e s m => m String
ident = tok $ do
  x <- letterChar <|> oneOf syms1 
  xs <- many (alphaNumChar <|> oneOf syms2)
  let s = x:xs 
  guard $ map toLower s `Set.notMember` reserved
  return s
  where
    syms1 = "!\"#$%&()/,;?@_`'{}|~"
    syms2 = '.' : syms1

variable :: C e s m => m MIP.Var
variable = liftM MIP.toVar ident

label :: C e s m => m MIP.Label
label = do
  name <- ident
  tok $ char ':'
  return $! T.pack name

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
#if MIN_VERSION_megaparsec(5,0,0)
parser :: (MonadParsec e s m, Token s ~ Char) => m (MIP.Problem Scientific)
#else
parser :: MonadParsec s m Char => m (MIP.Problem Scientific)
#endif
parser = do
  name <- optional $ try $ do
    space
    string' "\\* Problem: " 
    liftM fromString $ manyTill anyChar (try (string " *\\\n"))
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

problem :: C e s m => m (MIP.ObjectiveFunction Scientific)
problem = do
  flag <-  (try minimize >> return OptMin)
       <|> (try maximize >> return OptMax)
  name <- optional (try label)
  obj <- expr
  return def{ MIP.objLabel = name, MIP.objDir = flag, MIP.objExpr = obj }

minimize, maximize :: C e s m => m ()
minimize = tok $ string' "min" >> optional (string' "imize") >> return ()
maximize = tok $ string' "max" >> optional (string' "imize") >> return ()

end :: C e s m => m ()
end = tok $ string' "end"

-- ---------------------------------------------------------------------------

constraintSection :: C e s m => m [MIP.Constraint Scientific]
constraintSection = subjectTo >> many (try (constraint False))

subjectTo :: C e s m => m ()
subjectTo = msum
  [ try $ tok (string' "subject") >> tok (string' "to")
  , try $ tok (string' "such") >> tok (string' "that")
  , try $ tok (string' "st")
  , try $ tok (string' "s") >> optional (tok (char '.')) >> tok (string' "t")
        >> tok (char '.') >> return ()
  ]

constraint :: C e s m => Bool -> m (MIP.Constraint Scientific)
constraint isLazy = do
  name <- optional (try label)
  g <- optional $ try indicator

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

relOp :: C e s m => m MIP.RelOp
relOp = tok $ msum
  [ char '<' >> optional (char '=') >> return MIP.Le
  , char '>' >> optional (char '=') >> return MIP.Ge
  , char '=' >> msum [ char '<' >> return MIP.Le
                     , char '>' >> return MIP.Ge
                     , return MIP.Eql
                     ]
  ]

indicator :: C e s m => m (MIP.Var, Scientific)
indicator = do
  var <- variable
  tok (char '=')
  val <- tok ((char '0' >> return 0) <|> (char '1' >> return 1))
  tok $ string "->"
  return (var, val)

lazyConstraintsSection :: C e s m => m [MIP.Constraint Scientific]
lazyConstraintsSection = do
  tok $ string' "lazy"
  tok $ string' "constraints"
  many $ try $ constraint True

userCutsSection :: C e s m => m [MIP.Constraint Scientific]
userCutsSection = do
  tok $ string' "user"
  tok $ string' "cuts"
  many $ try $ constraint False

type Bounds2 c = (Maybe (MIP.BoundExpr c), Maybe (MIP.BoundExpr c))

boundsSection :: C e s m => m (Map MIP.Var (MIP.Bounds Scientific)) 
boundsSection = do
  tok $ string' "bound" >> optional (char' 's')
  liftM (Map.map g . Map.fromListWith f) $ many (try bound)
  where
    f (lb1,ub1) (lb2,ub2) = (combineMaybe max lb1 lb2, combineMaybe min ub1 ub2)
    g (lb, ub) = ( fromMaybe MIP.defaultLB lb
                 , fromMaybe MIP.defaultUB ub
                 )

bound :: C e s m => m (MIP.Var, Bounds2 Scientific)
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

boundExpr :: C e s m => m (MIP.BoundExpr Scientific)
boundExpr = msum 
  [ try (tok (char '+') >> inf >> return MIP.PosInf)
  , try (tok (char '-') >> inf >> return MIP.NegInf)
  , do
      s <- option 1 sign
      x <- number
      return $ MIP.Finite (s*x)
  ]

inf :: C e s m => m ()
inf = tok (string "inf" >> optional (string "inity")) >> return ()

-- ---------------------------------------------------------------------------

generalSection :: C e s m => m [MIP.Var]
generalSection = do
  tok $ string' "gen" >> optional (string' "eral" >> optional (string' "s"))
  many (try variable)

binarySection :: C e s m => m [MIP.Var]
binarySection = do
  tok $ string' "bin" >> optional (string' "ar" >> (string' "y" <|> string' "ies"))
  many (try variable)

semiSection :: C e s m => m [MIP.Var]
semiSection = do
  tok $ string' "semi" >> optional (string' "-continuous" <|> string' "s")
  many (try variable)

sosSection :: C e s m => m [MIP.SOSConstraint Scientific]
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

expr :: forall e s m. C e s m => m (MIP.Expr Scientific)
expr = try expr1 <|> return 0
  where
    expr1 :: m (MIP.Expr Scientific)
    expr1 = do
      t <- term True
      ts <- many (term False)
      return $ foldr (+) 0 (t : ts)

sign :: (C e s m, Num a) => m a
sign = tok ((char '+' >> return 1) <|> (char '-' >> return (-1)))

term :: C e s m => Bool -> m (MIP.Expr Scientific)
term flag = do
  s <- if flag then optional sign else liftM Just sign
  c <- optional number
  e <- liftM MIP.varExpr variable <|> qexpr
  return $ case combineMaybe (*) s c of
    Nothing -> e
    Just d -> MIP.constExpr d * e

qexpr :: C e s m => m (MIP.Expr Scientific)
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

qterm :: C e s m => Bool -> m (MIP.Term Scientific)
qterm flag = do
  s <- if flag then optional sign else liftM Just sign
  c <- optional number
  es <- do
    e <- qfactor
    es <- many (tok (char '*') >> qfactor)
    return $ e ++ concat es
  return $ case combineMaybe (*) s c of
    Nothing -> MIP.Term 1 es
    Just d -> MIP.Term d es

qfactor :: C e s m => m [MIP.Var]
qfactor = do
  v <- variable
  msum [ tok (char '^') >> tok (char '2') >> return [v,v]
       , return [v]
       ]

number :: forall e s m. C e s m => m Scientific
number = tok $ P.signed sep P.number
 
skipManyTill :: Alternative m => m a -> m end -> m ()
skipManyTill p end = scan
  where
    scan = (end *> pure ()) <|> (p *> scan)

-- ---------------------------------------------------------------------------

type M a = Writer Builder a

execM :: M a -> TL.Text
execM m = B.toLazyText $ execWriter m

writeString :: T.Text -> M ()
writeString s = tell $ B.fromText s

writeChar :: Char -> M ()
writeChar c = tell $ B.singleton c

-- ---------------------------------------------------------------------------

-- | Render a problem into a string.
render :: MIP.FileOptions -> MIP.Problem Scientific -> Either String TL.Text
render _ mip = Right $ execM $ render' $ normalize mip

writeVar :: MIP.Var -> M ()
writeVar v = writeString $ unintern v

render' :: MIP.Problem Scientific -> M ()
render' mip = do
  case MIP.name mip of
    Just name -> writeString $ "\\* Problem: " <> name <> " *\\\n"
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
      writeString $ fromString $ show typ
      writeString " ::"
      forM_ xs $ \(v, r) -> do
        writeString "  "
        writeVar v
        writeString " : "
        tell $ B.scientificBuilder r
      writeChar '\n'

  writeString "END\n"

-- FIXME: Gurobi は quadratic term が最後に一つある形式でないとダメっぽい
renderExpr :: Bool -> MIP.Expr Scientific -> M ()
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

    f :: MIP.Term Scientific -> T.Text
    f (MIP.Term c [])  = showConstTerm c
    f (MIP.Term c [v]) = showCoeff c <> fromString (MIP.fromVar v)
    f _ = error "should not happen"

    g :: MIP.Term Scientific -> T.Text
    g (MIP.Term c vs) = 
      (if isObj then showCoeff (2*c) else showCoeff c) <>
      mconcat (intersperse " * " (map (fromString . MIP.fromVar) vs))

showValue :: Scientific -> T.Text
showValue = fromString . show

showCoeff :: Scientific -> T.Text
showCoeff c =
  if c' == 1
    then s
    else s <> showValue c' <> " "
  where
    c' = abs c
    s = if c >= 0 then "+ " else "- "

showConstTerm :: Scientific -> T.Text
showConstTerm c = s <> showValue (abs c)
  where
    s = if c >= 0 then "+ " else "- "

renderLabel :: Maybe MIP.Label -> M ()
renderLabel l =
  case l of
    Nothing -> return ()
    Just s -> writeString s >> writeString ": "

renderOp :: MIP.RelOp -> M ()
renderOp MIP.Le = writeString "<="
renderOp MIP.Ge = writeString ">="
renderOp MIP.Eql = writeString "="

renderConstraint :: MIP.Constraint Scientific -> M ()
renderConstraint c@MIP.Constraint{ MIP.constrExpr = e, MIP.constrLB = lb, MIP.constrUB = ub } = do
  renderLabel (MIP.constrLabel c)
  case MIP.constrIndicator c of
    Nothing -> return ()
    Just (v,vval) -> do
      writeVar v
      writeString " = "
      tell $ B.scientificBuilder vval
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
  tell $ B.scientificBuilder val

renderBoundExpr :: MIP.BoundExpr Scientific -> M ()
renderBoundExpr (MIP.Finite r) = tell $ B.scientificBuilder r
renderBoundExpr MIP.NegInf = writeString "-inf"
renderBoundExpr MIP.PosInf = writeString "+inf"

renderVariableList :: [MIP.Var] -> M ()
renderVariableList vs = fill 80 (map (fromString . MIP.fromVar) vs) >> writeChar '\n'

fill :: Int -> [T.Text] -> M ()
fill width str = go str 0
  where
    go [] _ = return ()
    go (x:xs) 0 = writeString x >> go xs (T.length x)
    go (x:xs) w =
      if w + 1 + T.length x <= width
        then writeChar ' ' >> writeString x >> go xs (w + 1 + T.length x)
        else writeChar '\n' >> go (x:xs) 0

-- ---------------------------------------------------------------------------

{-
compileExpr :: Expr -> Maybe (Map Var Scientific)
compileExpr e = do
  xs <- forM e $ \(Term c vs) ->
    case vs of
      [v] -> return (v, c)
      _ -> mzero
  return (Map.fromList xs)
-}

-- ---------------------------------------------------------------------------

normalize :: (Eq r, Num r) => MIP.Problem r -> MIP.Problem r
normalize = removeEmptyExpr . removeRangeConstraints

removeRangeConstraints :: (Eq r, Num r) => MIP.Problem r -> MIP.Problem r
removeRangeConstraints prob = runST $ do
  vsRef <- newSTRef $ MIP.variables prob
  cntRef <- newSTRef (0::Int)
  newvsRef <- newSTRef []
            
  let gensym = do
        vs <- readSTRef vsRef
        let loop !c = do
              let v = MIP.toVar ("~r_" ++ show c)
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
          , MIP.constrLB = MIP.Finite 0
          , MIP.constrUB = MIP.Finite 0
          }

  newvs <- liftM reverse $ readSTRef newvsRef
  return $
    prob
    { MIP.constraints = cs2
    , MIP.varType = MIP.varType prob `Map.union` Map.fromList [(v, MIP.ContinuousVariable) | (v,_) <- newvs]
    , MIP.varBounds = MIP.varBounds prob `Map.union` (Map.fromList newvs)
    }

removeEmptyExpr :: Num r => MIP.Problem r -> MIP.Problem r
removeEmptyExpr prob =
  prob
  { MIP.objectiveFunction = obj{ MIP.objExpr = convertExpr (MIP.objExpr obj) }
  , MIP.constraints = map convertConstr $ MIP.constraints prob
  , MIP.userCuts    = map convertConstr $ MIP.userCuts prob
  }
  where
    obj = MIP.objectiveFunction prob
    
    convertExpr (MIP.Expr []) = MIP.Expr [MIP.Term 0 [MIP.toVar "x0"]]
    convertExpr e = e

    convertConstr constr =
      constr
      { MIP.constrExpr = convertExpr $ MIP.constrExpr constr
      }
