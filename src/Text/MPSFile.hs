{-# OPTIONS_GHC -Wall -fno-warn-unused-do-bind #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Text.MPSFile
-- Copyright   :  (c) Masahiro Sakai 2012-2014
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  portable
--
-- A .mps format parser library.
-- 
-- References:
-- 
-- * <http://pic.dhe.ibm.com/infocenter/cosinfoc/v12r4/topic/ilog.odms.cplex.help/CPLEX/File_formats_reference/topics/MPS_synopsis.html>
-- 
-- * <http://pic.dhe.ibm.com/infocenter/cosinfoc/v12r4/topic/ilog.odms.cplex.help/CPLEX/File_formats_reference/topics/MPS_ext_synopsis.html>
-- 
-- * <http://www.gurobi.com/documentation/5.0/reference-manual/node744>
--
-- * <http://en.wikipedia.org/wiki/MPS_(format)>
--
-----------------------------------------------------------------------------
module Text.MPSFile
  ( parseString
  , parseFile
  ) where

import Control.Monad
import Data.Maybe
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Ratio
import Data.Interned
import Data.Interned.String

import qualified Text.ParserCombinators.Parsec as P
import Text.ParserCombinators.Parsec hiding (spaces, newline, Column)

import Data.OptDir
import qualified Data.MIP as MIP
import ToySolver.Internal.TextUtil (readUnsignedInteger)

type Column = MIP.Var
type Row = InternedString

data BoundType
  = LO	-- lower bound
  | UP	-- upper bound
  | FX	-- variable is fixed at the specified value
  | FR	-- free variable (no lower or upper bound)
  | MI	-- infinite lower bound
  | PL	-- infinite upper bound
  | BV	-- variable is binary (equal 0 or 1)
  | LI	-- lower bound for integer variable
  | UI	-- upper bound for integer variable
  | SC	-- upper bound for semi-continuous variable
  deriving (Eq, Ord, Show, Read)

-- ---------------------------------------------------------------------------

-- | Parse a string containing LP file data.
-- The source name is only | used in error messages and may be the empty string.
parseString :: SourceName -> String -> Either ParseError MIP.Problem
parseString = parse mpsfile

-- | Parse a file containing LP file data.
parseFile :: FilePath -> IO (Either ParseError MIP.Problem)
parseFile = parseFromFile mpsfile

-- ---------------------------------------------------------------------------

space' :: Parser Char
space' = oneOf [' ', '\t']

spaces' :: Parser ()
spaces' = skipMany space'

spaces1' :: Parser ()
spaces1' = skipMany1 space'

commentline :: Parser ()
commentline = do
  _ <- char '*'
  _ <- manyTill anyChar P.newline
  return ()

newline' :: Parser ()
newline' = do
  spaces'
  _ <- P.newline
  skipMany commentline
  return ()

tok :: Parser a -> Parser a
tok p = do
  x <- p
  msum [spaces1', lookAhead (try (char '\n' >> return ())), eof]
  return x

row :: Parser Row
row = liftM intern ident

column :: Parser Column
column = liftM MIP.toVar ident

ident :: Parser String
ident = tok $ many1 $ noneOf [' ', '\t', '\n']

stringLn :: String -> Parser ()
stringLn s = string s >> newline'

sign :: Num a => Parser a
sign = (char '+' >> return 1) <|> (char '-' >> return (-1))

number :: Parser Rational
number = tok $ do
  b <- (do{ s <- option 1 sign; x <- nat; y <- option 0 frac; return (s * (fromInteger x + y)) })
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

mpsfile :: Parser MIP.Problem
mpsfile = do
  many commentline

  _name <- nameSection

  -- http://pic.dhe.ibm.com/infocenter/cosinfoc/v12r4/topic/ilog.odms.cplex.help/CPLEX/File_formats_reference/topics/MPS_ext_objsen.html
  -- CPLEX extends the MPS standard by allowing two additional sections: OBJSEN and OBJNAME.
  -- If these options are used, they must appear in order and as the first and second sections after the NAME section. 
  objsense <- optionMaybe $ objSenseSection
  objname  <- optionMaybe $ objNameSection

  rows <- rowsSection

  -- http://pic.dhe.ibm.com/infocenter/cosinfoc/v12r4/topic/ilog.odms.cplex.help/CPLEX/File_formats_reference/topics/MPS_ext_usercuts.html
  -- The order of sections must be ROWS USERCUTS.  
  usercuts <- option [] userCutsSection

  -- http://pic.dhe.ibm.com/infocenter/cosinfoc/v12r4/topic/ilog.odms.cplex.help/CPLEX/File_formats_reference/topics/MPS_ext_lazycons.html
  -- The order of sections must be ROWS USERCUTS LAZYCONS.
  lazycons <- option [] lazyConsSection

  (cols, intvs1) <- colsSection
  rhss <- rhsSection
  rngs <- option Map.empty rangesSection
  bnds <- option [] boundsSection

  -- http://pic.dhe.ibm.com/infocenter/cosinfoc/v12r4/topic/ilog.odms.cplex.help/CPLEX/File_formats_reference/topics/MPS_ext_quadobj.html
  -- Following the BOUNDS section, a QMATRIX section may be specified.
  qobj <- msum [quadObjSection, qMatrixSection, return []]

  -- http://pic.dhe.ibm.com/infocenter/cosinfoc/v12r4/topic/ilog.odms.cplex.help/CPLEX/File_formats_reference/topics/MPS_ext_sos.html
  -- Note that in an MPS file, the SOS section must follow the BOUNDS section.
  sos <- option [] sosSection

  -- http://pic.dhe.ibm.com/infocenter/cosinfoc/v12r4/topic/ilog.odms.cplex.help/CPLEX/File_formats_reference/topics/MPS_ext_qcmatrix.html
  -- QCMATRIX sections appear after the optional SOS section. 
  qterms <- liftM Map.fromList $ many qcMatrixSection

  -- http://pic.dhe.ibm.com/infocenter/cosinfoc/v12r4/topic/ilog.odms.cplex.help/CPLEX/File_formats_reference/topics/MPS_ext_indicators.html
  -- The INDICATORS section follows any quadratic constraint section and any quadratic objective section.
  inds <- option Map.empty indicatorsSection

  string "ENDATA"

  let objrow =
        case objname of
          Nothing -> head [r | (Nothing, r) <- rows] -- XXX
          Just r  -> intern r
      objdir =
        case objsense of
          Nothing -> OptMin
          Just d  -> d
      vs     = Map.keysSet cols
      intvs2 = Set.fromList [col | (t,col,_) <- bnds, t `elem` [BV,LI,UI]]
      scvs   = Set.fromList [col | (SC,col,_) <- bnds]

  let explicitBounds = Map.fromListWith f
        [ case typ of
            LO -> (col, (Just (MIP.Finite val), Nothing))
            UP -> (col, (Nothing, Just (MIP.Finite val)))
            FX -> (col, (Just (MIP.Finite val), Just (MIP.Finite val)))
            FR -> (col, (Just MIP.NegInf, Just MIP.PosInf))
            MI -> (col, (Just MIP.NegInf, Nothing))
            PL -> (col, (Nothing, Just MIP.PosInf))
            BV -> (col, (Just (MIP.Finite 0), Just (MIP.Finite 1)))
            LI -> (col, (Just (MIP.Finite val), Nothing))
            UI -> (col, (Nothing, Just (MIP.Finite val)))
            SC -> (col, (Nothing, Just (MIP.Finite val)))
        | (typ,col,val) <- bnds ]
        where
          f (a1,b1) (a2,b2) = (g a1 a2, g b1 b2)
          g _ (Just x) = Just x
          g x Nothing  = x

  let bounds = Map.fromList
        [ case Map.lookup v explicitBounds of
            Nothing ->
              if v `Set.member` intvs1
              then
                -- http://eaton.math.rpi.edu/cplex90html/reffileformatscplex/reffileformatscplex9.html
                -- If no bounds are specified for the variables within markers, bounds of 0 (zero) and 1 (one) are assumed.
                (v, (MIP.Finite 0, MIP.Finite 1))
              else
                (v, (MIP.Finite 0, MIP.PosInf))
            Just (Nothing, Just (MIP.Finite ub)) | ub < 0 ->
              {-
                http://pic.dhe.ibm.com/infocenter/cosinfoc/v12r4/topic/ilog.odms.cplex.help/CPLEX/File_formats_reference/topics/MPS_records.html
                If no bounds are specified, CPLEX assumes a lower
                bound of 0 (zero) and an upper bound of +∞. If only a
                single bound is specified, the unspecified bound
                remains at 0 or +∞, whichever applies, with one
                exception. If an upper bound of less than 0 is
                specified and no other bound is specified, the lower
                bound is automatically set to -∞. CPLEX deviates
                slightly from a convention used by some MPS readers
                when it encounters an upper bound of 0 (zero). Rather
                than automatically set this variable’s lower bound to
                -∞, CPLEX accepts both a lower and upper bound of 0,
                effectively fixing that variable at 0. CPLEX resets
                the lower bound to -∞ only if the upper bound is less
                than 0. A warning message is issued when this
                exception is encountered.
              -}
              (v, (MIP.NegInf, MIP.Finite ub))
            {-
              lp_solve uses 1 as default lower bound for semi-continuous variable.
              <http://lpsolve.sourceforge.net/5.5/mps-format.htm>
              But Gurobi Optimizer uses 0 as default lower bound for semi-continuous variable.
              Here we adopt Gurobi's way.
            -}
{-
            Just (Nothing, ub) | v `Set.member` scvs ->
              (v, (MIP.Finite 1, fromMaybe MIP.PosInf ub))
-}
            Just (lb,ub) ->
              (v, (fromMaybe (MIP.Finite 0) lb, fromMaybe MIP.PosInf ub))
        | v <- Set.toList vs ]

  let rowCoeffs :: Map Row (Map Column Rational)
      rowCoeffs = Map.fromListWith Map.union [(row, Map.singleton col coeff) | (col,m) <- Map.toList cols, (row,coeff) <- Map.toList m]

  let f :: Bool -> (Maybe MIP.RelOp, Row) -> [MIP.Constraint]
      f _isLazy (Nothing, _row) = mzero
      f isLazy (Just op, row) = do
        let lhs = [MIP.Term c　[col] | (col,c) <- Map.toList (Map.findWithDefault Map.empty row rowCoeffs)]
                  ++ Map.findWithDefault [] row qterms
        let rhs = Map.findWithDefault 0 row rhss
        (op2,rhs2) <-
          case Map.lookup row rngs of
            Nothing  -> return (op, rhs)
            Just rng ->
              case op of
                MIP.Ge  -> [(MIP.Ge, rhs), (MIP.Le, rhs + abs rng)]
                MIP.Le  -> [(MIP.Ge, rhs - abs rng), (MIP.Le, rhs)]
                MIP.Eql ->
                  if rng < 0
                  then [(MIP.Ge, rhs + rng), (MIP.Le, rhs)]
                  else [(MIP.Ge, rhs), (MIP.Le, rhs + rng)]
        return $
          MIP.Constraint
          { MIP.constrLabel     = Just $ unintern row
          , MIP.constrIndicator = Map.lookup row inds
          , MIP.constrIsLazy    = isLazy
          , MIP.constrBody      = (lhs, op2, rhs2)
          }

  let mip =
        MIP.Problem
        { MIP.dir                     = objdir
        , MIP.objectiveFunction       =
            ( Just (unintern objrow)
            , [MIP.Term c [col] | (col,m) <- Map.toList cols, c <- maybeToList (Map.lookup objrow m)] ++ qobj
            )
        , MIP.constraints           = concatMap (f False) rows ++ concatMap (f True) lazycons
        , MIP.sosConstraints        = sos
        , MIP.userCuts              = concatMap (f False) usercuts
        , MIP.varInfo               =
            Map.fromAscList
            [ ( v
              , MIP.VarInfo
                { MIP.varBounds = Map.findWithDefault MIP.defaultBounds v bounds
                , MIP.varType   =
                    if v `Set.member` intvs1 || v `Set.member` intvs2 then MIP.IntegerVariable
                    else if v `Set.member` scvs then MIP.SemiContinuousVariable
                    else MIP.ContinuousVariable
                }
              )
            | v <- Set.toAscList vs
            ]
        }

  return mip

nameSection :: Parser (Maybe String)
nameSection = do
  string "NAME"
  n <- optionMaybe $ do
    spaces1'
    ident
  newline'
  return n

objSenseSection :: Parser OptDir
objSenseSection = do
  try $ stringLn "OBJSENSE"
  spaces1'
  d <-  (try (stringLn "MAX") >> return OptMax)
    <|> (stringLn "MIN" >> return OptMin)
  return d

objNameSection :: Parser String
objNameSection = do
  try $ stringLn "OBJNAME"
  spaces1'
  name <- ident
  newline'
  return name

rowsSection :: Parser [(Maybe MIP.RelOp, Row)]
rowsSection = do
  try $ stringLn "ROWS"
  rowsBody

userCutsSection :: Parser [(Maybe MIP.RelOp, Row)]
userCutsSection = do
  try $ stringLn "USERCUTS"
  rowsBody

lazyConsSection :: Parser [(Maybe MIP.RelOp, Row)]
lazyConsSection = do
  try $ stringLn "LAZYCONS"
  rowsBody

rowsBody :: Parser [(Maybe MIP.RelOp, Row)]
rowsBody = many $ do
  spaces1'
  op <- msum
        [ char 'N' >> return Nothing
        , char 'G' >> return (Just MIP.Ge)
        , char 'L' >> return (Just MIP.Le)
        , char 'E' >> return (Just MIP.Eql)
        ]
  spaces1'
  name <- row
  newline'
  return (op, name)

colsSection :: Parser (Map Column (Map Row Rational), Set Column)
colsSection = do
  try $ stringLn "COLUMNS"
  body False Map.empty Set.empty
  where
    body :: Bool -> Map Column (Map Row Rational) -> Set Column -> Parser (Map Column (Map Row Rational), Set Column)
    body isInt rs ivs = msum
      [ do isInt' <- try intMarker
           body isInt' rs ivs
      , do (k,v) <- entry
           let rs'  = Map.insertWith Map.union k v rs
               ivs' = if isInt then Set.insert k ivs else ivs
           seq rs' $ seq ivs' $ body isInt rs' ivs'
      , return (rs, ivs)
      ]

    intMarker :: Parser Bool
    intMarker = do
      spaces1'
      _marker <- ident 
      string "'MARKER'"
      spaces1'
      b <-  (try (string "'INTORG'") >> return True)
        <|> (string "'INTEND'" >> return False)
      newline'
      return b

    entry :: Parser (Column, Map Row Rational)
    entry = do
      spaces1'
      col <- column
      rv1 <- rowAndVal
      opt <- optionMaybe rowAndVal
      newline'
      case opt of
        Nothing -> return (col, rv1)
        Just rv2 ->  return (col, Map.union rv1 rv2)

rowAndVal :: Parser (Map Row Rational)
rowAndVal = do
  r <- row
  val <- number
  return $ Map.singleton r val

rhsSection :: Parser (Map Row Rational)
rhsSection = do
  try $ stringLn "RHS"
  liftM Map.unions $ many entry
  where
    entry = do
      spaces1'
      _name <- ident
      rv1 <- rowAndVal
      opt <- optionMaybe rowAndVal
      newline'
      case opt of
        Nothing  -> return rv1
        Just rv2 -> return $ Map.union rv1 rv2

rangesSection :: Parser (Map Row Rational)
rangesSection = do
  try $ stringLn "RANGES"
  liftM Map.unions $ many entry
  where
    entry = do
      spaces1'
      _name <- ident
      rv1 <- rowAndVal
      opt <- optionMaybe rowAndVal
      newline'
      case opt of
        Nothing  -> return rv1
        Just rv2 -> return $ Map.union rv1 rv2

boundsSection :: Parser [(BoundType, Column, Rational)]
boundsSection = do
  try $ stringLn "BOUNDS"
  many entry
  where
    entry = do
      spaces1'
      typ   <- boundType
      _name <- ident
      col   <- column
      val   <- if typ `elem` [FR, BV, MI, PL]
               then return 0
               else number
      newline'
      return (typ, col, val)

boundType :: Parser BoundType
boundType = tok $ do
  let ks = ["LO", "UP", "FX", "FR", "MI", "PL", "BV", "LI", "UI", "SC"]
  msum [try (string k) >> return (read k) | k <- ks]

sosSection :: Parser [MIP.SOSConstraint]
sosSection = do
  try $ stringLn "SOS"
  many entry
  where
    entry = do
      spaces1'
      typ <-  (try (string "S1") >> return MIP.S1)
          <|> (string "S2" >> return MIP.S2)
      spaces1'
      name <- ident
      newline'
      xs <- many (try identAndVal)
      return $ MIP.SOSConstraint{ MIP.sosLabel = Just name, MIP.sosType = typ, MIP.sosBody = xs }

    identAndVal :: Parser (Column, Rational)
    identAndVal = do
      spaces1'
      col <- column
      val <- number
      newline'
      return (col, val)

quadObjSection :: Parser [MIP.Term]
quadObjSection = do
  try $ stringLn "QUADOBJ"
  many entry
  where
    entry = do
      spaces1'
      col1 <- column
      col2 <- column
      val  <- number
      newline'
      return $ MIP.Term (if col1 /= col2 then val else val / 2) [col1, col2]

qMatrixSection :: Parser [MIP.Term]
qMatrixSection = do
  try $ stringLn "QMATRIX"
  many entry
  where
    entry = do
      spaces1'
      col1 <- column
      col2 <- column
      val  <- number
      newline'
      return $ MIP.Term (val / 2) [col1, col2]

qcMatrixSection :: Parser (Row, [MIP.Term])
qcMatrixSection = do
  try $ stringLn "QCMATRIX"
  spaces1'
  r <- row
  xs <- many entry
  return (r, xs)
  where
    entry = do
      spaces1'
      col1 <- column
      col2 <- column
      val  <- number
      newline'
      return $ MIP.Term val [col1, col2]

indicatorsSection :: Parser (Map Row (Column, Rational))
indicatorsSection = do
  try $ stringLn "INDICATORS"
  liftM Map.fromList $ many entry
  where
    entry = do
      spaces1'
      string "IF"
      spaces1'
      r <- row
      var <- column
      val <- number
      newline'
      return (r, (var, val))
