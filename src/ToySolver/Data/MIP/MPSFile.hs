{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_GHC -Wall -fno-warn-unused-do-bind #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.Data.MIP.MPSFile
-- Copyright   :  (c) Masahiro Sakai 2012-2014
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  non-portable (TypeFamilies)
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
module ToySolver.Data.MIP.MPSFile
  ( parseString
  , parseFile
  , parser
  , render
  ) where

import Control.Applicative ((<*))
import Control.Monad
import Control.Monad.Writer
import Data.Default.Class
import Data.Maybe
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Ratio
import Data.Interned
import Data.Interned.String

import qualified Text.Parsec as P
import Text.Parsec hiding (spaces, newline, Column)
import Text.Parsec.String
import Text.Printf

import Data.OptDir
import qualified ToySolver.Data.MIP.Base as MIP
import ToySolver.Internal.TextUtil (readUnsignedInteger)

type Column = MIP.Var
type Row = InternedString

data BoundType
  = LO  -- lower bound
  | UP  -- upper bound
  | FX  -- variable is fixed at the specified value
  | FR  -- free variable (no lower or upper bound)
  | MI  -- infinite lower bound
  | PL  -- infinite upper bound
  | BV  -- variable is binary (equal 0 or 1)
  | LI  -- lower bound for integer variable
  | UI  -- upper bound for integer variable
  | SC  -- upper bound for semi-continuous variable
  | SI  -- upper bound for semi-integer variable
  deriving (Eq, Ord, Show, Read, Enum, Bounded)

-- ---------------------------------------------------------------------------

-- | Parse a string containing MPS file data.
-- The source name is only | used in error messages and may be the empty string.
parseString :: SourceName -> String -> Either ParseError MIP.Problem
parseString = parse (parser <* eof)

-- | Parse a file containing MPS file data.
parseFile :: FilePath -> IO (Either ParseError MIP.Problem)
parseFile = parseFromFile (parser <* eof)

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

-- | MPS file parser
parser :: Parser MIP.Problem
parser = do
  many commentline

  name <- nameSection

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
  P.spaces

  let objrow =
        case objname of
          Nothing -> head [r | (Nothing, r) <- rows] -- XXX
          Just r  -> intern r
      objdir =
        case objsense of
          Nothing -> OptMin
          Just d  -> d
      vs     = Map.keysSet cols `Set.union` Set.fromList [col | (_,col,_) <- bnds]
      intvs2 = Set.fromList [col | (t,col,_) <- bnds, t `elem` [BV,LI,UI]]
      scvs   = Set.fromList [col | (SC,col,_) <- bnds]
      sivs   = Set.fromList [col | (SI,col,_) <- bnds]

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
            SI -> (col, (Nothing, Just (MIP.Finite val)))
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
      f _isLazy (Nothing, _row) = []
      f isLazy (Just op, row) = do
        let lhs = [MIP.Term c [col] | (col,c) <- Map.toList (Map.findWithDefault Map.empty row rowCoeffs)]
                  ++ Map.findWithDefault [] row qterms
        let rhs = Map.findWithDefault 0 row rhss
            (lb,ub) =
              case Map.lookup row rngs of
                Nothing  ->
                  case op of
                    MIP.Ge  -> (MIP.Finite rhs, MIP.PosInf)
                    MIP.Le  -> (MIP.NegInf, MIP.Finite rhs)
                    MIP.Eql -> (MIP.Finite rhs, MIP.Finite rhs)
                Just rng ->
                  case op of
                    MIP.Ge  -> (MIP.Finite rhs, MIP.Finite (rhs + abs rng))
                    MIP.Le  -> (MIP.Finite (rhs - abs rng), MIP.Finite rhs)
                    MIP.Eql ->
                      if rng < 0
                      then (MIP.Finite (rhs + rng), MIP.Finite rhs)
                      else (MIP.Finite rhs, MIP.Finite (rhs + rng))
        return $
          MIP.Constraint
          { MIP.constrLabel     = Just $ unintern row
          , MIP.constrIndicator = Map.lookup row inds
          , MIP.constrIsLazy    = isLazy
          , MIP.constrExpr      = MIP.Expr lhs
          , MIP.constrLB        = lb
          , MIP.constrUB        = ub
          }

  let mip =
        MIP.Problem
        { MIP.name                  = name
        , MIP.objectiveFunction     = def
            { MIP.objDir = objdir
            , MIP.objLabel = Just (unintern objrow)
            , MIP.objExpr = MIP.Expr $ [MIP.Term c [col] | (col,m) <- Map.toList cols, c <- maybeToList (Map.lookup objrow m)] ++ qobj
            }
        , MIP.constraints           = concatMap (f False) rows ++ concatMap (f True) lazycons
        , MIP.sosConstraints        = sos
        , MIP.userCuts              = concatMap (f False) usercuts
        , MIP.varType               = Map.fromAscList
            [ ( v
              , if v `Set.member` sivs then
                  MIP.SemiIntegerVariable
                else if v `Set.member` intvs1 && v `Set.member` scvs then
                  MIP.SemiIntegerVariable
                else if v `Set.member` intvs1 || v `Set.member` intvs2 then
                  MIP.IntegerVariable
                else if v `Set.member` scvs then
                  MIP.SemiContinuousVariable
                else
                  MIP.ContinuousVariable
              )
            | v <- Set.toAscList vs ]
        , MIP.varBounds             = Map.fromAscList [(v, Map.findWithDefault MIP.defaultBounds v bounds) | v <- Set.toAscList vs]
        }

  return mip

nameSection :: Parser (Maybe String)
nameSection = do
  string "NAME"
  n <- optionMaybe $ try $ do
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
  msum [try (string (show k)) >> return k | k <- [minBound..maxBound]]

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
  try $ string "QCMATRIX"
  spaces1'
  r <- row
  newline'
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

-- ---------------------------------------------------------------------------

type M a = Writer ShowS a

execM :: M a -> String
execM m = execWriter m ""

writeString :: String -> M ()
writeString s = tell $ showString s

writeChar :: Char -> M ()
writeChar c = tell $ showChar c

-- ---------------------------------------------------------------------------

render :: MIP.Problem -> Either String String
render mip | not (checkAtMostQuadratic mip) = Left "Expression must be atmost quadratic"
render mip = Right $ execM $ render' $ nameRows mip

render' :: MIP.Problem -> M ()
render' mip = do
  let probName = fromMaybe "" (MIP.name mip)

  -- NAME section
  -- The name starts in column 15 in fixed formats.
  writeSectionHeader $ "NAME" ++ replicate 10 ' ' ++ probName
  
  let MIP.ObjectiveFunction
       { MIP.objLabel = Just objName
       , MIP.objDir = dir
       , MIP.objExpr = obj
       } = MIP.objectiveFunction mip

  -- OBJSENSE section
  -- Note: GLPK-4.48 does not support this section.
  writeSectionHeader "OBJSENSE"
  case dir of
    OptMin -> writeFields ["MIN"]
    OptMax -> writeFields ["MAX"]

{-
  -- OBJNAME section
  -- Note: GLPK-4.48 does not support this section.
  writeSectionHeader "OBJNAME"
  writeFields [objName]
-}

  let splitRange c =
        case (MIP.constrLB c, MIP.constrUB c) of
          (MIP.Finite x, MIP.PosInf) -> ((MIP.Ge, x), Nothing)
          (MIP.NegInf, MIP.Finite x) -> ((MIP.Le, x), Nothing)
          (MIP.Finite x1, MIP.Finite x2)
            | x1 == x2 -> ((MIP.Eql, x1), Nothing)
            | x1 < x2  -> ((MIP.Eql, x1), Just (x2 - x1))
          _ -> error "invalid constraint bound"

  let renderRows cs = do
        forM_ cs $ \c -> do
          let ((op,_), _) = splitRange c
          let s = case op of
                    MIP.Le  -> "L"
                    MIP.Ge  -> "G"
                    MIP.Eql -> "E"
          writeFields [s, fromJust $ MIP.constrLabel c]

  -- ROWS section
  writeSectionHeader "ROWS"
  writeFields ["N", objName]
  renderRows [c | c <- MIP.constraints mip, not (MIP.constrIsLazy c)]

  -- USERCUTS section
  unless (null (MIP.userCuts mip)) $ do
    writeSectionHeader "USERCUTS"
    renderRows (MIP.userCuts mip)

  -- LAZYCONS section
  let lcs = [c | c <- MIP.constraints mip, MIP.constrIsLazy c]
  unless (null lcs) $ do
    writeSectionHeader "LAZYCONS"
    renderRows lcs

  -- COLUMNS section
  writeSectionHeader "COLUMNS"
  let cols :: Map Column (Map String Rational)
      cols = Map.fromListWith Map.union
             [ (v, Map.singleton l d)
             | (Just l, xs) <-
                 (Just objName, obj) :
                 [(MIP.constrLabel c, lhs) | c <- MIP.constraints mip ++ MIP.userCuts mip, let lhs = MIP.constrExpr c]
             , MIP.Term d [v] <- MIP.terms xs
             ]
      f col xs =
        forM_ (Map.toList xs) $ \(row, d) -> do
          writeFields ["", unintern col, row, showValue d]
      ivs = MIP.integerVariables mip `Set.union` MIP.semiIntegerVariables mip
  forM_ (Map.toList (Map.filterWithKey (\col _ -> col `Set.notMember` ivs) cols)) $ \(col, xs) -> f col xs
  unless (Set.null ivs) $ do
    writeFields ["", "MARK0000", "'MARKER'", "", "'INTORG'"]
    forM_ (Map.toList (Map.filterWithKey (\col _ -> col `Set.member` ivs) cols)) $ \(col, xs) -> f col xs
    writeFields ["", "MARK0001", "'MARKER'", "", "'INTEND'"]

  -- RHS section
  let rs = [(fromJust $ MIP.constrLabel c, rhs) | c <- MIP.constraints mip ++ MIP.userCuts mip, let ((_,rhs),_) = splitRange c, rhs /= 0]
  writeSectionHeader "RHS"
  forM_ rs $ \(name, val) -> do
    writeFields ["", "rhs", name, showValue val]

  -- RANGES section
  let rngs = [(fromJust $ MIP.constrLabel c, fromJust rng) | c <- MIP.constraints mip ++ MIP.userCuts mip, let ((_,_), rng) = splitRange c, isJust rng]
  unless (null rngs) $ do
    writeSectionHeader "RANGES"
    forM_ rngs $ \(name, val) -> do
      writeFields ["", "rhs", name, showValue val]

  -- BOUNDS section
  writeSectionHeader "BOUNDS"
  forM_ (Map.toList (MIP.varType mip)) $ \(col, vt) -> do
    let (lb,ub) = MIP.getBounds mip col
    case (lb,ub)  of
      (MIP.NegInf, MIP.PosInf) -> do
        -- free variable (no lower or upper bound)
        writeFields ["FR", "bound", unintern col]
                  
      (MIP.Finite 0, MIP.Finite 1) | vt == MIP.IntegerVariable -> do
        -- variable is binary (equal 0 or 1)
        writeFields ["BV", "bound", unintern col] 

      (MIP.Finite a, MIP.Finite b) | a == b -> do
        -- variable is fixed at the specified value
        writeFields ["FX", "bound", unintern col, showValue a]

      _ -> do
        case lb of
          MIP.PosInf -> error "should not happen"
          MIP.NegInf -> do
            -- Minus infinity
            writeFields ["MI", "bound", unintern col]
          MIP.Finite 0 | vt == MIP.ContinuousVariable -> return ()
          MIP.Finite a -> do
            let t = case vt of
                      MIP.IntegerVariable -> "LI" -- lower bound for integer variable
                      _ -> "LO" -- Lower bound
            writeFields [t, "bound", unintern col, showValue a]

        case ub of
          MIP.NegInf -> error "should not happen"
          MIP.PosInf | vt == MIP.ContinuousVariable -> return ()
          MIP.PosInf -> do
            when (vt == MIP.SemiContinuousVariable || vt == MIP.SemiIntegerVariable) $
              error "cannot express +inf upper bound of semi-continuous or semi-integer variable"
            writeFields ["PL", "bound", unintern col] -- Plus infinity
          MIP.Finite a -> do
            let t = case vt of
                      MIP.SemiContinuousVariable -> "SC" -- Upper bound for semi-continuous variable
                      MIP.SemiIntegerVariable ->
                        -- Gurobi uses "SC" while lpsolve uses "SI" for upper bound of semi-integer variable
                        "SC"
                      MIP.IntegerVariable -> "UI" -- Upper bound for integer variable
                      _ -> "UP" -- Upper bound
            writeFields [t, "bound", unintern col, showValue a]

  -- QMATRIX section
  -- Gurobiは対称行列になっていないと "qmatrix isn't symmetric" というエラーを発生させる
  let qm = Map.map (2*) $ quadMatrix obj
  unless (Map.null qm) $ do
    writeSectionHeader "QMATRIX"
    forM_ (Map.toList qm) $ \(((v1,v2), val)) -> do
      writeFields ["", unintern v1, unintern v2, showValue val]

  -- SOS section
  unless (null (MIP.sosConstraints mip)) $ do
    writeSectionHeader "SOS"
    forM_ (MIP.sosConstraints mip) $ \sos -> do
      let t = case MIP.sosType sos of
                MIP.S1 -> "S1"
                MIP.S2 -> "S2"
      writeFields $ t : maybeToList (MIP.sosLabel sos)
      forM_ (MIP.sosBody sos) $ \(var,val) -> do
        writeFields ["", unintern var, showValue val]

  -- QCMATRIX section
  let xs = [ (fromJust $ MIP.constrLabel c, qm)
           | c <- MIP.constraints mip ++ MIP.userCuts mip
           , let lhs = MIP.constrExpr c
           , let qm = quadMatrix lhs
           , not (Map.null qm) ]
  unless (null xs) $ do
    forM_ xs $ \(row, qm) -> do
      -- The name starts in column 12 in fixed formats.
      writeSectionHeader $ "QCMATRIX" ++ replicate 3 ' ' ++ row
      forM_ (Map.toList qm) $ \((v1,v2), val) -> do
        writeFields ["", unintern v1, unintern v2, showValue val]

  -- INDICATORS section
  -- Note: Gurobi-5.6.3 does not support this section.
  let ics = [c | c <- MIP.constraints mip, isJust $ MIP.constrIndicator c]
  unless (null ics) $ do
    writeSectionHeader "INDICATORS"
    forM_ ics $ \c -> do
      let Just (var,val) = MIP.constrIndicator c
      writeFields ["IF", fromJust (MIP.constrLabel c), unintern var, showValue val]

  -- ENDATA section
  writeSectionHeader "ENDATA"

writeSectionHeader :: String -> M ()
writeSectionHeader s = writeString s >> writeChar '\n'

-- Fields start in column 2, 5, 15, 25, 40 and 50
writeFields :: [String] -> M ()
writeFields xs = f1 xs >> writeChar '\n'
  where
    -- columns 1-4
    f1 [] = return ()
    f1 [x] = writeString (' ' : x)
    f1 (x:xs) = do
      writeString $ printf " %-2s " x
      f2 xs

    -- columns 5-14
    f2 [] = return ()
    f2 [x] = writeString x
    f2 (x:xs) = do
      writeString $ printf "%-9s " x
      f3 xs

    -- columns 15-24
    f3 [] = return ()
    f3 [x] = writeString x
    f3 (x:xs) = do
      writeString $ printf "%-9s " x
      f4 xs

    -- columns 25-39
    f4 [] = return ()
    f4 [x] = writeString x
    f4 (x:xs) = do
      writeString $ printf "%-14s " x
      f5 xs

    -- columns 40-49
    f5 [] = return ()
    f5 [x] = writeString x
    f5 (x:xs) = do
      writeString $ printf "%-19s " x
      f6 xs

    -- columns 50-
    f6 [] = return ()
    f6 [x] = writeString x
    f6 _ = error "MPSFile: >6 fields (this should not happen)"

showValue :: Rational -> String
showValue c =
  if denominator c == 1
    then show (numerator c)
    else show (fromRational c :: Double)
 
nameRows :: MIP.Problem -> MIP.Problem
nameRows mip
  = mip
  { MIP.objectiveFunction = (MIP.objectiveFunction mip){ MIP.objLabel = Just objName' }
  , MIP.constraints = f (MIP.constraints mip) ["row" ++ show n | n <- [(1::Int)..]]
  , MIP.userCuts = f (MIP.userCuts mip) ["usercut" ++ show n | n <- [(1::Int)..]]
  , MIP.sosConstraints = g (MIP.sosConstraints mip) ["sos" ++ show n | n <- [(1::Int)..]]
  }
  where
    objName = MIP.objLabel $ MIP.objectiveFunction mip
    used = Set.fromList $ catMaybes $ objName : [MIP.constrLabel c | c <- MIP.constraints mip ++ MIP.userCuts mip] ++ [MIP.sosLabel c | c <- MIP.sosConstraints mip]
    objName' = fromMaybe (head [name | n <- [(1::Int)..], let name = "obj" ++ show n, name `Set.notMember` used]) objName

    f [] _ = []
    f (c:cs) (name:names)
      | isJust (MIP.constrLabel c) = c : f cs (name:names)
      | name `Set.notMember` used = c{ MIP.constrLabel = Just name } : f cs names
      | otherwise = f (c:cs) names

    g [] _ = []
    g (c:cs) (name:names)
      | isJust (MIP.sosLabel c) = c : g cs (name:names)
      | name `Set.notMember` used = c{ MIP.sosLabel = Just name } : g cs names
      | otherwise = g (c:cs) names

quadMatrix :: MIP.Expr -> Map (MIP.Var, MIP.Var) Rational
quadMatrix e = Map.fromList $ do
  let m = Map.fromListWith (+) [(if v1<=v2 then (v1,v2) else (v2,v1), c) | MIP.Term c [v1,v2] <- MIP.terms e]
  ((v1,v2),c) <- Map.toList m
  if v1==v2 then
    [((v1,v2), c)]
  else
    [((v1,v2), c/2), ((v2,v1), c/2)]

checkAtMostQuadratic :: MIP.Problem -> Bool
checkAtMostQuadratic mip =  all (all f . MIP.terms) es
  where
    es = MIP.objExpr (MIP.objectiveFunction mip) :
         [lhs | c <- MIP.constraints mip ++ MIP.userCuts mip, let lhs = MIP.constrExpr c]
    f :: MIP.Term -> Bool
    f (MIP.Term _ [_]) = True
    f (MIP.Term _ [_,_]) = True
    f _ = False

-- ---------------------------------------------------------------------------
