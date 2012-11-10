-----------------------------------------------------------------------------
-- |
-- Module      :  Text.MPSFile
-- Copyright   :  (c) Masahiro Sakai 2012
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
import Control.Monad.Error
import Data.Char
import Data.List
import Data.Maybe
import qualified Data.Set as Set
import qualified Data.Map as Map

import Data.OptDir
import qualified Text.LPFile as LPFile

type M = Either String

type Column = String
type Row = String
type RHS = String

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

parseString :: String -> Either String LPFile.LP
parseString s = do
  let ls = [l | l <- lines s, not ("*" `isPrefixOf` l)]
  (_name, ls)    <- nameSection ls
  (objsense, ls) <- objSenseSection ls
  (objname, ls)  <- objNameSection ls
  (rows, ls)     <- rowsSection ls
  (usercuts, ls) <- userCutsSection ls
  (lazycons, ls) <- lazyConsSection ls
  (cols, ls)     <- colsSection ls
  (rhss, ls)     <- rhsSection ls
  (bnds, ls)     <- boundsSection ls
  (sos,  ls)     <- sosSection ls
  (qobj1, ls)    <- quadObjSection ls
  (qobj2, ls)    <- qMatrixSection ls
  (inds, ls)     <- indicatorsSection ls
  -- TODO: SOS
  (qterms, ls) <- qcMatrixSection ls
  guard $ ls == ["ENDATA"]

  let objrow =
        case objname of
          Nothing -> head [row | (Nothing, row) <- rows] -- XXX
          Just r  -> r
      objdir =
        case objsense of
          Nothing -> OptMin
          Just d  -> d
      vs     = Set.fromList [col | (col,_,_,_) <- cols]
      intvs1 = Set.fromList [col | (col,True,_,_) <- cols]
      intvs2 = Set.fromList [col | (t,_,col,_) <- bnds, t `elem` [BV,LI,UI]]
      scvs   = Set.fromList [col | (SC,_,col,_) <- bnds]

  let explicitBounds = Map.fromListWith f
        [ case typ of
            LO -> (col, (Just (LPFile.Finite val'), Nothing))
            UP -> (col, (Nothing, Just (LPFile.Finite val')))
            FX -> (col, (Just (LPFile.Finite val'), Just (LPFile.Finite val')))
            FR -> (col, (Just LPFile.NegInf, Just LPFile.PosInf))
            MI -> (col, (Just LPFile.NegInf, Nothing))
            PL -> (col, (Nothing, Just LPFile.PosInf))
            BV -> (col, (Just (LPFile.Finite 0), Just (LPFile.Finite 1)))
            LI -> (col, (Just (LPFile.Finite val'), Nothing))
            UI -> (col, (Nothing, Just (LPFile.Finite val')))
            SC -> (col, (Nothing, Just (LPFile.Finite val')))
        | (typ,_,col,val) <- bnds, let val' = toRational val ]
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
                (v, (LPFile.Finite 0, LPFile.Finite 1))
              else
                (v, (LPFile.Finite 0, LPFile.PosInf))
            Just (Nothing, Just (LPFile.Finite ub)) | ub < 0 ->
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
              (v, (LPFile.NegInf, LPFile.Finite (toRational ub)))
            Just (lb,ub) ->
              (v, (fromMaybe (LPFile.Finite 0) lb, fromMaybe LPFile.PosInf ub))
        | v <- Set.toList vs ]

  let lp =
        LPFile.LP
        { LPFile.variables               = Set.fromList [col | (col,_,_,_) <- cols]
        , LPFile.dir                     = objdir
        , LPFile.objectiveFunction       =
            ( Just objrow
            , [LPFile.Term (toRational c) [col] | (col,_,row,c) <- cols, objrow == row]
              ++ qobj1 ++ qobj2
            )
        , LPFile.constraints             =
            [ LPFile.Constraint
              { LPFile.constrType      = typ
              , LPFile.constrLabel     = Just row
              , LPFile.constrIndicator = Map.lookup row inds
              , LPFile.constrBody      =
                  ( [LPFile.Term (toRational c)　[col] | (col,_,row2,c) <- cols, row == row2]
                    ++ Map.findWithDefault [] row qterms 
                  , op
                  , head $ [toRational v | (_,row2,v) <- rhss, row == row2] ++ [0]
                  )
              }
            | (typ, (Just op, row)) <- zip (repeat LPFile.NormalConstraint) rows ++
                                       zip (repeat LPFile.UserDefinedCut) usercuts ++
                                       zip (repeat LPFile.LazyConstraint) lazycons
            ]
        , LPFile.bounds                  = bounds
        , LPFile.integerVariables        = intvs1 `Set.union` intvs2
        , LPFile.binaryVariables         = Set.empty
        , LPFile.semiContinuousVariables = scvs
        , LPFile.sos                     = sos
        }

  return lp

parseFile :: FilePath -> IO (Either String LPFile.LP)
parseFile fname = liftM parseString $ readFile fname

nameSection :: [String] -> M (Maybe String, [String])
nameSection (l:ls) =
  case words l of
    ["NAME"] -> return (Nothing, ls)
    ["NAME", n] -> return (Just n, ls)
    _ -> throwError "NAME expected"
nameSection [] = throwError "NAME expected"

objSenseSection :: [String] -> M (Maybe OptDir, [String])
objSenseSection ("OBJSENSE":l:ls) =
  case strip l of
    "MAX" -> return (Just OptMax, ls)
    "MIN" -> return (Just OptMin, ls)
    s     -> throwError ("unknown OBJSENSE: " ++ s)
objSenseSection ls = return (Nothing, ls)

objNameSection :: [String] -> M (Maybe String, [String])
objNameSection ("OBJNAME":l:ls) = return (Just (strip l), ls)
objNameSection ls = return (Nothing, ls)

rowsSection :: [String] -> M ([(Maybe LPFile.RelOp, Row)], [String])
rowsSection ("ROWS":ls) = rowsSection' ls
rowsSection _ = throwError "ROWS expected"

userCutsSection :: [String] -> M ([(Maybe LPFile.RelOp, Row)], [String])
userCutsSection ("USERCUTS":ls) = rowsSection' ls
userCutsSection ls = return ([], ls)

lazyConsSection :: [String] -> M ([(Maybe LPFile.RelOp, Row)], [String])
lazyConsSection ("LAZYCONS":ls) = rowsSection' ls
lazyConsSection ls = return ([], ls)

rowsSection' :: [String] -> M ([(Maybe LPFile.RelOp, Row)], [String])
rowsSection' lls@((' ':l):ls) =
  case words l of
    ["N",name] -> rowsSection' ls >>= \(xs, ls2) -> return ((Nothing, name) : xs, ls2)
    ["G",name] -> rowsSection' ls >>= \(xs, ls2) -> return ((Just LPFile.Ge,  name) : xs, ls2)
    ["L",name] -> rowsSection' ls >>= \(xs, ls2) -> return ((Just LPFile.Le,  name) : xs, ls2)
    ["E",name] -> rowsSection' ls >>= \(xs, ls2) -> return ((Just LPFile.Eql, name) : xs, ls2)
    _ -> return ([], lls)
rowsSection' ls = return ([],ls)

colsSection :: [String] -> M ([(Column, Bool, Row, Double)], [String])
colsSection ("COLUMNS":ls) = go ls False
  where
    go lls@((' ':l):ls) integrality =
      case words l of
        [_marker, "'MARKER'", "'INTORG'"] -> go ls True
        [_marker, "'MARKER'", "'INTEND'"] -> go ls False
        [col,row,val] -> do
          (xs,ls2) <- go ls integrality
          return ((col, integrality, row, read val) : xs, ls2)
        [col,row1,val1,row2,val2] -> do
          (xs,ls2) <- go ls integrality
          return ((col, integrality, row1, read val1) : (col, integrality, row2, read val2) : xs, ls2)
        _ ->
          return ([], lls)
    go ls _ = return ([],ls)
colsSection _ = throwError "COLUMNS expected"

rhsSection :: [String] -> M ([(RHS, Row, Double)], [String])
rhsSection ("RHS":ls) = go ls
  where
    go lls@((' ':l):ls) =
      case words l of
        [rhs,row,val] -> do
          (xs,ls2) <- go ls
          return ((rhs,row, read val) : xs, ls2)
        [rhs,row1,val1,row2,val2] -> do
          (xs,ls2) <- go ls
          return ((rhs,row1,read val1) : (rhs,row2,read val2) : xs, ls2)
        _ ->
          return ([], lls)
    go ls = return ([],ls)
rhsSection _ = throwError "RHS expected"

boundsSection :: [String] -> M ([(BoundType, String, Column, Double)], [String])
boundsSection ("BOUNDS":ls) = go ls
  where
    go lls@((' ':l):ls) =
      case words l of
        [typ, name, col, val] -> do
          (xs,ls2) <- go ls
          return ((read typ, name, col, read val) : xs, ls2)
        _ ->
          return ([], lls)
    go ls = return ([],ls)
boundsSection ls = return ([], ls)

sosSection :: [String] -> M ([(Maybe String, LPFile.SOSType, [(Column, Rational)])], [String])
sosSection ("SOS":ls) = go ls
  where
    go lls@((' ':l):ls) =
      case words l of
        ["S1", name] -> do
          (set,ls) <- go2 ls
          (xs,ls) <- go ls
          return ((Just name, LPFile.S1, set) : xs, ls)
        ["S2", name] -> do
          (set,ls) <- go2 ls
          (xs,ls) <- go ls
          return ((Just name, LPFile.S2, set) : xs, ls)
        _ ->
          return ([], lls)
    go ls = return ([],ls)
    go2 lls@((' ':l):ls) =
      case words l of
        [col, w] | all isDigit w -> do
          (set,ls) <- go2 ls
          return ((col, fromInteger (read w)) : set, ls)
        _ -> return ([],lls)
    go2 ls = return ([], ls)
sosSection ls = return ([], ls)

quadObjSection :: [String] -> M ([LPFile.Term], [String])
quadObjSection ("QUADOBJ":ls) = go ls
  where
    cplex = False
    go lls@((' ':l):ls) =
      case words l of
        [col1, col2, val] -> do
          (xs,ls2) <- go ls
          let val2 :: Double
              val2 = read val
              val3 =
                if cplex && col1 /= col2 -- XXX: CPLEXとGurobiで解釈が違う
                then toRational val2
                else toRational val2 / 2
          return (LPFile.Term val3 [col1, col2] : xs, ls2)
        _ ->
          return ([], lls)
    go ls = return ([], ls)
quadObjSection ls = return ([], ls)

qMatrixSection :: [String] -> M ([LPFile.Term], [String])
qMatrixSection lls@("QMATRIX":ls) = go ls
  where
    go lls@((' ':l):ls) =
      case words l of
        [col1, col2, val] -> do
          (xs,ls2) <- go ls
          let val2 :: Double
              val2 = read val
              val3 = toRational val2 / 2
          return (LPFile.Term val3 [col1, col2] : xs, ls2)
        _ ->
          return ([], lls)
    go ls = return ([], ls)
qMatrixSection ls = return ([], ls)

-- TODO: SOS section

qcMatrixSection :: [String] -> M (Map.Map Row [LPFile.Term], [String])
qcMatrixSection lls@(l:ls) =
  case words l of
    ["QCMATRIX", row] -> do
      (xs,ls)  <- go ls
      (m,ls) <- qcMatrixSection ls
      return (Map.insert row xs m, ls)
    _ -> return (Map.empty, lls)
  where
    go lls@((' ':l):ls) =
      case words l of
        [col1, col2, val] -> do
          (xs,ls2) <- go ls
          let val2 :: Double
              val2 = read val
          return (LPFile.Term (toRational val2) [col1, col2] : xs, ls2)
        _ ->
          return ([], lls)
    go ls = return ([], ls)
qcMatrixSection ls = return (Map.empty, ls)

indicatorsSection :: [String] -> M (Map.Map Row (Column, Rational), [String])
indicatorsSection lls@("INDICATORS":ls) = go ls
  where
    go lls@((' ':l):ls) =
      case words l of
        ["IF", row, var, val] -> do
          (xs,ls2) <- go ls
          let val2 :: Integer
              val2 = read val
          return (Map.insert row (var, toRational val2) xs, ls2)
        _ ->
          return (Map.empty, lls)
    go ls = return (Map.empty, ls)
indicatorsSection ls = return (Map.empty, ls)

strip :: String -> String
strip = reverse . f . reverse . f
  where
    f = dropWhile isSpace

testdata :: String
testdata = unlines
  [ "NAME          example2.mps"
  , "ROWS"
  , " N  obj     "
  , " L  c1      "
  , " L  c2      "
  , "COLUMNS"
  , "    x1        obj                 -1   c1                  -1"
  , "    x1        c2                   1"
  , "    x2        obj                 -2   c1                   1"
  , "    x2        c2                  -3"
  , "    x3        obj                 -3   c1                   1"
  , "    x3        c2                   1"
  , "RHS"
  , "    rhs       c1                  20   c2                  30"
  , "BOUNDS"
  , " UP BOUND     x1                  40"
  , "ENDATA"
  ]
