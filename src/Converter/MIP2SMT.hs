{-# OPTIONS_GHC -Wall #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Converter.MIP2SMT
-- Copyright   :  (c) Masahiro Sakai 2012-2014
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  experimental
-- Portability :  portable
--
-----------------------------------------------------------------------------
module Converter.MIP2SMT
  ( convert
  , Options (..)
  , defaultOptions
  , Language (..)
  ) where

import Data.Char
import Data.Ord
import Data.List
import Data.Ratio
import qualified Data.Set as Set
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.MIP as MIP
import System.IO
import Text.Printf
import qualified Text.LPFile as LPFile
import ToySolver.Util (showRationalAsFiniteDecimal)

data Options
  = Options
  { optLanguage     :: Language
  , optCheckSAT     :: Bool
  , optProduceModel :: Bool
  , optOptimize     :: Bool
  }
  deriving (Show, Eq, Ord)

defaultOptions :: Options
defaultOptions
  = Options
  { optLanguage     = SMTLIB2
  , optCheckSAT     = True
  , optProduceModel = True
  , optOptimize     = False
  }

data Language
  = SMTLIB2
  | YICES
  deriving (Show, Eq, Ord, Enum)

-- ------------------------------------------------------------------------

type Var = String
type Env = Map MIP.Var Var

concatS :: [ShowS] -> ShowS
concatS = foldr (.) id
 
unlinesS :: [ShowS] -> ShowS
unlinesS = concatS . map (. showChar '\n')

list :: [ShowS] -> ShowS
list xs = showParen True $ concatS (intersperse (showChar ' ') xs)

and' :: [ShowS] -> ShowS
and' [] = showString "true"
and' [x] = x
and' xs = list (showString "and" : xs)

or' :: [ShowS] -> ShowS
or' [] = showString "false"
or' [x] = x
or' xs = list (showString "or" : xs)

not' :: ShowS -> ShowS
not' x = list [showString "not", x]

expr :: Options -> Env -> MIP.Problem -> MIP.Expr -> ShowS
expr opt env mip e =
  case e of
    [] -> showChar '0'
    _ -> list (showChar '+' : map f e)
  where
    f (MIP.Term c []) = realNum opt c
    f (MIP.Term c vs) =
      case xs of
        [] -> realNum opt 1
        [x] -> x
        _ -> list (showChar '*' : xs)
      where
        xs = [realNum opt c | c /= 1] ++
             [ v3
             | v <- vs
             , let v2 = env Map.! v
             , let v3 = if MIP.getVarType mip v == MIP.IntegerVariable
                        then toReal opt (showString v2)
                        else showString v2
             ]

realNum :: Options -> Rational -> ShowS
realNum opt r =
  case optLanguage opt of
    SMTLIB2
      | r < 0     -> list [showChar '-', f (negate r)]
      | otherwise -> f r
    YICES ->
      if denominator r == 1
        then shows (numerator r)
        else shows (numerator r) . showChar '/' . shows (denominator r)
  where
    f r = case showRationalAsFiniteDecimal r of
            Just s  -> showString s
            Nothing -> list [showChar '/', shows (numerator r) . showString ".0", shows (denominator r) . showString ".0"]

rel :: Bool -> MIP.RelOp -> ShowS -> ShowS -> ShowS
rel True MIP.Eql x y = and' [rel False MIP.Le x y, rel False MIP.Ge x y]
rel _ MIP.Eql x y = list [showString "=", x, y]
rel _ MIP.Le x y = list [showString "<=", x, y]
rel _ MIP.Ge x y = list [showString ">=", x, y]

toReal :: Options -> ShowS -> ShowS
toReal opt x =
  case optLanguage opt of
    SMTLIB2 -> list [showString "to_real", x]
    YICES   -> x

assert :: Options -> (ShowS, Maybe String) -> ShowS
assert opt (x, label) = list [showString "assert", x']
  where
    x' = case label of
           Just name | optLanguage opt == SMTLIB2 ->
             list [ showString "!"
                  , x
                  , showString ":named"
                  , showString (encode opt name)
                  ]
           _ -> x

constraint :: Options -> Bool -> Env -> MIP.Problem -> MIP.Constraint -> (ShowS, Maybe String)
constraint opt q env mip
  MIP.Constraint
  { MIP.constrLabel     = label
  , MIP.constrIndicator = g
  , MIP.constrBody      = (e, op, b)
  } = (c1, label)
  where
    c0 = rel q op (expr opt env mip e) (realNum opt b)
    c1 = case g of
           Nothing -> c0
           Just (var,val) ->
             list [ showString "=>"
                  , rel q MIP.Eql (expr opt env mip [MIP.Term 1 [var]]) (realNum opt val)
                  , c0
                  ]

conditions :: Options -> Bool -> Env -> MIP.Problem -> [(ShowS, Maybe String)]
conditions opt q env mip = bnds ++ cs ++ ss
  where
    vs = MIP.variables mip
    bnds = map bnd (Set.toList vs)
    bnd v = (c1, Nothing)
      where
        v2 = env Map.! v
        v3 = if MIP.getVarType mip v == MIP.IntegerVariable
             then toReal opt (showString v2)
             else showString v2
        (lb,ub) = MIP.getBounds mip v
        s1 = case lb of
               MIP.NegInf -> []
               MIP.PosInf -> [showString "false"]
               MIP.Finite x -> [list [showString "<=", realNum opt x, v3]]
        s2 = case ub of
               MIP.NegInf -> [showString "false"]
               MIP.PosInf -> []
               MIP.Finite x -> [list [showString "<=", v3, realNum opt x]]
        c0 = and' (s1 ++ s2)
        c1 = if MIP.getVarType mip v == MIP.SemiContinuousVariable
             then or' [list [showString "=", showString v2, realNum opt 0], c0]
             else c0
    cs = map (constraint opt q env mip) (MIP.constraints mip)
    ss = concatMap sos (MIP.sosConstraints mip)
    sos (MIP.SOSConstraint label typ xs) = do
      (x1,x2) <- case typ of
                    MIP.S1 -> pairs $ map fst xs
                    MIP.S2 -> nonAdjacentPairs $ map fst $ sortBy (comparing snd) $ xs
      let c = not' $ and'
            [ list [showString "/=", v3, realNum opt 0]
            | v<-[x1,x2]
            , let v2 = env Map.! v
            , let v3 = if MIP.getVarType mip v == MIP.IntegerVariable
                       then toReal opt (showString v2)
                       else showString v2
            ]
      return (c, label)

pairs :: [a] -> [(a,a)]
pairs [] = []
pairs (x:xs) = [(x,x2) | x2 <- xs] ++ pairs xs

nonAdjacentPairs :: [a] -> [(a,a)]
nonAdjacentPairs (x1:x2:xs) = [(x1,x3) | x3 <- xs] ++ nonAdjacentPairs (x2:xs)
nonAdjacentPairs _ = []

convert :: Options -> MIP.Problem -> ShowS
convert opt mip =
  unlinesS $ options ++ defs ++ map (assert opt) (conditions opt False env mip)
             ++ [ assert opt (optimality, Nothing) | optOptimize opt ]
             ++ [ case optLanguage opt of
                    SMTLIB2 -> list [showString "check-sat"]
                    YICES   -> list [showString "check"]
                | optCheckSAT opt ]
  where
    vs = MIP.variables mip
    real_vs = vs `Set.difference` int_vs
    int_vs = MIP.integerVariables mip
    realType =
      case optLanguage opt of
        SMTLIB2 -> "Real"
        YICES   -> "real"
    intType  =
      case optLanguage opt of
        SMTLIB2 -> "Int"
        YICES   -> "int"
    ts = [(v, realType) | v <- Set.toList real_vs] ++ [(v, intType) | v <- Set.toList int_vs]
    obj = snd (MIP.objectiveFunction mip)
    env = Map.fromList [(v, encode opt (MIP.fromVar v)) | v <- Set.toList vs]
    -- Note that identifiers of LPFile does not contain '-'.
    -- So that there are no name crash.
    env2 = Map.fromList [(v, encode opt (MIP.fromVar v ++ "-2")) | v <- Set.toList vs]

    options =
      [ case optLanguage opt of
          SMTLIB2 -> list [showString "set-option", showString ":produce-models", showString "true"]
          YICES   -> list [showString "set-evidence!", showString "true"]
      | optProduceModel opt ]

    defs = do
      (v,t) <- ts
      let v2 = env Map.! v
      return $ showString $
        case optLanguage opt of
          SMTLIB2 -> printf "(declare-fun %s () %s)" v2 t
          YICES   -> printf "(define %s::%s) ; %s"  v2 t (MIP.fromVar v)

    optimality = list [showString "forall", decl, body]
      where
        decl =
          case optLanguage opt of
            SMTLIB2 -> list [list [showString (env2 Map.! v), showString t] | (v,t) <- ts]
            YICES   -> list [showString $ printf "%s::%s" (env2 Map.! v) t | (v,t) <- ts]
        body = list [showString "=>"
                    , and' (map fst (conditions opt True env2 mip))
                    , list [ showString $ if MIP.dir mip == MIP.OptMin then "<=" else ">="
                           , expr opt env mip obj, expr opt env2 mip obj
                           ]
                    ]

encode :: Options -> String -> String
encode opt s = 
  case optLanguage opt of
    SMTLIB2
     | all p s   -> s
     | any q s   -> error $ "cannot encode " ++ show s
     | otherwise -> "|" ++ s ++ "|"
    YICES   -> concatMap f s
  where
    p c = isAscii c && (isAlpha c || isDigit c || c `elem` "~!@$%^&*_-+=<>.?/")
    q c = c == '|' && c == '\\'

    -- Note that '[', ']', '\\' does not appear in identifiers of LP file.
    f '(' = "["
    f ')' = "]"
    f c | c `elem` "/\";" = printf "\\x%02d" (fromEnum c :: Int)
    f c = [c]

-- ------------------------------------------------------------------------

testFile :: FilePath -> IO ()
testFile fname = do
  result <- LPFile.parseFile fname
  case result of
    Right mip -> putStrLn $ convert defaultOptions mip ""
    Left err -> hPrint stderr err

test :: IO ()
test = putStrLn $ convert defaultOptions testdata ""

testdata :: MIP.Problem
Right testdata = LPFile.parseString "test" $ unlines
  [ "Maximize"
  , " obj: x1 + 2 x2 + 3 x3 + x4"
  , "Subject To"
  , " c1: - x1 + x2 + x3 + 10 x4 <= 20"
  , " c2: x1 - 3 x2 + x3 <= 30"
  , " c3: x2 - 3.5 x4 = 0"
  , "Bounds"
  , " 0 <= x1 <= 40"
  , " 2 <= x4 <= 3"
  , "General"
  , " x4"
  , "End"
  ]
