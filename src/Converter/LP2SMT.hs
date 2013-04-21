{-# OPTIONS_GHC -Wall #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Converter.LP2SMT
-- Copyright   :  (c) Masahiro Sakai 2012
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  experimental
-- Portability :  portable
--
-----------------------------------------------------------------------------
module Converter.LP2SMT
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
import qualified Data.Map.Strict as Map
import System.IO
import Text.Printf
import qualified Text.LPFile as LP
import Util (showRationalAsFiniteDecimal)

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
type Env = Map.Map LP.Var Var

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

expr :: Options -> Env -> LP.LP -> LP.Expr -> ShowS
expr opt env lp e =
  case e of
    [] -> showChar '0'
    _ -> list (showChar '+' : map f e)
  where
    f (LP.Term c []) = realNum opt c
    f (LP.Term c vs) =
      case xs of
        [] -> realNum opt 1
        [x] -> x
        _ -> list (showChar '*' : xs)
      where
        xs = [realNum opt c | c /= 1] ++
             [ v3
             | v <- vs
             , let v2 = env Map.! v
             , let v3 = if LP.getVarType lp v == LP.IntegerVariable
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

rel :: Bool -> LP.RelOp -> ShowS -> ShowS -> ShowS
rel True LP.Eql x y = and' [rel False LP.Le x y, rel False LP.Ge x y]
rel _ LP.Eql x y = list [showString "=", x, y]
rel _ LP.Le x y = list [showString "<=", x, y]
rel _ LP.Ge x y = list [showString ">=", x, y]

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

constraint :: Options -> Bool -> Env -> LP.LP -> LP.Constraint -> (ShowS, Maybe String)
constraint opt q env lp
  LP.Constraint
  { LP.constrLabel     = label
  , LP.constrIndicator = g
  , LP.constrBody      = (e, op, b)
  } = (c1, label)
  where
    c0 = rel q op (expr opt env lp e) (realNum opt b)
    c1 = case g of
           Nothing -> c0
           Just (var,val) ->
             list [ showString "=>"
                  , rel q LP.Eql (expr opt env lp [LP.Term 1 [var]]) (realNum opt val)
                  , c0
                  ]

conditions :: Options -> Bool -> Env -> LP.LP -> [(ShowS, Maybe String)]
conditions opt q env lp = bnds ++ cs ++ ss
  where
    vs = LP.variables lp
    bnds = map bnd (Set.toList vs)
    bnd v = (c1, Nothing)
      where
        v2 = env Map.! v
        v3 = if LP.getVarType lp v == LP.IntegerVariable
             then toReal opt (showString v2)
             else showString v2
        (lb,ub) = LP.getBounds lp v
        s1 = case lb of
               LP.NegInf -> []
               LP.PosInf -> [showString "false"]
               LP.Finite x -> [list [showString "<=", realNum opt x, v3]]
        s2 = case ub of
               LP.NegInf -> [showString "false"]
               LP.PosInf -> []
               LP.Finite x -> [list [showString "<=", v3, realNum opt x]]
        c0 = and' (s1 ++ s2)
        c1 = if LP.getVarType lp v == LP.SemiContinuousVariable
             then or' [list [showString "=", showString v2, realNum opt 0], c0]
             else c0
    cs = map (constraint opt q env lp) (LP.constraints lp)
    ss = concatMap sos (LP.sos lp)
    sos (label, typ, xs) = do
      (x1,x2) <- case typ of
                    LP.S1 -> pairs $ map fst xs
                    LP.S2 -> nonAdjacentPairs $ map fst $ sortBy (comparing snd) $ xs
      let c = not' $ and'
            [ list [showString "/=", v3, realNum opt 0]
            | v<-[x1,x2]
            , let v2 = env Map.! v
            , let v3 = if LP.getVarType lp v == LP.IntegerVariable
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

convert :: Options -> LP.LP -> ShowS
convert opt lp =
  unlinesS $ defs ++ map (assert opt) (conditions opt False env lp)
             ++ [ assert opt (optimality, Nothing) | optOptimize opt ]
             ++ [ case optLanguage opt of
                    SMTLIB2 -> list [showString "set-option", showString ":produce-models", showString "true"]
                    YICES   -> list [showString "set-evidence!", showString "true"]
                | optProduceModel opt ]
             ++ [ case optLanguage opt of
                    SMTLIB2 -> list [showString "check-sat"]
                    YICES   -> list [showString "check"]
                | optCheckSAT opt ]
  where
    vs = LP.variables lp
    real_vs = vs `Set.difference` int_vs
    int_vs = LP.integerVariables lp
    realType =
      case optLanguage opt of
        SMTLIB2 -> "Real"
        YICES   -> "real"
    intType  =
      case optLanguage opt of
        SMTLIB2 -> "Int"
        YICES   -> "int"
    ts = [(v, realType) | v <- Set.toList real_vs] ++ [(v, intType) | v <- Set.toList int_vs]
    obj = snd (LP.objectiveFunction lp)
    env = Map.fromList [(v, encode opt v) | v <- Set.toList vs]
    -- Note that identifiers of LPFile does not contain '-'.
    -- So that there are no name crash.
    env2 = Map.fromList [(v, encode opt (v ++ "-2")) | v <- Set.toList vs]

    defs = do
      (v,t) <- ts
      let v2 = env Map.! v
      return $ showString $
        case optLanguage opt of
          SMTLIB2 -> printf "(declare-fun %s () %s)" v2 t
          YICES   -> printf "(define %s::%s) ; %s"  v2 t v

    optimality = list [showString "forall", decl, body]
      where
        decl =
          case optLanguage opt of
            SMTLIB2 -> list [list [showString (env2 Map.! v), showString t] | (v,t) <- ts]
            YICES   -> list [showString $ printf "%s::%s" (env2 Map.! v) t | (v,t) <- ts]
        body = list [showString "=>"
                    , and' (map fst (conditions opt True env2 lp))
                    , list [ showString $ if LP.dir lp == LP.OptMin then "<=" else ">="
                           , expr opt env lp obj, expr opt env2 lp obj
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
  result <- LP.parseFile fname
  case result of
    Right lp -> putStrLn $ convert defaultOptions lp ""
    Left err -> hPrint stderr err

test :: IO ()
test = putStrLn $ convert defaultOptions testdata ""

testdata :: LP.LP
Right testdata = LP.parseString "test" $ unlines
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
