{-# OPTIONS_GHC -Wall #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.Converter.MIP2SMT
-- Copyright   :  (c) Masahiro Sakai 2012-2014
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  experimental
-- Portability :  portable
--
-----------------------------------------------------------------------------
module ToySolver.Converter.MIP2SMT
  ( convert
  , Options (..)
  , defaultOptions
  , Language (..)
  , YicesVersion (..)
  ) where

import Data.Char
import Data.Default.Class
import Data.Ord
import Data.List
import Data.Ratio
import qualified Data.Set as Set
import Data.Map (Map)
import qualified Data.Map as Map
import System.IO
import Text.Printf

import qualified ToySolver.Data.MIP as MIP
import qualified ToySolver.Text.LPFile as LPFile
import ToySolver.Internal.Util (showRationalAsFiniteDecimal, isInteger)

data Options
  = Options
  { optLanguage     :: Language
  , optSetLogic     :: Maybe String
  , optCheckSAT     :: Bool
  , optProduceModel :: Bool
  , optOptimize     :: Bool
  }
  deriving (Show, Eq, Ord)

instance Default Options where
  def = defaultOptions

defaultOptions :: Options
defaultOptions
  = Options
  { optLanguage     = SMTLIB2
  , optSetLogic     = Nothing
  , optCheckSAT     = True
  , optProduceModel = True
  , optOptimize     = False
  }

data Language
  = SMTLIB2
  | YICES YicesVersion
  deriving (Show, Eq, Ord)

data YicesVersion
  = Yices1
  | Yices2
  deriving (Show, Eq, Ord, Enum, Bounded)

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

intExpr :: Options -> Env -> MIP.Problem -> MIP.Expr -> ShowS
intExpr opt env mip e =
  case e of
    [] -> intNum opt 0
    [t] -> f t
    _ -> list (showChar '+' : map f e)
  where
    f (MIP.Term c _) | not (isInteger c) =
      error ("ToySolver.Converter.MIP2SMT.intExpr: fractional coefficient: " ++ show c)
    f (MIP.Term c []) = intNum opt (floor c)
    f (MIP.Term (-1) vs) = list [showChar '-', f (MIP.Term 1 vs)]
    f (MIP.Term c vs) =
      case xs of
        [] -> intNum opt 1
        [x] -> x
        _ -> list (showChar '*' : xs)
      where
        xs = [intNum opt (floor c) | c /= 1] ++
             [showString (env Map.! v) | v <- vs]

realExpr :: Options -> Env -> MIP.Problem -> MIP.Expr -> ShowS
realExpr opt env mip e =
  case e of
    [] -> realNum opt 0
    [t] -> f t
    _ -> list (showChar '+' : map f e)
  where
    f (MIP.Term c []) = realNum opt c
    f (MIP.Term (-1) vs) = list [showChar '-', f (MIP.Term 1 vs)]
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
             , let v3 = if isInt mip v
                        then toReal opt (showString v2)
                        else showString v2
             ]

intNum :: Options -> Integer -> ShowS
intNum opt x =
  case optLanguage opt of
    SMTLIB2
      | x < 0     -> list [showChar '-', shows (negate x)]
      | otherwise -> shows x
    YICES _ -> shows x

realNum :: Options -> Rational -> ShowS
realNum opt r =
  case optLanguage opt of
    SMTLIB2
      | r < 0     -> list [showChar '-', f (negate r)]
      | otherwise -> f r
    YICES Yices1 ->
      if denominator r == 1
        then shows (numerator r)
        else shows (numerator r) . showChar '/' . shows (denominator r)
    YICES Yices2 ->
      case showRationalAsFiniteDecimal r of
        Just s  -> showString s
        Nothing -> shows (numerator r) . showChar '/' . shows (denominator r)
  where
    f r = case showRationalAsFiniteDecimal r of
            Just s  -> showString s
            Nothing -> list [showChar '/', shows (numerator r) . showString ".0", shows (denominator r) . showString ".0"]

rel :: Options -> Env -> MIP.Problem -> Bool -> MIP.RelOp -> MIP.Expr -> Rational -> ShowS
rel opt env mip q op lhs rhs
  | and [isInt mip v | v <- Set.toList (MIP.vars lhs)] &&
    and [isInteger c | MIP.Term c _ <- lhs] && isInteger rhs =
      f q op (intExpr opt env mip lhs) (intNum opt (floor rhs))
  | otherwise =
      f q op (realExpr opt env mip lhs) (realNum opt rhs)
  where
    f :: Bool -> MIP.RelOp -> ShowS -> ShowS -> ShowS
    f True MIP.Eql x y = and' [f False MIP.Le x y, f False MIP.Ge x y]
    f _ MIP.Eql x y = list [showString "=", x, y]
    f _ MIP.Le x y = list [showString "<=", x, y]
    f _ MIP.Ge x y = list [showString ">=", x, y]

toReal :: Options -> ShowS -> ShowS
toReal opt x =
  case optLanguage opt of
    SMTLIB2 -> list [showString "to_real", x]
    YICES _ -> x

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
    c0 = rel opt env mip q op e b
    c1 = case g of
           Nothing -> c0
           Just (var,val) ->
             list [ showString "=>"
                  , rel opt env mip q MIP.Eql [MIP.Term 1 [var]] val
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
        (lb,ub) = MIP.getBounds mip v

        c0 =
          case optLanguage opt of
            -- In SMT-LIB2 format, inequalities can be chained.
            -- For example, "(<= 0 x 10)" is equivalent to "(and (<= 0 x) (<= x 10))".
            -- 
            -- Supported solvers: cvc4-1.1, yices-2.2.1, z3-4.3.0
            -- Unsupported solvers: z3-4.0
            SMTLIB2
              | lb == MIP.PosInf || ub == MIP.NegInf -> showString "false"
              | length args >= 2 -> list (showString "<=" : args)
              | otherwise -> showString "true"
                  where
                    args = lb2 ++ [showString v2] ++ ub2
                    lb2 = case lb of
                            MIP.NegInf -> []
                            MIP.PosInf -> error "should not happen"
                            MIP.Finite x 
                              | isInt mip v -> [intNum opt (ceiling x)]
                              | otherwise -> [realNum opt x]
                    ub2 = case ub of 
                            MIP.NegInf -> error "should not happen"
                            MIP.PosInf -> []
                            MIP.Finite x
                              | isInt mip v -> [intNum opt (floor x)]
                              | otherwise -> [realNum opt x]
            YICES _ -> and' (s1 ++ s2)
              where
                s1 = case lb of
                       MIP.NegInf -> []
                       MIP.PosInf -> [showString "false"]
                       MIP.Finite x ->
                         if isInt mip v
                         then [list [showString "<=", intNum opt (ceiling x), showString v2]]
                         else [list [showString "<=", realNum opt x, showString v2]]
                s2 = case ub of
                       MIP.NegInf -> [showString "false"]
                       MIP.PosInf -> []
                       MIP.Finite x ->
                         if isInt mip v
                         then [list [showString "<=", showString v2, intNum opt (floor x)]]
                         else [list [showString "<=", showString v2, realNum opt x]]

        c1 = case MIP.getVarType mip v of
               MIP.SemiContinuousVariable ->
                 or' [list [showString "=", showString v2, realNum opt 0], c0]
               MIP.SemiIntegerVariable ->
                 or' [list [showString "=", showString v2, intNum opt 0], c0]
               _ ->
                 c0

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
            , let v3 = if isInt mip v
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
  unlinesS $ options ++ set_logic ++ defs ++ map (assert opt) (conditions opt False env mip)
             ++ [ assert opt (optimality, Nothing) | optOptimize opt ]
             ++ [ case optLanguage opt of
                    SMTLIB2 -> list [showString "check-sat"]
                    YICES _ -> list [showString "check"]
                | optCheckSAT opt ]
  where
    vs = MIP.variables mip
    real_vs = vs `Set.difference` int_vs
    int_vs = MIP.integerVariables mip `Set.union` MIP.semiIntegerVariables mip
    realType =
      case optLanguage opt of
        SMTLIB2 -> "Real"
        YICES _ -> "real"
    intType  =
      case optLanguage opt of
        SMTLIB2 -> "Int"
        YICES _ -> "int"
    ts = [(v, realType) | v <- Set.toList real_vs] ++ [(v, intType) | v <- Set.toList int_vs]
    obj = snd (MIP.objectiveFunction mip)
    env = Map.fromList [(v, encode opt (MIP.fromVar v)) | v <- Set.toList vs]
    -- Note that identifiers of LPFile does not contain '-'.
    -- So that there are no name crash.
    env2 = Map.fromList [(v, encode opt (MIP.fromVar v ++ "-2")) | v <- Set.toList vs]

    options =
      [ case optLanguage opt of
          SMTLIB2 -> list [showString "set-option", showString ":produce-models", showString "true"]
          YICES _ -> list [showString "set-evidence!", showString "true"]
      | optProduceModel opt && optLanguage opt /= YICES Yices2
      ]

    set_logic =
      case optSetLogic opt of
        Just logic | optLanguage opt == SMTLIB2 -> [list [showString "set-logic", showString logic]]
        _ -> []

    defs = do
      (v,t) <- ts
      let v2 = env Map.! v
      return $ showString $
        case optLanguage opt of
          SMTLIB2 -> printf "(declare-fun %s () %s)" v2 t
          YICES _ -> printf "(define %s::%s) ; %s"  v2 t (MIP.fromVar v)

    optimality = list [showString "forall", decl, body]
      where
        decl =
          case optLanguage opt of
            SMTLIB2 -> list [list [showString (env2 Map.! v), showString t] | (v,t) <- ts]
            YICES _ -> list [showString $ printf "%s::%s" (env2 Map.! v) t | (v,t) <- ts]
        body = list [showString "=>"
                    , and' (map fst (conditions opt True env2 mip))
                    , list [ showString $ if MIP.dir mip == MIP.OptMin then "<=" else ">="
                           , realExpr opt env mip obj, realExpr opt env2 mip obj
                           ]
                    ]

encode :: Options -> String -> String
encode opt s = 
  case optLanguage opt of
    SMTLIB2
     | all p s   -> s
     | any q s   -> error $ "cannot encode " ++ show s
     | otherwise -> "|" ++ s ++ "|"
    YICES _ -> concatMap f s
  where
    p c = isAscii c && (isAlpha c || isDigit c || c `elem` "~!@$%^&*_-+=<>.?/")
    q c = c == '|' && c == '\\'

    -- Note that '[', ']', '\\' does not appear in identifiers of LP file.
    f '(' = "["
    f ')' = "]"
    f c | c `elem` "/\";" = printf "\\x%02d" (fromEnum c :: Int)
    f c = [c]

isInt :: MIP.Problem -> MIP.Var -> Bool
isInt mip v = vt == MIP.IntegerVariable || vt == MIP.SemiIntegerVariable
  where
    vt = MIP.getVarType mip v

-- ------------------------------------------------------------------------

testFile :: FilePath -> IO ()
testFile fname = do
  result <- LPFile.parseFile fname
  case result of
    Right mip -> putStrLn $ convert def mip ""
    Left err -> hPrint stderr err

test :: IO ()
test = putStrLn $ convert def testdata ""

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
