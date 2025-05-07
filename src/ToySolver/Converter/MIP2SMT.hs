{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_HADDOCK show-extensions #-}
{-# LANGUAGE OverloadedStrings #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.Converter.MIP2SMT
-- Copyright   :  (c) Masahiro Sakai 2012-2014,2016
-- License     :  BSD-style
--
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  experimental
-- Portability :  non-portable
--
-----------------------------------------------------------------------------
module ToySolver.Converter.MIP2SMT
  ( mip2smt
  , Options (..)
  , Language (..)
  , YicesVersion (..)
  ) where

import Data.Char
import Data.Default.Class
import Data.Ord
import Data.List (intersperse, sortBy)
import Data.Ratio
import qualified Data.Set as Set
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Text as T
import qualified Data.Text.Lazy.IO as TLIO
import Data.Text.Lazy.Builder (Builder)
import qualified Data.Text.Lazy.Builder as B
import qualified Data.Text.Lazy.Builder.Int as B
import Text.Printf

import qualified Numeric.Optimization.MIP as MIP
import ToySolver.Internal.Util (showRationalAsFiniteDecimal, isInteger)

-- | Translation options.
--
-- The default option can be obtained by 'def'.
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
  def =
    Options
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

type Var = T.Text
type Env = Map MIP.Var Var

list :: [Builder] -> Builder
list xs = B.singleton '(' <> mconcat (intersperse (B.singleton ' ') xs) <> B.singleton ')'

and' :: [Builder] -> Builder
and' [] = "true"
and' [x] = x
and' xs = list ("and" : xs)

or' :: [Builder] -> Builder
or' [] = "false"
or' [x] = x
or' xs = list ("or" : xs)

not' :: Builder -> Builder
not' x = list ["not", x]

intExpr :: Options -> Env -> MIP.Problem Rational -> MIP.Expr Rational -> Builder
intExpr opt env _mip e =
  case MIP.terms e of
    [] -> intNum opt 0
    [t] -> f t
    ts -> list (B.singleton '+' : map f ts)
  where
    f (MIP.Term c _) | not (isInteger c) =
      error ("ToySolver.Converter.MIP2SMT.intExpr: fractional coefficient: " ++ show c)
    f (MIP.Term c []) = intNum opt (floor c)
    f (MIP.Term (-1) vs) = list [B.singleton '-', f (MIP.Term 1 vs)]
    f (MIP.Term c vs) =
      case xs of
        [] -> intNum opt 1
        [x] -> x
        _ -> list (B.singleton '*' : xs)
      where
        xs = [intNum opt (floor c) | c /= 1] ++
             [B.fromText (env Map.! v) | v <- vs]

realExpr :: Options -> Env -> MIP.Problem Rational -> MIP.Expr Rational -> Builder
realExpr opt env mip e =
  case MIP.terms e of
    [] -> realNum opt 0
    [t] -> f t
    ts -> list (B.singleton '+' : map f ts)
  where
    f (MIP.Term c []) = realNum opt c
    f (MIP.Term (-1) vs) = list [B.singleton '-', f (MIP.Term 1 vs)]
    f (MIP.Term c vs) =
      case xs of
        [] -> realNum opt 1
        [x] -> x
        _ -> list (B.singleton '*' : xs)
      where
        xs = [realNum opt c | c /= 1] ++
             [ v3
             | v <- vs
             , let v2 = env Map.! v
             , let v3 = if isInt mip v
                        then toReal opt (B.fromText v2)
                        else B.fromText v2
             ]

intNum :: Options -> Integer -> Builder
intNum opt x =
  case optLanguage opt of
    SMTLIB2
      | x < 0     -> list [B.singleton '-', B.decimal (negate x)]
      | otherwise -> B.decimal x
    YICES _ -> B.decimal x

realNum :: Options -> Rational -> Builder
realNum opt r =
  case optLanguage opt of
    SMTLIB2
      | r < 0     -> list [B.singleton '-', f (negate r)]
      | otherwise -> f r
    YICES Yices1 ->
      if denominator r == 1
        then B.decimal (numerator r)
        else B.decimal (numerator r) <> B.singleton '/' <> B.decimal (denominator r)
    YICES Yices2 ->
      case showRationalAsFiniteDecimal r of
        Just s  -> B.fromString s
        Nothing -> B.decimal (numerator r) <> B.singleton '/' <> B.decimal (denominator r)
  where
    f r = case showRationalAsFiniteDecimal r of
            Just s  -> B.fromString s
            Nothing -> list [B.singleton '/', B.decimal (numerator r) <> ".0", B.decimal (denominator r) <> ".0"]

rel2 :: Options -> Env -> MIP.Problem Rational -> Bool -> MIP.BoundExpr Rational -> MIP.Expr Rational -> MIP.BoundExpr Rational -> Builder
rel2 opt env mip q lb e ub = and' (c1 ++ c2)
  where
    c1 =
      case lb of
        MIP.NegInf -> []
        MIP.Finite x -> [rel opt env mip q MIP.Ge e x]
        MIP.PosInf -> ["false"]
    c2 =
      case ub of
        MIP.NegInf -> ["false"]
        MIP.Finite x -> [rel opt env mip q MIP.Le e x]
        MIP.PosInf -> []

rel :: Options -> Env -> MIP.Problem Rational -> Bool -> MIP.RelOp -> MIP.Expr Rational -> Rational -> Builder
rel opt env mip q op lhs rhs
  | and [isInt mip v | v <- Set.toList (MIP.vars lhs)] &&
    and [isInteger c | MIP.Term c _ <- MIP.terms lhs] && isInteger rhs =
      f q op (intExpr opt env mip lhs) (intNum opt (floor rhs))
  | otherwise =
      f q op (realExpr opt env mip lhs) (realNum opt rhs)
  where
    f :: Bool -> MIP.RelOp -> Builder -> Builder -> Builder
    f True MIP.Eql x y = and' [f False MIP.Le x y, f False MIP.Ge x y]
    f _ MIP.Eql x y = list ["=", x, y]
    f _ MIP.Le x y = list ["<=", x, y]
    f _ MIP.Ge x y = list [">=", x, y]

toReal :: Options -> Builder -> Builder
toReal opt x =
  case optLanguage opt of
    SMTLIB2 -> list ["to_real", x]
    YICES _ -> x

assert :: Options -> (Builder, Maybe T.Text) -> Builder
assert opt (x, label) = list ["assert", x']
  where
    x' = case label of
           Just name | optLanguage opt == SMTLIB2 ->
             list [ "!"
                  , x
                  , ":named"
                  , B.fromText (encode opt name)
                  ]
           _ -> x

constraint :: Options -> Bool -> Env -> MIP.Problem Rational -> MIP.Constraint Rational -> (Builder, Maybe T.Text)
constraint opt q env mip
  MIP.Constraint
  { MIP.constrLabel     = label
  , MIP.constrIndicator = g
  , MIP.constrExpr = e
  , MIP.constrLB = lb
  , MIP.constrUB = ub
  } = (c1, label)
  where
    c0 = rel2 opt env mip q lb e ub
    c1 = case g of
           Nothing -> c0
           Just (var,val) ->
             list [ "=>"
                  , rel opt env mip q MIP.Eql (MIP.varExpr var) val
                  , c0
                  ]

conditions :: Options -> Bool -> Env -> MIP.Problem Rational -> [(Builder, Maybe T.Text)]
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
              | lb == MIP.PosInf || ub == MIP.NegInf -> "false"
              | length args >= 2 -> list ("<=" : args)
              | otherwise -> "true"
                  where
                    args = lb2 ++ [B.fromText v2] ++ ub2
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
                       MIP.PosInf -> ["false"]
                       MIP.Finite x ->
                         if isInt mip v
                         then [list ["<=", intNum opt (ceiling x), B.fromText v2]]
                         else [list ["<=", realNum opt x, B.fromText v2]]
                s2 = case ub of
                       MIP.NegInf -> ["false"]
                       MIP.PosInf -> []
                       MIP.Finite x ->
                         if isInt mip v
                         then [list ["<=", B.fromText v2, intNum opt (floor x)]]
                         else [list ["<=", B.fromText v2, realNum opt x]]

        c1 = case MIP.getVarType mip v of
               MIP.SemiContinuousVariable ->
                 or' [list ["=", B.fromText v2, realNum opt 0], c0]
               MIP.SemiIntegerVariable ->
                 or' [list ["=", B.fromText v2, intNum opt 0], c0]
               _ ->
                 c0

    cs = map (constraint opt q env mip) (MIP.constraints mip)
    ss = concatMap sos (MIP.sosConstraints mip)
    sos (MIP.SOSConstraint label typ xs) = do
      (x1,x2) <- case typ of
                    MIP.S1 -> pairs $ map fst xs
                    MIP.S2 -> nonAdjacentPairs $ map fst $ sortBy (comparing snd) $ xs
      let c = not' $ and'
            [ list ["/=", v3, realNum opt 0]
            | v<-[x1,x2]
            , let v2 = env Map.! v
            , let v3 = if isInt mip v
                       then toReal opt (B.fromText v2)
                       else B.fromText v2
            ]
      return (c, label)

pairs :: [a] -> [(a,a)]
pairs [] = []
pairs (x:xs) = [(x,x2) | x2 <- xs] ++ pairs xs

nonAdjacentPairs :: [a] -> [(a,a)]
nonAdjacentPairs (x1:x2:xs) = [(x1,x3) | x3 <- xs] ++ nonAdjacentPairs (x2:xs)
nonAdjacentPairs _ = []

mip2smt :: Options -> MIP.Problem Rational -> Builder
mip2smt opt mip =
  mconcat $ map (<> B.singleton '\n') $
    options ++ set_logic ++ defs ++ map (assert opt) (conditions opt False env mip)
    ++ [ assert opt (optimality, Nothing) | optOptimize opt ]
    ++ [ case optLanguage opt of
           SMTLIB2 -> list ["check-sat"]
           YICES _ -> list ["check"]
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
    obj = MIP.objectiveFunction mip
    env = Map.fromList [(v, encode opt (MIP.varName v)) | v <- Set.toList vs]
    -- Note that identifiers of LPFile does not contain '-'.
    -- So that there are no name crash.
    env2 = Map.fromList [(v, encode opt (MIP.varName v <> "-2")) | v <- Set.toList vs]

    options =
      [ case optLanguage opt of
          SMTLIB2 -> list ["set-option", ":produce-models", "true"]
          YICES _ -> list ["set-evidence!", "true"]
      | optProduceModel opt && optLanguage opt /= YICES Yices2
      ]

    set_logic =
      case optSetLogic opt of
        Just logic | optLanguage opt == SMTLIB2 -> [list ["set-logic", B.fromString logic]]
        _ -> []

    defs = do
      (v,t) <- ts
      let v2 = env Map.! v
      return $
        case optLanguage opt of
          SMTLIB2 -> "(declare-fun " <> B.fromText v2 <> " () " <> B.fromString t <> ")"
          YICES _ -> "(define " <> B.fromText v2 <> "::" <> B.fromString t <> ") ; " <> B.fromText  (MIP.varName v)

    optimality = list ["forall", decl, body]
      where
        decl =
          case optLanguage opt of
            SMTLIB2 -> list [list [B.fromText (env2 Map.! v), B.fromString t] | (v,t) <- ts]
            YICES _ -> list [B.fromText (env2 Map.! v) <> "::" <> B.fromString t | (v,t) <- ts]
        body = list ["=>"
                    , and' (map fst (conditions opt True env2 mip))
                    , list [ if MIP.objDir obj == MIP.OptMin then "<=" else ">="
                           , realExpr opt env mip (MIP.objExpr obj), realExpr opt env2 mip (MIP.objExpr obj)
                           ]
                    ]

encode :: Options -> T.Text -> T.Text
encode opt s =
  case optLanguage opt of
    SMTLIB2
     | T.all p s   -> s
     | T.any q s   -> error $ "cannot encode " ++ show s
     | otherwise -> "|" <> s <> "|"
    YICES _ -> T.concatMap f s
  where
    p c = isAscii c && (isAlpha c || isDigit c || c `elem` ("~!@$%^&*_-+=<>.?/" :: [Char]))
    q c = c == '|' && c == '\\'

    -- Note that '[', ']', '\\' does not appear in identifiers of LP file.
    f '(' = "["
    f ')' = "]"
    f c | c `elem` ("/\";" :: [Char]) = T.pack $ printf "\\x%02d" (fromEnum c :: Int)
    f c = T.singleton c

isInt :: MIP.Problem Rational -> MIP.Var -> Bool
isInt mip v = vt == MIP.IntegerVariable || vt == MIP.SemiIntegerVariable
  where
    vt = MIP.getVarType mip v

-- ------------------------------------------------------------------------

_testFile :: FilePath -> IO ()
_testFile fname = do
  mip <- MIP.readLPFile def fname
  TLIO.putStrLn $ B.toLazyText $ mip2smt def (fmap toRational mip)

_test :: IO ()
_test = TLIO.putStrLn $ B.toLazyText $ mip2smt def _testdata

_testdata :: MIP.Problem Rational
Right _testdata = fmap (fmap toRational) $ MIP.parseLPString def "test" $ unlines
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
