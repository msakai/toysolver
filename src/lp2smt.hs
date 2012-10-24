{-# OPTIONS_GHC -Wall -fno-warn-unused-do-bind #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  lp2smt
-- Copyright   :  (c) Masahiro Sakai 2011-2012
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  experimental
-- Portability :  portable
--
-----------------------------------------------------------------------------
module Main where

import Data.Ord
import Data.List
import Data.Ratio
import qualified Data.Set as Set
import qualified Data.Map as Map
import System.Console.GetOpt
import System.Environment
import System.Exit
import System.IO
import Text.Printf
import qualified Text.LPFile as LP

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

expr :: Bool -> Env -> LP.LP -> LP.Expr -> ShowS
expr isYices env lp e =
  case e of
    [] -> showChar '0'
    _ -> list (showChar '+' : map f e)
  where
    f (LP.Term c []) = realNum isYices c
    f (LP.Term c vs) =
      case xs of
        [] -> realNum isYices 1
        [x] -> x
        _ -> list (showChar '*' : xs)
      where
        xs = [realNum isYices c | c /= 1] ++
             [ v3
             | v <- vs
             , let v2 = env Map.! v
             , let v3 = if not isYices && (v `Set.member` LP.integerVariables lp || v `Set.member` LP.binaryVariables lp)
                        then list [showString "to_real", showString v2]
                        else showString v2
             ]

realNum :: Bool -> Rational -> ShowS
realNum isYices r
  | isYices =
    if denominator r == 1
      then shows (numerator r)
      else shows (numerator r) . showChar '/' . shows (denominator r)
  | r == 0    = showString "0.0"
  | r < 0     = list [showChar '-', f (negate r)]
  | otherwise = f r
  where
    f r = if denominator r == 1
          then shows (numerator r) . showString ".0"
          else list [showChar '/', shows (numerator r) . showString ".0", shows (denominator r) . showString ".0"]

rel :: Bool -> LP.RelOp -> ShowS -> ShowS -> ShowS
rel True LP.Eql x y = and' [rel False LP.Le x y, rel False LP.Ge x y]
rel _ LP.Eql x y = list [showString "=", x, y]
rel _ LP.Le x y = list [showString "<=", x, y]
rel _ LP.Ge x y = list [showString ">=", x, y]

assert :: ShowS -> ShowS
assert x = list [showString "assert", x]

constraint :: Bool -> Bool -> Env -> LP.LP -> LP.Constraint -> ShowS
constraint isYices q env lp LP.Constraint{ LP.constrIndicator = g, LP.constrBody = (e, op, b) } =
  case g of 
    Nothing -> c
    Just (var,val) ->
      list [ showString "=>"
           , rel q LP.Eql (expr isYices env lp [LP.Term 1 [var]]) (realNum isYices val)
           , c
           ]
  where
    c = rel q op (expr isYices env lp e) (realNum isYices b)

conditions :: Bool -> Bool -> Env -> LP.LP -> [ShowS]
conditions isYices q env lp = bnds ++ bins ++ cs ++ ss
  where
    vs = LP.variables lp
    bins = do
      v <- Set.toList (LP.binaryVariables lp)
      let v2 = env Map.! v
      return $ list [showString "or", rel q LP.Eql (showString v2) (showChar '0'), rel q LP.Eql (showString v2) (showChar '1')]
    bnds = map bnd (Set.toList vs)
    bnd v =
      if v `Set.member` (LP.semiContinuousVariables lp)
       then or' [list [showString "=", showString v2, realNum isYices 0], and' (s1 ++ s2)]
       else and' (s1 ++ s2)
      where
        v2 = env Map.! v
        v3 = if v `Set.member` LP.integerVariables lp || v `Set.member` LP.binaryVariables lp
             then list [showString "to_real", showString v2]
             else showString v2
        (lb,ub) = LP.getBounds lp v
        s1 = case lb of
               LP.NegInf -> []
               LP.PosInf -> [showString "false"]
               LP.Finite x -> [list [showString "<=", realNum isYices x, v3]]
        s2 = case ub of
               LP.NegInf -> [showString "false"]
               LP.PosInf -> []
               LP.Finite x -> [list [showString "<=", v3, realNum isYices x]]
    cs = map (constraint isYices q env lp) (LP.constraints lp)
    ss = concatMap sos (LP.sos lp)
    sos (_, typ, xs) = do
      (x1,x2) <- case typ of
                    LP.S1 -> pairs $ map fst xs
                    LP.S2 -> nonAdjacentPairs $ map fst $ sortBy (comparing snd) $ xs
      return $ not' $ and'
        [ list [showString "/=", v3, realNum isYices 0]
        | v<-[x1,x2]
        , let v2 = env Map.! v
        , let v3 = if v `Set.member` LP.integerVariables lp || v `Set.member` LP.binaryVariables lp
                   then list [showString "to_real", showString v2]
                   else showString v2
        ]

pairs :: [a] -> [(a,a)]
pairs [] = []
pairs (x:xs) = [(x,x2) | x2 <- xs] ++ pairs xs

nonAdjacentPairs :: [a] -> [(a,a)]
nonAdjacentPairs (x1:x2:xs) = [(x1,x3) | x3 <- xs] ++ nonAdjacentPairs (x2:xs)
nonAdjacentPairs _ = []

lp2smt :: LP.LP -> Bool -> Bool -> Bool -> ShowS
lp2smt lp isYices optimize check =
  unlinesS $ defs ++ map assert (conditions isYices False env lp)
             ++ [ optimalityDef ]
             ++ [ assert (showString "optimality") | optimize ]
             ++ [ if isYices
                  then list [showString "set-evidence!", showString "true"]
                  else list [showString "set-option", showString ":produce-models", showString "false"]
                | check ]
             ++ [ if isYices
                  then list [showString "check"]
                  else list [showString "check-sat"]
                | check ]
  where
    vs = LP.variables lp
    real_vs = vs `Set.difference` int_vs
    int_vs = LP.integerVariables lp `Set.union` LP.binaryVariables lp
    realType = if isYices then "real" else "Real"
    intType  = if isYices then "int" else "Int"
    ts = [(v, realType) | v <- Set.toList real_vs] ++ [(v, intType) | v <- Set.toList int_vs]
    obj = snd (LP.objectiveFunction lp)
    env = Map.fromList [(v, encode v) | v <- Set.toList vs]
    -- Note that identifiers of LPFile does not contain '-'.
    -- So that there are no name crash.
    env2 = Map.fromList [(v, encode v ++ "-2") | v <- Set.toList vs]

    defs = do
      (v,t) <- ts
      let v2 = env Map.! v
      return $ showString $
        if isYices
        then printf "(define %s::%s) ; %s"  v2 t v
        else printf "(declare-fun %s () %s) ; %s" v2 t v

    optimalityDef =
      if isYices
      then list [showString "define", showString "optimality::bool", optimality]
      else list [showString "define-fun", showString "optimality", list [], showString "Bool", optimality]

    optimality = list [showString "forall", decl, body]
      where
        decl =
          if isYices
          then list [showString $ printf "%s::%s" (env2 Map.! v) t | (v,t) <- ts]
          else list [list [showString (env2 Map.! v), showString t] | (v,t) <- ts]
        body = list [showString "=>"
                    , and' (conditions isYices True env2 lp)
                    , list [ showString $ if LP.dir lp == LP.OptMin then "<=" else ">="
                           , expr isYices env lp obj, expr isYices env2 lp obj
                           ]
                    ]

encode :: String -> String
encode s = concatMap f s
  where
    -- Note that '[', ']', '\\' does not appear in identifiers of LP file.
    f '(' = "["
    f ')' = "]"
    f c | c `elem` "/\";" = printf "\\x%02d" (fromEnum c :: Int)
    f c = [c]

data Flag
    = Help
    | Optimize
    | NoCheck
    | Yices
    deriving Eq

options :: [OptDescr Flag]
options =
    [ Option ['h'] ["help"]  (NoArg Help)       "show help"
    , Option [] ["yices"]    (NoArg Yices)      "output .ys instead of .smt2"
    , Option [] ["optimize"] (NoArg Optimize)   "output optimiality condition which uses quantifiers"
    , Option [] ["no-check"] (NoArg NoCheck)    "do not output \"(check)\""
    ]


main :: IO ()
main = do
  args <- getArgs
  case getOpt Permute options args of
    (o,_,[])
      | Help `elem` o    -> putStrLn (usageInfo header options)
    (o,[fname],[]) -> do
      ret <- if fname == "-"
             then fmap (LP.parseString "-") getContents
             else LP.parseFile fname
      case ret of
        Right lp -> putStrLn $ lp2smt lp (Yices `elem` o) (Optimize `elem` o) (not (NoCheck `elem` o)) ""
        Left err -> hPrint stderr err >> exitFailure
    (_,_,errs) -> do
        hPutStrLn stderr $ concat errs ++ usageInfo header options
        exitFailure

header :: String
header = "Usage: lp2smt [OPTION]... [file.lp|-]"

testFile :: FilePath -> IO ()
testFile fname = do
  result <- LP.parseFile fname
  case result of
    Right lp -> putStrLn $ lp2smt lp False True True ""
    Left err -> hPrint stderr err

test :: IO ()
test = putStrLn $ lp2smt testdata False True True ""

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
