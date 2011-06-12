{-# OPTIONS_GHC -Wall -fno-warn-unused-do-bind #-}
module Main where

import Data.Function (on)
import Data.List
import Data.Ratio
import qualified Data.Set as Set
import qualified Data.Map as Map
import System.Exit
import System.IO
import Text.Printf
import qualified LPFile as LP

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
and' xs = list (showString "and" : xs)

or' :: [ShowS] -> ShowS
or' [] = showString "false"
or' xs = list (showString "or" : xs)

not' :: ShowS -> ShowS
not' x = list [showString "not", x]

expr :: Env -> LP.Expr -> ShowS
expr env e =
  case map f (terms e) of
    [] -> showChar '0'
    xs -> list (showChar '+' : xs)
  where
    f (LP.Var v) = showString (env Map.! v)
    f (LP.Const r) = num r
    f ((LP.Const 1) LP.:*: b) = f b
    f (a LP.:*: b) = list [showChar '*', f a, f b]
    f (a LP.:+: b) = if a == LP.Const 1 then f b else list [showString "+", f a, f b]
    f (a LP.:/: b) = list [showChar '/', f a, f b]

    terms :: LP.Expr -> [LP.Expr]
    terms (a LP.:+: b) = terms a ++ terms b
    terms (LP.Const 0) = []
    terms x = [x]

num :: Rational -> ShowS
num r
  | denominator r == 1 = shows (numerator r)
  | otherwise = shows (numerator r) . showChar '/' . shows (denominator r)

rel :: Bool -> LP.RelOp -> ShowS -> ShowS -> ShowS
rel True LP.Eql x y = and' [rel False LP.Le x y, rel False LP.Ge x y]
rel _ LP.Eql x y = list [showString "=", x, y]
rel _ LP.Le x y = list [showString "<=", x, y]
rel _ LP.Ge x y = list [showString ">=", x, y]

assert :: ShowS -> ShowS
assert x = list [showString "assert", x]

constraint :: Bool -> Env -> LP.Constraint -> ShowS
constraint q env (_, g, (e, op, b)) =
  case g of 
    Nothing -> c
    Just (var,val) ->
      list [ showString "=>"
           , rel q LP.Eql (expr env (LP.Var var)) (num val)
           , c
           ]
  where
    c = rel q op (expr env e) (num b)

conditions :: Bool -> Env -> LP.LP -> [ShowS]
conditions q env lp = bnds ++ bins ++ cs ++ ss
  where
    vs = LP.variables lp
    bins = do
      v <- Set.toList (LP.binaryVariables lp)
      let v2 = env Map.! v
      return $ list [showString "or", rel q LP.Eql (showString v2) (showChar '0'), rel q LP.Eql (showString v2) (showChar '1')]
    bnds = map bnd (Set.toList vs)
    bnd v =
      if v `Set.member` (LP.semiContinuousVariables lp)
       then or' [list [showString "=", showString v2, num 0], and' (s1 ++ s2)]
       else and' (s1 ++ s2)
      where
        v2 = env Map.! v
        (lb,ub) = LP.getBounds lp v
        s1 = case lb of
               LP.NegInf -> []
               LP.PosInf -> [showString "false"]
               LP.Finite x -> [list [showString "<=", num x, showString v2]]
        s2 = case ub of
               LP.NegInf -> [showString "false"]
               LP.PosInf -> []
               LP.Finite x -> [list [showString "<=", showString v2, num x]]
    cs = map (constraint q env) (LP.constraints lp)
    ss = concatMap sos (LP.sos lp)
    sos (_, typ, xs) = do
      (x1,x2) <- case typ of
                    LP.S1 -> pairs $ map fst xs
                    LP.S2 -> nonAdjacentPairs $ map fst $ sortBy (compare `on` snd) $ xs
      return $ not' $ and' [list [showString "/=", showString (env Map.! v), showChar '0']  | v<-[x1,x2]]

pairs :: [a] -> [(a,a)]
pairs [] = []
pairs (x:xs) = [(x,x2) | x2 <- xs] ++ pairs xs

nonAdjacentPairs :: [a] -> [(a,a)]
nonAdjacentPairs (x1:x2:xs) = [(x1,x3) | x3 <- xs] ++ nonAdjacentPairs (x2:xs)
nonAdjacentPairs _ = []

lp2ys :: LP.LP -> ShowS
lp2ys lp = unlinesS $ defs ++ map assert (conditions False env lp)
                   ++ [list [showString "check"], assert optimality, list [showString "check"]]
  where
    vs = LP.variables lp
    real_vs = vs `Set.difference` int_vs
    int_vs = LP.integerVariables lp `Set.union` LP.binaryVariables lp
    ts = [(v, "real")| v <- Set.toList real_vs] ++ [(v, "int") | v <- Set.toList int_vs]
    obj = snd (LP.objectiveFunction lp)
    env = Map.fromList [(v, "x"++show i) | (v,i) <- zip (Set.toList vs) [(1::Int)..]]
    env2 = Map.fromList [(v, "y"++show i) | (v,i) <- zip (Set.toList vs) [(1::Int)..]]

    defs = do
      (v,t) <- ts
      let v2 = env Map.! v
      return $ showString $ printf "(define %s::%s) ; %s"  v2 t v

    optimality = list [showString "forall", decl, body]
      where
        decl = list [showString $ printf "%s::%s" (env2 Map.! v) t | (v,t) <- ts]
        body = list [showString "=>"
                    , and' (conditions True env2 lp)
                    , list [ showString $ if LP.isMinimize lp then "<=" else ">="
                           , expr env obj, expr env2 obj
                           ]
                    ]

main :: IO ()
main = do
  s <- getContents
  case LP.parseString "-" s of
    Right lp -> putStrLn $ lp2ys lp ""
    Left err -> hPrint stderr err >> exitFailure

testFile :: FilePath -> IO ()
testFile fname = do
  result <- LP.parseFile fname
  case result of
    Right lp -> putStrLn $ lp2ys lp ""
    Left err -> hPrint stderr err

test :: IO ()
test = putStrLn $ lp2ys testdata ""

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
