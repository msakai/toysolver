-----------------------------------------------------------------------------
-- |
-- Module      :  toysolver
-- Copyright   :  (c) Masahiro Sakai 2011
-- License     :  BSD-style
-- 
-----------------------------------------------------------------------------

module Main where

import Control.Monad
import Data.List
import qualified Data.Set as Set
import qualified Data.Map as Map
import qualified Data.IntMap as IM
import qualified Data.IntSet as IS
import System.Exit
import System.Environment
import System.Console.GetOpt
import System.IO
import Text.Printf

import Expr
import Formula
import qualified LA
import qualified OmegaTest
import qualified Cooper
import qualified MIPSolverHL
import qualified LPFile as LP

-- ---------------------------------------------------------------------------

data Flag
    = Help
    | Version
    | Solver String
{-
    | SatMode
    | Load String
    | Trace String
-}
    deriving Eq

options :: [OptDescr Flag]
options =
    [ Option ['h'] ["help"]    (NoArg Help)            "show help"
    , Option ['v'] ["version"] (NoArg Version)         "show version number"
    , Option [] ["solver"] (ReqArg Solver "SOLVER")    "mip (default), omega-test, cooper"
{-
    , Option ['l'] ["load"]    (ReqArg Load "FILE") "load FILE"
    , Option ['t'] ["trace"]    (OptArg (Trace . fromMaybe "on") "[on|off]")
             "enable/disable trace"
-}
    ]

version :: [Int]
version = [0,0,1]

versionStr :: String
versionStr = intercalate "." $ map show $ version

header :: String
header = "Usage: toysolver [OPTION...] file.lp"

-- ---------------------------------------------------------------------------

run :: String -> LP.LP -> IO ()
run solver lp = do
  unless (Set.null (LP.semiContinuousVariables lp)) $ do
    hPutStrLn stderr "semi-continuous variables are not supported."
    exitFailure

  case solver of
    _ | solver `elem` ["omega-test", "cooper"] -> solveByQE
    _ -> solveByMIP
  where
    vs = LP.variables lp
    vsAssoc = zip (Set.toList vs) [0..]
    nameToVar = Map.fromList vsAssoc
    varToName = IM.fromList [(v,name) | (name,v) <- vsAssoc]

    compileE :: LP.Expr -> Expr Rational
    compileE = foldr (+) (Const 0) . map compileT

    compileT :: LP.Term -> Expr Rational
    compileT (LP.Term c vs) =
      foldr (*) (Const c) [Var (nameToVar Map.! v) | v <- vs]

    obj = compileE $ snd $ LP.objectiveFunction lp

    cs1 = do
      v <- Set.toList vs
      let v2 = Var (nameToVar Map.! v)
      let (l,u) = LP.getBounds lp v
      [Const x .<=. v2 | LP.Finite x <- return l] ++
        [v2 .<=. Const x | LP.Finite x <- return u]
    cs2 = do
      (_, ind, (lhs, rel, rhs)) <- LP.constraints lp
      let rel2 = case rel of
                  LP.Ge  -> Ge
                  LP.Le  -> Le
                  LP.Eql -> Eql
      case ind of
        Nothing -> return (Rel (compileE lhs) rel2 (Const rhs))
        Just _ -> error "indicator constraint is not supported yet"
    cs3 = do
      v <- Set.toList (LP.binaryVariables lp)
      let v' = nameToVar Map.! v
      [ Const 0 .<=. Var v', Var v' .<=. Const 1 ]

    ivs = f (LP.integerVariables lp) `IS.union` f (LP.binaryVariables lp)
      where
        f = IS.fromList . map (nameToVar Map.!) . Set.toList

    solveByQE =
      case mapM LA.compileAtom (cs1 ++ cs2 ++ cs3) of
        Nothing -> do
          putStrLn "unknown"
          exitFailure
        Just cs ->
          case f cs ivs of
            Nothing -> do
              putStrLn "unsat"
              exitFailure
            Just m -> do
              putStrLn "sat"
              putStrLn $ showValue (Expr.eval m obj)
              printModel m vs
       where
         f = case solver of
               "omega-test" -> OmegaTest.solveQFLA
               "cooper"     -> Cooper.solveQFLA
               _ -> error "unknown solver"

    solveByMIP =
      case MIPSolverHL.optimize (LP.dir lp) obj (cs1 ++ cs2 ++ cs3) ivs of
        OptUnknown -> do
          putStrLn "unknown"
          exitFailure
        OptUnsat -> do
          putStrLn "unsat"
          exitFailure
        Unbounded -> do
          putStrLn "unbounded"
          exitFailure
        Optimum r m -> do
          putStrLn "optimum"
          putStrLn $ showValue r
          printModel m vs               

    printModel :: Model Rational -> Set.Set String -> IO ()
    printModel m vs =
      forM_ (Set.toList vs) $ \v -> do
        printf "%s: %s\n" v (showValue (m IM.! (nameToVar Map.! v)))

    showValue :: Rational -> String
    showValue v = show (fromRational v :: Double)

-- ---------------------------------------------------------------------------

getSolver :: [Flag] -> String
getSolver xs = last $ "mip" : [s | Solver s <- xs]

main :: IO ()
main = do
  args <- getArgs
  case getOpt Permute options args of
    (o,_,[])
      | Help `elem` o    -> putStrLn (usageInfo header options)
      | Version `elem` o -> putStrLn versionStr
    (o,[fname],[]) -> do
      ret <- LP.parseFile fname
      case ret of
        Left err -> hPrint stderr err >> exitFailure
        Right lp -> run (getSolver o) lp
    (_,_,errs) ->
        hPutStrLn stderr $ concat errs ++ usageInfo header options
