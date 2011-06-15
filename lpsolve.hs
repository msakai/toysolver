-----------------------------------------------------------------------------
-- |
-- Module      :  lpsolve
-- Copyright   :  (c) Masahiro Sakai 2011
-- License     :  BSD-style
-- 
-----------------------------------------------------------------------------

module Main where

import Control.Monad
import qualified Data.Set as Set
import qualified Data.Map as Map
import qualified Data.IntMap as IM
import System.Exit
import System.IO
import Text.Printf

import qualified Simplex
import qualified LPFile as LP

run :: LP.LP -> IO ()
run lp = do
  unless (Set.null (LP.integerVariables lp)) $ do
    hPutStrLn stderr "integer variables are not supported."
    exitFailure
  unless (Set.null (LP.binaryVariables lp)) $ do
    hPutStrLn stderr "binary variables are not supported."
    exitFailure
  unless (Set.null (LP.semiContinuousVariables lp)) $ do
    hPutStrLn stderr "semi-continuous variables are not supported."
    exitFailure

  let fun = if LP.isMinimize lp then Simplex.minimize else Simplex.maximize

  case fun obj (cs1 ++ cs2) of
    Simplex.OptUnknown -> do
      putStrLn "unknown"
      exitFailure
    Simplex.OptUnsat -> do
      putStrLn "unsat"
      exitFailure
    Simplex.Unbounded -> do
      putStrLn "unbounded"
      exitFailure
    Simplex.Optimum r m -> do
      putStrLn "optimum"
      print $ showValue r
      forM_ (Set.toList vs) $ \v -> do
        printf "%s: %s\n" v (showValue (m IM.! (nameToVar Map.! v)))
  where
    vs = LP.variables lp
    vsAssoc = zip (Set.toList vs) [0..]
    nameToVar = Map.fromList vsAssoc
    varToName = IM.fromList [(v,name) | (name,v) <- vsAssoc]

    compileE :: LP.Expr -> Simplex.Expr Rational
    compileE (LP.Const r) = Simplex.Const r
    compileE (LP.Var v) = Simplex.Var (nameToVar Map.! v)
    compileE (a LP.:+: b) = compileE a Simplex.:+: compileE b
    compileE (a LP.:*: b) = compileE a Simplex.:*: compileE b
    compileE (a LP.:/: b) = compileE a Simplex.:/: compileE b

    obj = compileE $ snd $ LP.objectiveFunction lp

    cs1 = do
      v <- Set.toList vs
      let v2 = Simplex.Var (nameToVar Map.! v)
      let (l,u) = LP.getBounds lp v
      [Simplex.Const x Simplex..<=. v2 | LP.Finite x <- return l] ++
        [v2 Simplex..<=. Simplex.Const x | LP.Finite x <- return u]
    cs2 = do
      (_, _, (lhs, rel, rhs)) <- LP.constraints lp
      let rel2 = case rel of
                  LP.Ge  -> Simplex.Ge
                  LP.Le  -> Simplex.Le
                  LP.Eql -> Simplex.Eql
      return (Simplex.Rel (compileE lhs) rel2 (Simplex.Const rhs))

    showValue v = show (fromRational v :: Double)

main :: IO ()
main = do
  s <- getContents
  case LP.parseString "-" s of
    Left err -> hPrint stderr err >> exitFailure
    Right lp -> run lp
