{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module TseitingEncoding
  ( Var
  , Lit
  , Clause
  , CNF
  , Formula
  , CNFGenMonad (..)
  , emitFormula
  , CNFGen
  , runCNFGen
  , execCNFGen
  , evalCNFGen
  ) where

import Control.Monad
import Control.Monad.RWS

type Var = Int
data Lit = Pos Var | Neg Var deriving (Show, Eq, Ord)
type Clause = [Lit]
type CNF = [Clause]

data Formula
  = Var Var
  | And [Formula]
  | Or [Formula]
  | Not Formula
  | Imply Formula Formula
  deriving (Show, Eq, Ord)

class Monad m => CNFGenMonad m where
  newVar :: m Var
  emitClause :: Clause -> m ()

emitFormula :: CNFGenMonad m => Formula -> m ()
emitFormula x = do
  v <- enc x
  emitClause [Pos v]

enc :: CNFGenMonad m => Formula -> m Var
enc (Var v) = return v
enc (And xs) = do
  v <- newVar
  vs <- mapM enc xs
  forM vs $ \v2 -> emitClause [Neg v, Pos v2]
  emitClause (Pos v : map Neg vs)
  return v
enc (Or xs) = do
  v <- newVar
  vs <- mapM enc xs
  forM vs $ \v2 -> emitClause [Pos v, Neg v2]
  emitClause (Neg v : map Pos vs)
  return v
enc (Not x) = do
  v <- newVar
  v2 <- enc x
  emitClause [Pos v, Pos v2]
  emitClause [Neg v, Neg v2]
  return v
enc (Imply x y) = enc (Or [Not x, y])

newtype CNFGen a = CNFGen (RWS () (Endo [Clause]) Int a)
  deriving Monad

instance CNFGenMonad CNFGen where
  newVar = CNFGen $ do
    cnt <- get
    put (cnt+1)
    return cnt
  emitClause cl = CNFGen (tell (Endo (cl:)))

runCNFGen :: CNFGen x -> (x, Int, CNF)
runCNFGen (CNFGen m) =
  case runRWS m () 0 of
    (x, cnt, f) -> (x, cnt, appEndo f [])

execCNFGen :: CNFGen x -> (Int, CNF)
execCNFGen m =
  case runCNFGen m of
    (_,cnt,cnf) -> (cnt,cnf)

evalCNFGen :: CNFGen x -> (x, CNF)
evalCNFGen m = 
  case runCNFGen m of
    (x,_,cnf) -> (x,cnf)

test :: (Int, CNF)
test = execCNFGen $ do
  x <- newVar
  y <- newVar
  z <- newVar
  emitFormula $ And [Or [Var x, Var y] , Var z]
{-
=>
(5
, [ [Pos 4,Neg 0]
  , [Pos 4,Neg 1]
  , [Neg 4,Pos 0,Pos 1]
  , [Neg 3,Pos 4]
  , [Neg 3,Pos 2]
  , [Pos 3,Neg 4,Neg 2]
  , [Pos 3]
  ]
)
-}
