{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies #-}
module Algorithm.FourierMotzkin.FOL
    ( solveFormula
    , eliminateQuantifiers
    , eliminateQuantifiers'
    )
    where

import Control.Monad
import qualified Data.IntSet as IS

import Data.ArithRel
import Data.Expr
import Data.Formula
import qualified Data.LA.FOL as LA

import Algorithm.FourierMotzkin.Core

-- ---------------------------------------------------------------------------

solveFormula :: [Var] -> Formula (Atom Rational) -> SatResult Rational
solveFormula vs formula =
  case eliminateQuantifiers' formula of
    Nothing -> Unknown
    Just dnf ->
      case msum [solve' (IS.fromList vs) xs | xs <- unDNF dnf] of
        Nothing -> Unsat
        Just m -> Sat m

eliminateQuantifiers :: Formula (Atom Rational) -> Maybe (Formula (Atom Rational))
eliminateQuantifiers phi = do
  dnf <- eliminateQuantifiers' phi
  return $ orB $ map (andB . map (LA.toFOLFormula . toLAAtom)) $ unDNF dnf

eliminateQuantifiers' :: Formula (Atom Rational) -> Maybe (DNF Lit)
eliminateQuantifiers' = f
  where
    f T = return true
    f F = return false
    f (Atom (Rel a op b)) = do
       a' <- LA.fromFOLExpr a
       b' <- LA.fromFOLExpr b
       return $ fromLAAtom $ Rel a' op b'
    f (And a b) = liftM2 (.&&.) (f a) (f b)
    f (Or a b) = liftM2 (.||.) (f a) (f b)
    f (Not a) = f (pushNot a)
    f (Imply a b) = f (Or (Not a) b)
    f (Equiv a b) = f (And (Imply a b) (Imply b a))
    f (Forall v a) = do
      dnf <- f (Exists v (pushNot a))
      return (notB dnf)
    f (Exists v a) = do
      dnf <- f a
      return $ orB [DNF $ map fst $ project' v xs | xs <- unDNF dnf]

-- ---------------------------------------------------------------------------
