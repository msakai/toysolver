{-# OPTIONS_GHC -Wall #-}
module ToySolver.FourierMotzkin.FOL
    ( solveFormula
    , eliminateQuantifiers
    , eliminateQuantifiers'
    )
    where

import Control.Monad
import qualified Data.IntSet as IS
import Data.Maybe

import ToySolver.Algebra.Lattice.Boolean

import ToySolver.Data.ArithRel
import ToySolver.Data.DNF
import qualified ToySolver.Data.FOL.Arith as FOL
import qualified ToySolver.Data.LA.FOL as LAFOL
import ToySolver.Data.Var

import ToySolver.FourierMotzkin.Core

-- ---------------------------------------------------------------------------

solveFormula :: [Var] -> FOL.Formula (FOL.Atom Rational) -> FOL.SatResult Rational
solveFormula vs formula =
  case eliminateQuantifiers' formula of
    Nothing -> FOL.Unknown
    Just dnf ->
      case msum [solve' (IS.fromList vs) xs | xs <- unDNF dnf] of
        Nothing -> FOL.Unsat
        Just m -> FOL.Sat m

eliminateQuantifiers :: FOL.Formula (FOL.Atom Rational) -> Maybe (FOL.Formula (FOL.Atom Rational))
eliminateQuantifiers phi = do
  dnf <- eliminateQuantifiers' phi
  return $ orB $ map (andB . map (LAFOL.toFOLFormula . toLAAtom)) $ unDNF dnf

eliminateQuantifiers' :: FOL.Formula (FOL.Atom Rational) -> Maybe (DNF Lit)
eliminateQuantifiers' = f
  where
    f FOL.T = return true
    f FOL.F = return false
    f (FOL.Atom (Rel a op b)) = do
       a' <- LAFOL.fromFOLExpr a
       b' <- LAFOL.fromFOLExpr b
       return $ fromLAAtom $ Rel a' op b'
    f (FOL.And a b) = liftM2 (.&&.) (f a) (f b)
    f (FOL.Or a b) = liftM2 (.||.) (f a) (f b)
    f (FOL.Not a) = f (FOL.pushNot a)
    f (FOL.Imply a b) = f (FOL.Or (FOL.Not a) b)
    f (FOL.Equiv a b) = f (FOL.And (FOL.Imply a b) (FOL.Imply b a))
    f (FOL.Forall v a) = do
      dnf <- f (FOL.Exists v (FOL.pushNot a))
      return (notB dnf)
    f (FOL.Exists v a) = do
      dnf <- f a
      return $ orB [DNF $ maybeToList $ fmap fst $ project' v xs | xs <- unDNF dnf]

-- ---------------------------------------------------------------------------
