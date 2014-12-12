{-# OPTIONS_GHC -Wall #-}
module ToySolver.Arith.FourierMotzkin.FOL
    ( solveFormula
    , eliminateQuantifiers
    , eliminateQuantifiers'
    )
    where

import Control.Monad
import qualified Data.IntSet as IS
import Data.Maybe
import Data.VectorSpace hiding (project)

import ToySolver.Data.ArithRel
import ToySolver.Data.Boolean
import ToySolver.Data.DNF
import qualified ToySolver.Data.FOL.Arith as FOL
import qualified ToySolver.Data.LA.FOL as LAFOL
import ToySolver.Data.Var

import ToySolver.Arith.FourierMotzkin.Core

-- ---------------------------------------------------------------------------

solveFormula :: VarSet -> FOL.Formula (FOL.Atom Rational) -> FOL.SatResult Rational
solveFormula vs formula =
  case eliminateQuantifiers' formula of
    Nothing -> FOL.Unknown
    Just dnf ->
      case msum [solve' vs xs | xs <- unDNF dnf] of
        Nothing -> FOL.Unsat
        Just m -> FOL.Sat m

eliminateQuantifiers :: FOL.Formula (FOL.Atom Rational) -> Maybe (FOL.Formula (FOL.Atom Rational))
eliminateQuantifiers phi = do
  dnf <- eliminateQuantifiers' phi
  return $ orB $ map (andB . map (LAFOL.toFOLFormula . toLAAtom)) $ unDNF dnf

eliminateQuantifiers' :: FOL.Formula (FOL.Atom Rational) -> Maybe (DNF Constr)
eliminateQuantifiers' = f
  where
    f FOL.T = return true
    f FOL.F = return false
    f (FOL.Atom (ArithRel a op b)) = do
       a' <- LAFOL.fromFOLExpr a
       b' <- LAFOL.fromFOLExpr b
       return $ fromLAAtom $ ArithRel a' op b'
    f (FOL.And a b) = liftM2 (.&&.) (f a) (f b)
    f (FOL.Or a b) = liftM2 (.||.) (f a) (f b)
    f (FOL.Not a) = f (FOL.pushNot a)
    f (FOL.Imply a b) = f (notB a .||.  b)
    f (FOL.Equiv a b) = f ((a .=>. b) .&&. (b .=>.a))
    f (FOL.Forall v a) = do
      dnf <- f (FOL.Exists v (FOL.pushNot a))
      return (negateDNFConstr dnf)
    f (FOL.Exists v a) = do
      dnf <- f a
      return $ orB [DNF $ maybeToList $ fmap fst $ project' v xs | xs <- unDNF dnf]

negateDNFConstr :: DNF Constr -> DNF Constr
negateDNFConstr (DNF xs) = orB . map (andB . map f) $ xs
  where
    f :: Constr -> DNF Constr
    f (IsPos t)    = DNF [[IsNonneg (negateV t)]]
    f (IsNonneg t) = DNF [[IsPos (negateV t)]]
    f (IsZero t)   = DNF [[IsPos t], [IsPos (negateV t)]]

-- ---------------------------------------------------------------------------
