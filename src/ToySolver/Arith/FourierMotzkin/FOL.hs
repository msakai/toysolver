{-# OPTIONS_GHC -Wall #-}
module ToySolver.Arith.FourierMotzkin.FOL
    ( solveFormula
    , eliminateQuantifiers
    , eliminateQuantifiers'
    )
    where

import Control.Monad
import Data.Maybe
import Data.VectorSpace hiding (project)

import ToySolver.Data.OrdRel
import ToySolver.Data.Boolean
import ToySolver.Data.DNF
import qualified ToySolver.Data.FOL.Arith as FOL
import qualified ToySolver.Data.LA.FOL as LAFOL
import ToySolver.Data.Var

import ToySolver.Arith.FourierMotzkin.Base

-- ---------------------------------------------------------------------------

-- | 
--
-- * @'solveFormula' {x1,…,xm} φ@ returns @'Sat' M@ such that @M ⊧_LRA φ@ when such @M@ exists,
--
-- * returns @'Unsat'@ when such @M@ does not exists, and
--
-- * returns @'Unknown'@ when @φ@ is beyond LRA.
-- 
solveFormula :: VarSet -> FOL.Formula (FOL.Atom Rational) -> FOL.SatResult Rational
solveFormula vs formula =
  case eliminateQuantifiers' formula of
    Nothing -> FOL.Unknown
    Just dnf ->
      case msum [solve' vs xs | xs <- unDNF dnf] of
        Nothing -> FOL.Unsat
        Just m -> FOL.Sat m

-- | Eliminate quantifiers and returns equivalent quantifier-free formula.
--
-- @'eliminateQuantifiers' φ@ returns @(ψ, lift)@ such that:
-- 
-- * ψ is a quantifier-free formula and @LRA ⊢ ∀y1, …, yn. φ ↔ ψ@ where @{y1, …, yn} = FV(φ) ⊇ FV(ψ)@, and
-- 
-- * if @M ⊧_LRA ψ@ then @lift M ⊧_LRA φ@.
--
-- φ may or may not be a closed formula.
--
eliminateQuantifiers :: FOL.Formula (FOL.Atom Rational) -> Maybe (FOL.Formula (FOL.Atom Rational))
eliminateQuantifiers phi = do
  dnf <- eliminateQuantifiers' phi
  return $ orB $ map (andB . map (LAFOL.toFOLFormula . toLAAtom)) $ unDNF dnf

eliminateQuantifiers' :: FOL.Formula (FOL.Atom Rational) -> Maybe (DNF Constr)
eliminateQuantifiers' = f
  where
    f FOL.T = return true
    f FOL.F = return false
    f (FOL.Atom (OrdRel a op b)) = do
       a' <- LAFOL.fromFOLExpr a
       b' <- LAFOL.fromFOLExpr b
       return $ fromLAAtom $ OrdRel a' op b'
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
