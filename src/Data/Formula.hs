{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Formula
-- Copyright   :  (c) Masahiro Sakai 2011
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  non-portable (MultiParamTypeClasses, FunctionalDependencies)
--
-- Formula of first order logic.
-- 
-----------------------------------------------------------------------------
module Data.Formula
  (

  -- * Overloaded operations for formula.
    Complement (..)
  , Boolean (..)

  -- * Relational operators
  , RelOp (..)
  , Rel (..)
  , (.<.), (.<=.), (.>=.), (.>.), (.==.), (./=.)
  , flipOp
  , negOp
  , showOp

  -- * Concrete formula
  , Atom (..)
  , Formula (..)
  , pushNot
  , DNF (..)
  ) where

import qualified Data.IntSet as IS
import Data.Expr

-- ---------------------------------------------------------------------------

infix 4 .<., .<=., .>=., .>., .==., ./=.
infixr 3 .&&.
infixr 2 .||.
infix 1 .=>. , .<=>.

-- | types that can be negated.
class Complement a where
  notF :: a -> a

-- | types that can be combined with boolean operations.
class Complement a => Boolean a where
  true, false :: a
  (.&&.), (.||.), (.=>.), (.<=>.) :: a -> a -> a

  -- | n-ary conjunction
  andF :: [a] -> a

  -- | n-ary disjunction
  orF :: [a] -> a

  x .=>. y = notF x .||. y
  x .<=>. y = (x .=>. y) .&&. (y .=>. x)
  andF = foldr (.&&.) true
  orF = foldr (.||.) false

-- ---------------------------------------------------------------------------

-- | relational operators
data RelOp = Lt | Le | Ge | Gt | Eql | NEq
    deriving (Show, Eq, Ord)

-- | type class for constructing relational formula
class Rel e r | r -> e where
  rel :: RelOp -> e -> e -> r

-- | constructing relational formula
(.<.) :: Rel e r => e -> e -> r
a .<. b  = rel Lt  a b

-- | constructing relational formula
(.<=.) :: Rel e r => e -> e -> r
a .<=. b = rel Le  a b

-- | constructing relational formula
(.>.) :: Rel e r => e -> e -> r
a .>. b  = rel Gt  a b

-- | constructing relational formula
(.>=.) :: Rel e r => e -> e -> r
a .>=. b = rel Ge  a b

-- | constructing relational formula
(.==.) :: Rel e r => e -> e -> r
a .==. b = rel Eql a b

-- | constructing relational formula
(./=.) :: Rel e r => e -> e -> r
a ./=. b = rel NEq a b

-- | flipping relational operator
--
-- @rel (flipOp op) a b@ is equivalent to @rel op b a@
flipOp :: RelOp -> RelOp 
flipOp Le = Ge
flipOp Ge = Le
flipOp Lt = Gt
flipOp Gt = Lt
flipOp Eql = Eql
flipOp NEq = NEq

-- | negating relational operator
--
-- @rel (negOp op) a b@ is equivalent to @notF (rel op a b)@
negOp :: RelOp -> RelOp
negOp Lt = Ge
negOp Le = Gt
negOp Ge = Lt
negOp Gt = Le
negOp Eql = NEq
negOp NEq = Eql

-- | operator symbol
showOp :: RelOp -> String
showOp Lt = "<"
showOp Le = "<="
showOp Ge = ">="
showOp Gt = ">"
showOp Eql = "="
showOp NEq = "/="

-- ---------------------------------------------------------------------------

-- | Atomic formula
data Atom c = Rel (Expr c) RelOp (Expr c)
    deriving (Show, Eq, Ord)

instance Complement (Atom c) where
  notF (Rel lhs op rhs) = Rel lhs (negOp op) rhs

instance Variables (Atom c) where
  vars (Rel a _ b) = vars a `IS.union` vars b

instance Rel (Expr c) (Atom c) where
  rel op a b = Rel a op b

-- ---------------------------------------------------------------------------

-- | formulas of first order logic
data Formula c
    = T
    | F
    | Atom (Atom c)
    | And (Formula c) (Formula c)
    | Or (Formula c) (Formula c)
    | Not (Formula c)
    | Imply (Formula c) (Formula c)
    | Equiv (Formula c) (Formula c)
    | Forall Var (Formula c)
    | Exists Var (Formula c)
    deriving (Show, Eq, Ord)

instance Variables (Formula c) where
  vars T = IS.empty
  vars F = IS.empty
  vars (Atom atom) = vars atom
  vars (And a b) = vars a `IS.union` vars b
  vars (Or a b) = vars a `IS.union` vars b
  vars (Not a) = vars a
  vars (Imply a b) = vars a `IS.union` vars b
  vars (Equiv a b) = vars a `IS.union` vars b
  vars (Forall v a) = IS.delete v (vars a)
  vars (Exists v a) = IS.delete v (vars a)

instance Complement (Formula c) where
  notF = Not

instance Boolean (Formula c) where
  true = T
  false = F
  (.&&.) = And
  (.||.) = Or
  (.=>.) = Imply
  (.<=>.) = Equiv

instance Rel (Expr c) (Formula c) where
  rel op a b = Atom $ rel op a b

-- | convert a formula into negation normal form
pushNot :: Formula c -> Formula c
pushNot T = F
pushNot F = T
pushNot (Atom (Rel a op b)) = Atom $ Rel a (negOp op) b
pushNot (And a b) = Or (pushNot a) (pushNot b)
pushNot (Or a b) = And (pushNot a) (pushNot b)
pushNot (Not a) = a
pushNot (Imply a b) = And a (pushNot b)
pushNot (Equiv a b) = Or (And a (pushNot b)) (And b (pushNot a))
pushNot (Forall v a) = Exists v (pushNot a)
pushNot (Exists v a) = Forall v (pushNot a)

-- | Disjunctive normal form
newtype DNF lit
  = DNF
  { unDNF :: [[lit]] -- ^ list of conjunction of literals
  } deriving (Show)

instance Complement lit => Complement (DNF lit) where
  notF (DNF xs) = DNF . sequence . map (map notF) $ xs

instance Complement lit => Boolean (DNF lit) where
  true = DNF [[]]
  false = DNF []
  DNF xs .&&. DNF ys = DNF [x++y | x<-xs, y<-ys]
  DNF xs .||. DNF ys = DNF (xs++ys)
