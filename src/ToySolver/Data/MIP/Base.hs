{-# OPTIONS_GHC -Wall #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.Data.MIP.Base
-- Copyright   :  (c) Masahiro Sakai 2011-2014
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  portable
--
-- Mixed-Integer Programming Problems with some commmonly used extensions
--
-----------------------------------------------------------------------------
module ToySolver.Data.MIP.Base
  ( Problem (..)
  , Expr
  , Term (..)
  , OptDir (..)
  , ObjectiveFunction
  , Constraint (..)
  , Bounds
  , Label
  , Var
  , VarType (..)
  , BoundExpr
  , Extended (..)
  , RelOp (..)
  , SOSType (..)
  , SOSConstraint (..)
  , defaultBounds
  , defaultLB
  , defaultUB
  , toVar
  , fromVar
  , getVarType
  , getBounds
  , variables
  , integerVariables
  , semiContinuousVariables
  , semiIntegerVariables

  -- * Utilities
  , Variables (..)
  , intersectBounds
  ) where

import Data.Default.Class
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Interned (intern, unintern)
import Data.Interned.String
import Data.ExtendedReal
import Data.OptDir

-- ---------------------------------------------------------------------------

-- | Problem
data Problem
  = Problem
  { dir :: OptDir
  , objectiveFunction :: ObjectiveFunction
  , constraints :: [Constraint]
  , sosConstraints :: [SOSConstraint]
  , userCuts :: [Constraint]
  , varType :: Map Var VarType
  , varBounds :: Map Var Bounds
  }
  deriving (Show, Eq, Ord)

instance Default Problem where
  def = Problem
        { dir = OptMin
        , objectiveFunction = (Nothing, [])
        , constraints = []
        , sosConstraints = []
        , userCuts = []
        , varType = Map.empty
        , varBounds = Map.empty
        }

-- | expressions
type Expr = [Term]

-- | terms
data Term = Term Rational [Var]
  deriving (Eq, Ord, Show)

-- | objective function
type ObjectiveFunction = (Maybe Label, Expr)

-- | constraint
data Constraint
  = Constraint
  { constrLabel     :: Maybe Label
  , constrIndicator :: Maybe (Var, Rational)
  , constrBody      :: (Expr, RelOp, Rational)
  , constrIsLazy    :: Bool
  }
  deriving (Eq, Ord, Show)

instance Default Constraint where
  def = Constraint
        { constrLabel = Nothing
        , constrIndicator = Nothing
        , constrBody = ([], Le, 0)
        , constrIsLazy = False
        }

data VarType
  = ContinuousVariable
  | IntegerVariable
-- 'nothaddock' is inserted not to confuse haddock
  -- nothaddock | BinaryVariable
  | SemiContinuousVariable
  | SemiIntegerVariable
  deriving (Eq, Ord, Show)

instance Default VarType where
  def = ContinuousVariable

-- | type for representing lower/upper bound of variables
type Bounds = (BoundExpr, BoundExpr)

-- | label
type Label = String

-- | variable
type Var = InternedString

-- | type for representing lower/upper bound of variables
type BoundExpr = Extended Rational

-- | relational operators
data RelOp = Le | Ge | Eql
    deriving (Eq, Ord, Enum, Show)

-- | types of SOS (special ordered sets) constraints
data SOSType
  = S1 -- ^ Type 1 SOS constraint
  | S2 -- ^ Type 2 SOS constraint
    deriving (Eq, Ord, Enum, Show, Read)

-- | SOS (special ordered sets) constraints
data SOSConstraint
  = SOSConstraint
  { sosLabel :: Maybe Label
  , sosType  :: SOSType
  , sosBody  :: [(Var, Rational)]
  }
  deriving (Eq, Ord, Show)

class Variables a where
  vars :: a -> Set Var

instance Variables a => Variables [a] where
  vars = Set.unions . map vars

instance (Variables a, Variables b) => Variables (Either a b) where
  vars (Left a)  = vars a
  vars (Right b) = vars b

instance Variables Problem where
  vars = variables

instance Variables Term where
  vars (Term _ xs) = Set.fromList xs

instance Variables Constraint where
  vars Constraint{ constrIndicator = ind, constrBody = (lhs, _, _) } =
    vars lhs `Set.union` vs2
    where
      vs2 = maybe Set.empty (Set.singleton . fst) ind

instance Variables SOSConstraint where
  vars SOSConstraint{ sosBody = xs } = Set.fromList (map fst xs)

-- | default bounds
defaultBounds :: Bounds
defaultBounds = (defaultLB, defaultUB)

-- | default lower bound (0)
defaultLB :: BoundExpr
defaultLB = 0

-- | default upper bound (+∞)
defaultUB :: BoundExpr
defaultUB = PosInf

-- | convert a string into a variable
toVar :: String -> Var
toVar = intern

-- | convert a variable into a string
fromVar :: Var -> String
fromVar = unintern

-- | looking up bounds for a variable
getVarType :: Problem -> Var -> VarType
getVarType lp v = Map.findWithDefault def v (varType lp)

-- | looking up bounds for a variable
getBounds :: Problem -> Var -> Bounds
getBounds lp v = Map.findWithDefault defaultBounds v (varBounds lp)

intersectBounds :: Bounds -> Bounds -> Bounds
intersectBounds (lb1,ub1) (lb2,ub2) = (max lb1 lb2, min ub1 ub2)

variables :: Problem -> Set Var
variables lp = Map.keysSet $ varType lp

integerVariables :: Problem -> Set Var
integerVariables lp = Map.keysSet $ Map.filter (IntegerVariable ==) (varType lp)

semiContinuousVariables :: Problem -> Set Var
semiContinuousVariables lp = Map.keysSet $ Map.filter (SemiContinuousVariable ==) (varType lp)

semiIntegerVariables :: Problem -> Set Var
semiIntegerVariables lp = Map.keysSet $ Map.filter (SemiIntegerVariable ==) (varType lp)
