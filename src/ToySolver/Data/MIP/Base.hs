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
  , Expr (..)
  , varExpr
  , constExpr
  , terms
  , Term (..)
  , OptDir (..)
  , ObjectiveFunction (..)
  , Constraint (..)
  , (.==.)
  , (.<=.)
  , (.>=.)
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

  -- * File I/O options
  , FileOptions (..)

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
import System.IO (TextEncoding)

infix 4 .<=., .>=., .==.

-- ---------------------------------------------------------------------------

-- | Problem
data Problem
  = Problem
  { name :: Maybe String
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
        { name = Nothing
        , objectiveFunction = def
        , constraints = []
        , sosConstraints = []
        , userCuts = []
        , varType = Map.empty
        , varBounds = Map.empty
        }

-- | expressions
newtype Expr = Expr [Term]
  deriving (Eq, Ord, Show)

varExpr :: Var -> Expr
varExpr v = Expr [Term 1 [v]]

constExpr :: Rational -> Expr
constExpr 0 = Expr []
constExpr c = Expr [Term c []]
           
terms :: Expr -> [Term]
terms (Expr ts) = ts

instance Num Expr where
  Expr e1 + Expr e2 = Expr (e1 ++ e2)
  Expr e1 * Expr e2 = Expr [Term (c1*c2) (vs1 ++ vs2) | Term c1 vs1 <- e1, Term c2 vs2 <- e2]
  negate (Expr e) = Expr [Term (-c) vs | Term c vs <- e]
  abs = id
  signum _ = 1
  fromInteger 0 = Expr []
  fromInteger c = Expr [Term (fromInteger c) []]

-- | terms
data Term = Term Rational [Var]
  deriving (Eq, Ord, Show)

-- | objective function
data ObjectiveFunction
  = ObjectiveFunction
  { objLabel :: Maybe Label
  , objDir :: OptDir
  , objExpr :: Expr
  }
  deriving (Eq, Ord, Show)

instance Default ObjectiveFunction where
  def =
    ObjectiveFunction
    { objLabel = Nothing
    , objDir = OptMin
    , objExpr = 0
    }

-- | constraint
data Constraint
  = Constraint
  { constrLabel     :: Maybe Label
  , constrIndicator :: Maybe (Var, Rational)
  , constrExpr      :: Expr
  , constrLB        :: BoundExpr
  , constrUB        :: BoundExpr
  , constrIsLazy    :: Bool
  }
  deriving (Eq, Ord, Show)

(.==.) :: Expr -> Expr -> Constraint
lhs .==. rhs =
  case splitConst (lhs - rhs) of
    (e, c) -> def{ constrExpr = e, constrLB = Finite (- c), constrUB = Finite (- c) }

(.<=.) :: Expr -> Expr -> Constraint
lhs .<=. rhs =
  case splitConst (lhs - rhs) of
    (e, c) -> def{ constrExpr = e, constrUB = Finite (- c) }

(.>=.) :: Expr -> Expr -> Constraint
lhs .>=. rhs =
  case splitConst (lhs - rhs) of
    (e, c) -> def{ constrExpr = e, constrLB = Finite (- c) }

splitConst :: Expr -> (Expr, Rational)
splitConst e = (e2, c)
  where
    e2 = Expr [t | t@(Term _ (_:_)) <- terms e]
    c = sum [c | Term c [] <- terms e]
    
instance Default Constraint where
  def = Constraint
        { constrLabel = Nothing
        , constrIndicator = Nothing
        , constrExpr = 0
        , constrLB = -inf
        , constrUB = inf
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

instance Variables Expr where
  vars (Expr e) = vars e

instance Variables Term where
  vars (Term _ xs) = Set.fromList xs

instance Variables ObjectiveFunction where
  vars ObjectiveFunction{ objExpr = e } = vars e

instance Variables Constraint where
  vars Constraint{ constrIndicator = ind, constrExpr = e } = Set.union (vars e) vs2
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
getVarType mip v = Map.findWithDefault def v (varType mip)

-- | looking up bounds for a variable
getBounds :: Problem -> Var -> Bounds
getBounds mip v = Map.findWithDefault defaultBounds v (varBounds mip)

intersectBounds :: Bounds -> Bounds -> Bounds
intersectBounds (lb1,ub1) (lb2,ub2) = (max lb1 lb2, min ub1 ub2)

variables :: Problem -> Set Var
variables mip = Map.keysSet $ varType mip

integerVariables :: Problem -> Set Var
integerVariables mip = Map.keysSet $ Map.filter (IntegerVariable ==) (varType mip)

semiContinuousVariables :: Problem -> Set Var
semiContinuousVariables mip = Map.keysSet $ Map.filter (SemiContinuousVariable ==) (varType mip)

semiIntegerVariables :: Problem -> Set Var
semiIntegerVariables mip = Map.keysSet $ Map.filter (SemiIntegerVariable ==) (varType mip)

data FileOptions
  = FileOptions
  { optFileEncoding :: Maybe TextEncoding
  } deriving (Show)

instance Default FileOptions where
  def =
    FileOptions
    { optFileEncoding = Nothing
    }
