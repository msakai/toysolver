{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies, FlexibleInstances #-}
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
  , IsVar (..)
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
  , VarType (..)
  , BoundExpr
  , Extended (..)
  , RelOp (..)
  , SOSType (..)
  , SOSConstraint (..)
  , defaultBounds
  , defaultLB
  , defaultUB
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
import Data.String
import Data.ExtendedReal
import Data.OptDir
import System.IO (TextEncoding)

import Data.Interned
import qualified Data.Text as T
import qualified Data.ByteString.Char8 as BS
import qualified Data.Interned.String as IS
import qualified Data.Interned.Text as IT
import qualified Data.Interned.ByteString as IBS

infix 4 .<=., .>=., .==.

-- ---------------------------------------------------------------------------

-- | Problem
data Problem v c
  = Problem
  { name :: Maybe String
  , objectiveFunction :: ObjectiveFunction v c
  , constraints :: [Constraint v c]
  , sosConstraints :: [SOSConstraint v c]
  , userCuts :: [Constraint v c]
  , varType :: Map v VarType
  , varBounds :: Map v (Bounds c)
  }
  deriving (Show, Eq, Ord)

instance Num c => Default (Problem v c) where
  def = Problem
        { name = Nothing
        , objectiveFunction = def
        , constraints = []
        , sosConstraints = []
        , userCuts = []
        , varType = Map.empty
        , varBounds = Map.empty
        }

class (Ord v, IsString v) => IsVar v where
  fromVar :: v -> String
  
instance IsVar String where
  fromVar = id
  
instance IsVar BS.ByteString where
  fromVar = BS.unpack
  
instance IsVar T.Text where
  fromVar = T.unpack

instance IsVar IS.InternedString where
  fromVar = unintern

instance IsVar IBS.InternedByteString where
  fromVar = fromVar . unintern
  
instance IsVar IT.InternedText where
  fromVar = fromVar . unintern

-- | expressions
newtype Expr v c = Expr [Term v c]
  deriving (Eq, Ord, Show)

varExpr :: Num c => v -> Expr v c
varExpr v = Expr [Term 1 [v]]

constExpr :: (Num c, Eq c) => c -> Expr v c
constExpr 0 = Expr []
constExpr c = Expr [Term c []]
           
terms :: Expr v c -> [Term v c]
terms (Expr ts) = ts

instance Num c => Num (Expr v c) where
  Expr e1 + Expr e2 = Expr (e1 ++ e2)
  Expr e1 * Expr e2 = Expr [Term (c1*c2) (vs1 ++ vs2) | Term c1 vs1 <- e1, Term c2 vs2 <- e2]
  negate (Expr e) = Expr [Term (-c) vs | Term c vs <- e]
  abs = id
  signum _ = 1
  fromInteger 0 = Expr []
  fromInteger c = Expr [Term (fromInteger c) []]

-- | terms
data Term v c = Term c [v]
  deriving (Eq, Ord, Show)

-- | objective function
data ObjectiveFunction v c
  = ObjectiveFunction
  { objLabel :: Maybe v
  , objDir :: OptDir
  , objExpr :: Expr v c
  }
  deriving (Eq, Ord, Show)

instance Default (ObjectiveFunction v c) where
  def =
    ObjectiveFunction
    { objLabel = Nothing
    , objDir = OptMin
    , objExpr = Expr [] -- 0
    }

-- | constraint
data Constraint v c
  = Constraint
  { constrLabel     :: Maybe v
  , constrIndicator :: Maybe (v, c)
  , constrExpr      :: Expr v c
  , constrLB        :: BoundExpr c
  , constrUB        :: BoundExpr c
  , constrIsLazy    :: Bool
  }
  deriving (Eq, Ord, Show)

(.==.) :: Real c => Expr v c -> Expr v c -> Constraint v c
lhs .==. rhs =
  case splitConst (lhs - rhs) of
    (e, c) -> def{ constrExpr = e, constrLB = Finite (- c), constrUB = Finite (- c) }

(.<=.) :: Real c => Expr v c -> Expr v c -> Constraint v c
lhs .<=. rhs =
  case splitConst (lhs - rhs) of
    (e, c) -> def{ constrExpr = e, constrUB = Finite (- c) }

(.>=.) :: Real c => Expr v c -> Expr v c -> Constraint v c
lhs .>=. rhs =
  case splitConst (lhs - rhs) of
    (e, c) -> def{ constrExpr = e, constrLB = Finite (- c) }

splitConst :: Num c => Expr v c -> (Expr v c, c)
splitConst e = (e2, c)
  where
    e2 = Expr [t | t@(Term _ (_:_)) <- terms e]
    c = sum [c | Term c [] <- terms e]
    
instance Real c => Default (Constraint v c) where
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
type Bounds c = (BoundExpr c, BoundExpr c)

-- | type for representing lower/upper bound of variables
type BoundExpr c = Extended c

-- | relational operators
data RelOp = Le | Ge | Eql
    deriving (Eq, Ord, Enum, Show)

-- | types of SOS (special ordered sets) constraints
data SOSType
  = S1 -- ^ Type 1 SOS constraint
  | S2 -- ^ Type 2 SOS constraint
    deriving (Eq, Ord, Enum, Show, Read)

-- | SOS (special ordered sets) constraints
data SOSConstraint v c
  = SOSConstraint
  { sosLabel :: Maybe v
  , sosType  :: SOSType
  , sosBody  :: [(v, c)]
  }
  deriving (Eq, Ord, Show)

class IsVar v => Variables v a where
  vars :: a -> Set v

instance Variables v a => Variables v [a] where
  vars = Set.unions . map vars

instance (Variables v a, Variables v b) => Variables v (Either a b) where
  vars (Left a)  = vars a
  vars (Right b) = vars b

instance IsVar v => Variables v (Problem v c) where
  vars = variables

instance IsVar v => Variables v (Expr v c) where
  vars (Expr e) = vars e

instance IsVar v => Variables v (Term v c) where
  vars (Term _ xs) = Set.fromList xs

instance IsVar v => Variables v (ObjectiveFunction v c) where
  vars ObjectiveFunction{ objExpr = e } = vars e

instance IsVar v => Variables v (Constraint v c) where
  vars Constraint{ constrIndicator = ind, constrExpr = e } = Set.union (vars e) vs2
    where
      vs2 = maybe Set.empty (Set.singleton . fst) ind

instance IsVar v => Variables v (SOSConstraint v c) where
  vars SOSConstraint{ sosBody = xs } = Set.fromList (map fst xs)

-- | default bounds
defaultBounds :: Real c => Bounds c
defaultBounds = (defaultLB, defaultUB)

-- | default lower bound (0)
defaultLB :: Real c => BoundExpr c
defaultLB = 0

-- | default upper bound (+∞)
defaultUB :: Real c => BoundExpr c
defaultUB = PosInf

-- | looking up bounds for a variable
getVarType :: Ord v => Problem v c -> v -> VarType
getVarType mip v = Map.findWithDefault def v (varType mip)

-- | looking up bounds for a variable
getBounds :: (Ord v, Real c) => Problem v c -> v -> Bounds c
getBounds mip v = Map.findWithDefault defaultBounds v (varBounds mip)

intersectBounds :: Ord c => Bounds c -> Bounds c -> Bounds c
intersectBounds (lb1,ub1) (lb2,ub2) = (max lb1 lb2, min ub1 ub2)

variables :: IsVar v => Problem v c -> Set v
variables mip = Map.keysSet $ varType mip

integerVariables :: IsVar v => Problem v c -> Set v
integerVariables mip = Map.keysSet $ Map.filter (IntegerVariable ==) (varType mip)

semiContinuousVariables :: IsVar v => Problem v c -> Set v
semiContinuousVariables mip = Map.keysSet $ Map.filter (SemiContinuousVariable ==) (varType mip)

semiIntegerVariables :: IsVar v => Problem v c -> Set v
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
