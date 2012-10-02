-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Polyhedron
-- Copyright   :  (c) Masahiro Sakai 2012
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  portable
--
-- Affine subspaces that are characterized by a set of linear (in)equalities.
-- 
-----------------------------------------------------------------------------
module Data.Polyhedron
  ( Polyhedron
  , univ
  , empty
  , intersection
  , fromConstraints
  , toConstraints
  ) where

import Data.List
import Data.Ratio
import qualified Data.IntSet as IS
import qualified Data.Map as Map
import Prelude hiding (null)

import qualified Data.Interval as Interval
import Data.Expr (Variables (..))
import Data.ArithRel (RelOp (..), flipOp)
import qualified Data.LA as LA
import Data.Linear
import Data.Lattice

type ExprR = LA.Expr Rational
type ExprZ = LA.Expr Integer

type AtomR = LA.Atom Rational

type IntervalR = Interval.Interval Rational

-- | Intersection of half-spaces
data Polyhedron
  = Polyhedron (Map.Map ExprZ IntervalR)
  | Empty
  deriving (Eq)

instance Variables Polyhedron where
  vars (Polyhedron m) = IS.unions [vars e | e <- Map.keys m]
  vars Empty = IS.empty

instance Lattice Polyhedron where
  top    = univ
  bottom = empty
  meet   = intersection
  join Empty b = b
  join a Empty = a
  join (Polyhedron m1) (Polyhedron m2) =
    normalize $ Polyhedron (Map.intersectionWith Interval.join m1 m2)

normalize :: Polyhedron -> Polyhedron
normalize (Polyhedron m) | any Interval.null (Map.elems m) = Empty
normalize p = p

-- | universe
univ :: Polyhedron
univ = Polyhedron Map.empty

-- | empty space
empty :: Polyhedron
empty = Empty

-- | intersection of 
intersection :: Polyhedron -> Polyhedron -> Polyhedron
intersection (Polyhedron m1) (Polyhedron m2) =
  normalize $ Polyhedron (Map.unionWith Interval.intersection m1 m2)
intersection _ _ = Empty

-- | Create a set of 'Polyhedron's that are characterized by a given
-- set of linear (in)equalities.
fromConstraints :: [AtomR] -> [Polyhedron]
fromConstraints cs = 
  map (foldl' intersection univ) $ transpose $ map fromAtom cs

fromAtom :: AtomR  -> [Polyhedron]
fromAtom (LA.Atom lhs NEq rhs) =
  fromAtom (LA.Atom lhs Lt rhs) ++ fromAtom (LA.Atom lhs Gt rhs)
fromAtom (LA.Atom lhs op rhs) =
  case LA.extract LA.unitVar (lhs .-. rhs) of
    (c, e1) ->
      case toRat e1 of
        (lhs1, d) ->
          let rhs1 = - c * fromIntegral d
              (lhs2,op2,rhs2) =
                if p lhs1
                then (lnegate lhs1, flipOp op, - rhs1)
                else (lhs1, op, rhs1)
              ival =
                case op of
                  Lt  -> Interval.interval Nothing (Just (False, rhs2))
                  Le  -> Interval.interval Nothing (Just (True, rhs2))
                  Ge  -> Interval.interval (Just (True, rhs2)) Nothing
                  Gt  -> Interval.interval (Just (False, rhs2)) Nothing
                  Eql -> Interval.singleton rhs2
                  NEq -> error "should not happen"
          in filter (Empty /=) [normalize $ Polyhedron (Map.singleton lhs2 ival)]

-- | Convert the polyhedron to a list of linear (in)equalities.
toConstraints :: Polyhedron -> [AtomR]
toConstraints Empty = [LA.Atom (LA.constant 0) Lt (LA.constant 0)]
toConstraints (Polyhedron m) = do
  (e, ival) <- Map.toList m
  let e' = LA.mapCoeff fromIntegral e
      xs = case Interval.lowerBound ival of
             Nothing -> []
             Just (True,c)  -> [LA.Atom (LA.constant c) Le e']
             Just (False,c) -> [LA.Atom (LA.constant c) Lt e']
      ys = case Interval.upperBound ival of
             Nothing -> []
             Just (True,c)  -> [LA.Atom e' Le (LA.constant c)]
             Just (False,c) -> [LA.Atom e' Lt (LA.constant c)]
  xs ++ ys

p :: ExprZ -> Bool
p e =
  case LA.terms e of
    (c,_):_ | c < 0 -> True
    _ -> False

-- | (t,c) represents t/c, and c must be >0.
type Rat = (ExprZ, Integer)

toRat :: ExprR -> Rat
toRat e = (LA.mapCoeff f e, d)
  where
    f :: Rational -> Integer
    f x = round (x * fromIntegral d)
    d :: Integer
    d = foldl' lcm 1 [denominator c | (c,_) <- LA.terms e]
