{-# OPTIONS_GHC -Wall #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.Data.Polynomial
-- Copyright   :  (c) Masahiro Sakai 2012-2013
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  portable
--
-- Polynomials
--
-- References:
--
-- * Monomial order <http://en.wikipedia.org/wiki/Monomial_order>
--
-- * Polynomial class for Ruby <http://www.math.kobe-u.ac.jp/~kodama/tips-RubyPoly.html>
--
-- * constructive-algebra package <http://hackage.haskell.org/package/constructive-algebra>
-- 
-----------------------------------------------------------------------------
module ToySolver.Data.Polynomial
  (
  -- * Polynomial type
    Polynomial

  -- * Conversion
  , Var (..)
  , constant
  , terms
  , fromTerms
  , coeffMap
  , fromCoeffMap
  , fromTerm

  -- * Query
  , Degree (..)
  , Vars (..)
  , lt
  , lc
  , lm
  , coeff
  , lookupCoeff
  , isPrimitive

  -- * Operations
  , Factor (..)
  , SQFree (..)
  , ContPP (..)
  , deriv
  , integral
  , eval
  , subst
  , mapCoeff
  , toMonic
  , toUPolynomialOf
  , divModMP
  , reduce

  -- * Univariate polynomials
  , UPolynomial
  , X (..)
  , UTerm
  , UMonomial
  , div
  , mod
  , divMod
  , divides
  , gcd
  , lcm
  , exgcd
  , pdivMod
  , pdiv
  , pmod
  , gcd'
  , isRootOf
  , isSquareFree
  , nat
  , eisensteinsCriterion

  -- * Term
  , Term
  , tdeg
  , tscale
  , tmult
  , tdivides
  , tdiv
  , tderiv
  , tintegral

  -- * Monic monomial
  , Monomial
  , mone
  , mfromIndices
  , mfromIndicesMap
  , mindices
  , mindicesMap
  , mmult
  , mpow
  , mdivides
  , mdiv
  , mderiv
  , mintegral
  , mlcm
  , mgcd
  , mcoprime

  -- * Monomial order
  , MonomialOrder
  , lex
  , revlex
  , grlex
  , grevlex

  -- * Pretty Printing
  , PrintOptions (..)
  , prettyPrint
  , PrettyCoeff (..)
  , PrettyVar (..)
  ) where

import Prelude hiding (lex, div, mod, divMod, gcd, lcm)
import ToySolver.Data.Polynomial.Base
import ToySolver.Data.Polynomial.Factorization.FiniteField ()
import ToySolver.Data.Polynomial.Factorization.Integer ()
import ToySolver.Data.Polynomial.Factorization.Rational ()
