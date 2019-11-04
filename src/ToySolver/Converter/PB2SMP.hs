{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE OverloadedStrings #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.Converter.PB2SMP
-- Copyright   :  (c) Masahiro Sakai 2013,2016
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  experimental
-- Portability :  non-portable
--
-----------------------------------------------------------------------------
module ToySolver.Converter.PB2SMP
  ( pb2smp
  ) where

import Data.ByteString.Builder
import Data.List
#if !MIN_VERSION_base(4,11,0)
import Data.Monoid
#endif
import qualified Data.PseudoBoolean as PBFile

pb2smp :: Bool -> PBFile.Formula -> Builder
pb2smp isUnix formula =
  header <>
  decls <>
  char7 '\n' <>
  obj2 <>
  char7 '\n' <>
  constrs <>
  char7 '\n' <>
  actions <>
  footer
  where
    nv = PBFile.pbNumVars formula

    header =
      if isUnix
      then byteString "#include \"simple.h\"\nvoid ufun()\n{\n\n"
      else mempty
    
    footer =
      if isUnix
      then "\n}\n"
      else mempty

    actions = byteString $
      "solve();\n" <>
      "x[i].val.print();\n" <>
      "cost.val.print();\n"

    decls =
      byteString "Element i(set=\"1 .. " <> intDec nv <>
      byteString "\");\nIntegerVariable x(type=binary, index=i);\n"

    constrs = mconcat
      [ showSum lhs <>
        op2 <>
        integerDec rhs <>
        ";\n"
      | (lhs, op, rhs) <- PBFile.pbConstraints formula
      , let op2 = case op of
                    PBFile.Ge -> " >= "
                    PBFile.Eq -> " == "
      ]

    showSum :: PBFile.Sum -> Builder
    showSum [] = char7 '0'
    showSum xs = mconcat $ intersperse " + " $ map showTerm xs

    showTerm (n,ls) = mconcat $ intersperse (char7 '*') $ showCoeff n ++ [showLit l | l<-ls]

    showCoeff n
      | n == 1    = []
      | n < 0     = [char7 '(' <> integerDec n <> char7 ')']
      | otherwise = [integerDec n]

    showLit l =
      if l < 0
      then "(1-x[" <> intDec (abs l) <> "])"
      else "x[" <> intDec l <> "]"

    obj2 =
      case PBFile.pbObjectiveFunction formula of
        Just obj' ->
          byteString "Objective cost(type=minimize);\ncost = " <> showSum obj' <> ";\n"
        Nothing -> mempty
