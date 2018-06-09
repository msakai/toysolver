{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE OverloadedStrings #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.Converter.PB2LSP
-- Copyright   :  (c) Masahiro Sakai 2013-2014,2016
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  experimental
-- Portability :  non-portable (OverloadedStrings)
--
-----------------------------------------------------------------------------
module ToySolver.Converter.PB2LSP
  ( pb2lsp
  , wbo2lsp
  ) where

import Data.ByteString.Builder
import Data.List
import Data.Monoid
import qualified Data.PseudoBoolean as PBFile

pb2lsp :: PBFile.Formula -> Builder
pb2lsp formula =
  byteString "function model() {\n" <>
  decls <>
  constrs <>
  obj2 <>
  "}\n"
  where
    nv = PBFile.pbNumVars formula

    decls = byteString "  for [i in 1.." <> intDec nv <> byteString "] x[i] <- bool();\n"

    constrs = mconcat
      [ byteString "  constraint " <>
        showConstr c <>
        ";\n"
      | c <- PBFile.pbConstraints formula
      ]

    obj2 =
      case PBFile.pbObjectiveFunction formula of
        Just obj' -> byteString "  minimize " <> showSum obj' <> ";\n"
        Nothing -> mempty

wbo2lsp :: PBFile.SoftFormula -> Builder
wbo2lsp softFormula =
  byteString "function model() {\n" <>
  decls <>
  constrs <>
  costDef <>
  topConstr <>
  byteString "  minimize cost;\n}\n"
  where
    nv = PBFile.wboNumVars softFormula

    decls = byteString "  for [i in 1.." <> intDec nv <> byteString "] x[i] <- bool();\n"

    constrs = mconcat
      [ byteString "  constraint " <>
        showConstr c <>
        ";\n"
      | (Nothing, c) <- PBFile.wboConstraints softFormula
      ]

    costDef = byteString "  cost <- sum(\n" <> s <> ");\n"
      where
        s = mconcat . intersperse (",\n") $ xs
        xs = ["    " <> integerDec w <> "*!(" <> showConstr c <> ")"
             | (Just w, c) <- PBFile.wboConstraints softFormula]

    topConstr =
      case PBFile.wboTopCost softFormula of
        Nothing -> mempty
        Just t -> byteString "  constraint cost <= " <> integerDec t <> ";\n"

showConstr :: PBFile.Constraint -> Builder
showConstr (lhs, PBFile.Ge, 1) | and [c==1 | (c,_) <- lhs] =
  "or(" <> mconcat (intersperse "," (map (f . snd) lhs)) <> ")"
  where
    f [l] = showLit l
    f ls  = "and(" <> mconcat (intersperse "," (map showLit ls)) <> ")"
showConstr (lhs, op, rhs) = showSum lhs  <> op2 <> integerDec rhs
  where
    op2 = case op of
            PBFile.Ge -> " >= "
            PBFile.Eq -> " == "

sum' :: [Builder] -> Builder
sum' xs = "sum(" <> mconcat (intersperse ", " xs) <> ")"

showSum :: PBFile.Sum -> Builder
showSum = sum' . map showTerm

showTerm :: PBFile.WeightedTerm -> Builder
showTerm (n,ls) = mconcat $ intersperse "*" $ [integerDec n | n /= 1] ++ [showLit l | l<-ls]

showLit :: PBFile.Lit -> Builder
showLit l =
  if l < 0
  then "!x[" <> intDec (abs l) <> "]"
  else "x[" <> intDec l <> "]"
