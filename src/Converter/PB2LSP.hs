{-# OPTIONS_GHC -Wall #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Converter.PB2LSP
-- Copyright   :  (c) Masahiro Sakai 2013
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  experimental
-- Portability :  portable
--
-----------------------------------------------------------------------------
module Converter.PB2LSP
  ( ObjType (..)
  , convert
  ) where

import Data.List
import qualified Text.PBFile as PBFile
import Converter.ObjType

convert :: ObjType -> PBFile.Formula -> ShowS
convert objType formula@(obj, cs) =
  showString "function model() {\n" .
  decls .
  constrs .
  obj2 .
  showString "}\n"
  where
    nv = PBFile.pbNumVars formula

    decls = showString $
      "  for [i in 1.." ++ show nv ++ "] x[i] <- bool();\n"

    constrs = foldr (.) id
      [ showString "  constraint " .
        showString (showSum lhs) .
        showString op2 .
        shows rhs .
        showString ";\n"
      | (lhs, op, rhs) <- cs
      , let op2 = case op of
                    PBFile.Ge -> " >= "
                    PBFile.Eq -> " == "
      ]

    sum' :: [String] -> String
    sum' xs = "sum(" ++ intercalate ", " xs ++ ")"

    showSum = sum' . map showTerm

    showTerm (n,ls) = intercalate "*" $ [show n | n /= 1] ++ [showLit l | l<-ls]

    showLit l =
      if l < 0
      then "!x[" ++ show (abs l) ++ "]"
      else "x[" ++ show l ++ "]"

    obj2 =
      case obj of
        Just obj' ->
          showString "  minimize " . showString (showSum obj') . showString ";\n"
        Nothing ->
          case objType of
            ObjNone    -> id
            ObjMaxOne  ->
              showString "maximize " . showString s . showString ";\n"
            ObjMaxZero  ->
              showString "minimize " . showString s . showString ";\n"
            where
              s = sum' [showLit x | x<-[1..nv]]
