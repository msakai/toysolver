{-# OPTIONS_GHC -Wall #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.Converter.PB2LSP
-- Copyright   :  (c) Masahiro Sakai 2013
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  experimental
-- Portability :  portable
--
-----------------------------------------------------------------------------
module ToySolver.Converter.PB2LSP
  ( convert
  ) where

import Data.List
import qualified ToySolver.Text.PBFile as PBFile

convert :: PBFile.Formula -> ShowS
convert formula =
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
      | (lhs, op, rhs) <- PBFile.pbConstraints formula
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
      case PBFile.pbObjectiveFunction formula of
        Just obj' -> showString "  minimize " . showString (showSum obj') . showString ";\n"
        Nothing -> id
