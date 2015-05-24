{-# OPTIONS_GHC -Wall #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.Converter.PB2LSP
-- Copyright   :  (c) Masahiro Sakai 2013-2014
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  experimental
-- Portability :  portable
--
-----------------------------------------------------------------------------
module ToySolver.Converter.PB2LSP
  ( convert
  , convertWBO
  ) where

import Data.List
import qualified Data.PseudoBoolean as PBFile

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
        showString (showConstr c) .
        showString ";\n"
      | c <- PBFile.pbConstraints formula
      ]

    obj2 =
      case PBFile.pbObjectiveFunction formula of
        Just obj' -> showString "  minimize " . showString (showSum obj') . showString ";\n"
        Nothing -> id

convertWBO :: PBFile.SoftFormula -> ShowS
convertWBO softFormula =
  showString "function model() {\n" .
  decls .
  constrs .
  costDef .
  topConstr .
  showString "  minimize cost;\n" .
  showString "}\n"
  where
    nv = PBFile.wboNumVars softFormula

    decls = showString $
      "  for [i in 1.." ++ show nv ++ "] x[i] <- bool();\n"

    constrs = foldr (.) id
      [ showString "  constraint " .
        showString (showConstr c) .
        showString ";\n"
      | (Nothing, c) <- PBFile.wboConstraints softFormula
      ]

    costDef = showString "  cost <- sum(\n" . s . showString ");\n"
      where
        s = foldr (.) id . intersperse (showString ",\n") . map showString $ xs
        xs = ["    " ++ show w ++ "*!(" ++ showConstr c ++ ")" | (Just w, c) <- PBFile.wboConstraints softFormula]

    topConstr =
      case PBFile.wboTopCost softFormula of
        Nothing -> id
        Just t -> showString $ "  constraint cost <= " ++ show t ++ ";\n"

showConstr :: PBFile.Constraint -> String
showConstr (lhs, PBFile.Ge, 1) | and [c==1 | (c,_) <- lhs] =
  "or(" ++ intercalate "," (map (f . snd) lhs) ++ ")"
  where
    f [l] = showLit l
    f ls  = "and(" ++ intercalate "," (map showLit ls) ++ ")"
showConstr (lhs, op, rhs) = showSum lhs  ++ op2 ++ show rhs
  where
    op2 = case op of
            PBFile.Ge -> " >= "
            PBFile.Eq -> " == "

sum' :: [String] -> String
sum' xs = "sum(" ++ intercalate ", " xs ++ ")"

showSum :: PBFile.Sum -> String
showSum = sum' . map showTerm

showTerm :: PBFile.WeightedTerm -> String
showTerm (n,ls) = intercalate "*" $ [show n | n /= 1] ++ [showLit l | l<-ls]

showLit :: PBFile.Lit -> String
showLit l =
  if l < 0
  then "!x[" ++ show (abs l) ++ "]"
  else "x[" ++ show l ++ "]"
