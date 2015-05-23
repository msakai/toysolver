{-# OPTIONS_GHC -Wall #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.Converter.PB2SMP
-- Copyright   :  (c) Masahiro Sakai 2013
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  experimental
-- Portability :  portable
--
-----------------------------------------------------------------------------
module ToySolver.Converter.PB2SMP
  ( convert
  ) where

import Data.List
import qualified ToySolver.Data.PseudoBoolean as PBFile

convert :: Bool -> PBFile.Formula -> ShowS
convert isUnix formula =
  header .
  decls .
  showString "\n" .
  obj2 .
  showString "\n" .
  constrs .
  showString "\n" .
  actions .
  footer
  where
    nv = PBFile.pbNumVars formula

    header =
      if isUnix
      then showString "#include \"simple.h\"\nvoid ufun()\n{\n\n"
      else id
    
    footer =
      if isUnix
      then showString "\n}\n"
      else id

    actions =
      showString "solve();\n" .
      showString "x[i].val.print();\n" .
      showString "cost.val.print();\n"

    decls = showString $
      "Element i(set=\"1 .. " ++ show nv ++ "\");\n" ++
      "IntegerVariable x(type=binary, index=i);\n"

    constrs = foldr (.) id
      [ showString (showSum lhs) .
        showString op2 .
        shows rhs .
        showString ";\n"
      | (lhs, op, rhs) <- PBFile.pbConstraints formula
      , let op2 = case op of
                    PBFile.Ge -> " >= "
                    PBFile.Eq -> " == "
      ]

    showSum :: PBFile.Sum -> String
    showSum [] = "0"
    showSum xs = intercalate " + " $ map showTerm xs

    showTerm (n,ls) = intercalate "*" $ showCoeff n ++ [showLit l | l<-ls]

    showCoeff n
      | n == 1    = []
      | n < 0     = ["(" ++ show n ++ ")"]
      | otherwise = [show n]

    showLit l =
      if l < 0
      then "(1-x[" ++ show (abs l) ++ "])"
      else "x[" ++ show l ++ "]"

    obj2 =
      case PBFile.pbObjectiveFunction formula of
        Just obj' ->
          showString "Objective cost(type=minimize);\n" .
          showString "cost = " . showString (showSum obj') . showString ";\n"
        Nothing -> id
