{-# OPTIONS_GHC -Wall #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.Converter.PBSetObj
-- Copyright   :  (c) Masahiro Sakai 2013
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  experimental
-- Portability :  portable
--
-----------------------------------------------------------------------------
module ToySolver.Converter.PBSetObj
  ( ObjType (..)
  , setObj
  ) where

import qualified Data.PseudoBoolean as PBFile
import ToySolver.Converter.ObjType

setObj :: ObjType -> PBFile.Formula -> PBFile.Formula
setObj objType formula = formula{ PBFile.pbObjectiveFunction = Just obj2 }
  where
    obj2 = genObj objType formula

genObj :: ObjType -> PBFile.Formula -> PBFile.Sum
genObj objType formula =
  case objType of
    ObjNone    -> []
    ObjMaxOne  -> [(1,[-v]) | v <- [1 .. PBFile.pbNumVars formula]] -- minimize false literals
    ObjMaxZero -> [(1,[ v]) | v <- [1 .. PBFile.pbNumVars formula]] -- minimize true literals
