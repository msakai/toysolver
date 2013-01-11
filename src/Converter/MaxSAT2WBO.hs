{-# OPTIONS_GHC -Wall #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Converter.MaxSAT2WBO
-- Copyright   :  (c) Masahiro Sakai 2013
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  experimental
-- Portability :  portable
--
-----------------------------------------------------------------------------
module Converter.MaxSAT2WBO
  ( convert
  ) where

import qualified Text.PBFile as PBFile
import qualified Text.MaxSAT as MaxSAT

convert :: MaxSAT.WCNF -> PBFile.SoftFormula
convert
  MaxSAT.WCNF
  { MaxSAT.topCost = top
  , MaxSAT.clauses = cs
  } = (Nothing, map f cs)
  where
    f (w,ls)
     | w>=top    = (Nothing, p) -- hard constraint
     | otherwise = (Just w, p)  -- soft constraint
     where
       p = ([(1,[l]) | l <- ls], PBFile.Ge, 1)

