module Text.GurobiSol
  ( Model
  , render
  ) where

import Data.Map (Map)
import qualified Data.Map as Map
import Data.Ratio

type Model = Map String Double

render :: Model -> Maybe Double -> String
render m obj = unlines $ ls1 ++ ls2
  where
    ls1 = case obj of
            Nothing  -> []
            Just val -> ["# Objective value = " ++ show val]
    ls2 = [name ++ " " ++ show val | (name,val) <- Map.toList m]
