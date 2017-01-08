{-# LANGUAGE OverloadedStrings #-}
module ToySolver.Data.MIP.Solution.Gurobi
  ( render
  , writeFile
  ) where

import Prelude hiding (writeFile)
import Data.Interned (unintern)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Monoid
import Data.Scientific (Scientific)
import qualified Data.Text.Lazy as TL
import Data.Text.Lazy.Builder (Builder)
import qualified Data.Text.Lazy.Builder as B
import qualified Data.Text.Lazy.Builder.Scientific as B
import qualified Data.Text.Lazy.IO as TLIO
import qualified ToySolver.Data.MIP as MIP

render :: MIP.Solution Scientific -> TL.Text
render (MIP.Solution obj vs) = B.toLazyText $ ls1 <> mconcat ls2
  where
    ls1 = case obj of
            Nothing  -> mempty
            Just val -> "# Objective value = " <> B.scientificBuilder val <> B.singleton '\n'
    ls2 = [B.fromText (unintern name) <> B.singleton ' ' <> B.scientificBuilder val <> B.singleton '\n' | (name,val) <- Map.toList vs]

writeFile :: FilePath -> MIP.Solution Scientific -> IO ()
writeFile fname sol = do
  TLIO.writeFile fname (render sol)
