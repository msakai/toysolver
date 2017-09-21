module ToySolver.SAT.Enum where

import Conduit
import Control.Monad
import Data.Array.IArray
import ToySolver.SAT as SAT

models :: SAT.Solver -> Source IO SAT.Model
models solver = loop
  where
    loop = do
      ret <- liftIO $ SAT.solve solver
      when ret $ do
        m <- liftIO $ SAT.getModel solver
        yield m
        liftIO $ SAT.addClause solver [SAT.literal v (not b) | (v,b) <- assocs m]
        loop
