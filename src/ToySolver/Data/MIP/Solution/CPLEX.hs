{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.Data.MIP.Solution.CPLEX
-- Copyright   :  (c) Masahiro Sakai 2017
-- License     :  BSD-style
--
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  non-portable
--
-----------------------------------------------------------------------------
module ToySolver.Data.MIP.Solution.CPLEX
  ( Solution (..)
  , parse
  , readFile
  ) where

import Prelude hiding (readFile)
#if !MIN_VERSION_base(4,8,0)
import Control.Applicative
#endif
import Data.Default.Class
import Data.Interned
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import qualified Data.Map as Map
import Data.Maybe
import Data.Scientific (Scientific)
import Data.String
import qualified Data.Text as T
import qualified Data.Text.Lazy as TL
import qualified Text.XML as XML
import Text.XML.Cursor
import ToySolver.Data.MIP (Solution)
import qualified ToySolver.Data.MIP.Base as MIP

parseDoc :: XML.Document -> MIP.Solution Scientific
parseDoc doc = 
  MIP.Solution
  { MIP.solStatus = status
  , MIP.solObjectiveValue = obj
  , MIP.solVariables = Map.fromList vs
  }
  where
    obj :: Maybe Scientific
    obj = listToMaybe
      $  fromDocument doc
      $| element "CPLEXSolution"
      &/ element "header"
      >=> attribute "objectiveValue"
      &| (read . T.unpack)

    status :: MIP.Status
    status = head
      $  fromDocument doc
      $| element "CPLEXSolution"
      &/ element "header"
      >=> attribute "solutionStatusValue"
      &| (flip (IntMap.findWithDefault MIP.StatusUnknown) table . read . T.unpack)

    f :: Cursor -> [(MIP.Var, Scientific)]
    f x
      | XML.NodeElement e <- node x = maybeToList $ do
          let m = XML.elementAttributes e
          name <- Map.lookup "name" m
          value <- read . T.unpack <$> Map.lookup "value" m
          return (intern name, value)
      | otherwise = []
    vs = fromDocument doc
      $| element "CPLEXSolution"
      &/ element "variables"
      &/ element "variable"
      >=> f

-- https://www.ibm.com/support/knowledgecenter/en/SSSA5P_12.7.0/ilog.odms.cplex.help/refcallablelibrary/macros/Solution_status_codes.html
table :: IntMap MIP.Status
table = IntMap.fromList
  [ (1,   MIP.StatusOptimal)               -- CPX_STAT_OPTIMAL
  , (2,   MIP.StatusUnbounded)             -- CPX_STAT_UNBOUNDED
  , (3,   MIP.StatusInfeasible)            -- CPX_STAT_INFEASIBLE
  , (4,   MIP.StatusInfeasibleOrUnbounded) -- CPX_STAT_INForUNBD
  , (5,   MIP.StatusOptimal)               -- CPX_STAT_OPTIMAL_INFEAS
{-
  , (6,   ) -- CPX_STAT_NUM_BEST
  , (10,  ) -- CPX_STAT_ABORT_IT_LIM
  , (11,  ) -- CPX_STAT_ABORT_TIME_LIM
  , (12,  ) -- CPX_STAT_ABORT_OBJ_LIM
  , (13,  ) -- CPX_STAT_ABORT_USER
  , (14,  ) -- CPX_STAT_FEASIBLE_RELAXED_SUM
  , (15,  ) -- CPX_STAT_OPTIMAL_RELAXED_SUM
  , (16,  ) -- CPX_STAT_FEASIBLE_RELAXED_INF
  , (17,  ) -- CPX_STAT_OPTIMAL_RELAXED_INF
  , (18,  ) -- CPX_STAT_FEASIBLE_RELAXED_QUAD
  , (19,  ) -- CPX_STAT_OPTIMAL_RELAXED_QUAD
  , (20,  ) -- CPX_STAT_OPTIMAL_FACE_UNBOUNDED
  , (21,  ) -- CPX_STAT_ABORT_PRIM_OBJ_LIM
  , (22,  ) -- CPX_STAT_ABORT_DUAL_OBJ_LIM
  , (23,  ) -- CPX_STAT_FEASIBLE
-}
  , (24,  MIP.StatusFeasible) -- CPX_STAT_FIRSTORDER
{-
  , (25,  ) -- CPX_STAT_ABORT_DETTIME_LIM
  , (30,  ) -- CPX_STAT_CONFLICT_FEASIBLE
  , (31,  ) -- CPX_STAT_CONFLICT_MINIMAL
  , (32,  ) -- CPX_STAT_CONFLICT_ABORT_CONTRADICTION
  , (33,  ) -- CPX_STAT_CONFLICT_ABORT_TIME_LIM
  , (34,  ) -- CPX_STAT_CONFLICT_ABORT_IT_LIM
  , (35,  ) -- CPX_STAT_CONFLICT_ABORT_NODE_LIM
  , (36,  ) -- CPX_STAT_CONFLICT_ABORT_OBJ_LIM
  , (37,  ) -- CPX_STAT_CONFLICT_ABORT_MEM_LIM
  , (38,  ) -- CPX_STAT_CONFLICT_ABORT_USER
  , (39,  ) -- CPX_STAT_CONFLICT_ABORT_DETTIME_LIM
-}
  , (40,  MIP.StatusInfeasibleOrUnbounded) -- CPX_STAT_BENDERS_MASTER_UNBOUNDED
--  , (41,  ) -- CPX_STAT_BENDERS_NUM_BEST
  , (101, MIP.StatusOptimal)               -- CPXMIP_OPTIMAL
  , (102, MIP.StatusOptimal)               -- CPXMIP_OPTIMAL_TOL
  , (103, MIP.StatusInfeasible)            -- CPXMIP_INFEASIBLE
--  , (104, ) -- CPXMIP_SOL_LIM
  , (105, MIP.StatusFeasible)              -- CPXMIP_NODE_LIM_FEAS
--  , (106, ) -- CPXMIP_NODE_LIM_INFEAS
  , (107, MIP.StatusFeasible)              -- CPXMIP_TIME_LIM_FEAS
--  , (108, ) -- CPXMIP_TIME_LIM_INFEAS
  , (109, MIP.StatusFeasible)              -- CPXMIP_FAIL_FEAS
--  , (110, ) -- CPXMIP_FAIL_INFEAS
  , (111, MIP.StatusFeasible)              -- CPXMIP_MEM_LIM_FEAS
--  , (112, ) -- CPXMIP_MEM_LIM_INFEAS
  , (113, MIP.StatusFeasible)              -- CPXMIP_ABORT_FEAS
--  , (114, ) -- CPXMIP_ABORT_INFEAS
  , (115, MIP.StatusOptimal)               -- CPXMIP_OPTIMAL_INFEAS
  , (116, MIP.StatusFeasible)              -- CPXMIP_FAIL_FEAS_NO_TREE
--  , (117, ) -- CPXMIP_FAIL_INFEAS_NO_TREE
  , (118, MIP.StatusUnbounded)             -- CPXMIP_UNBOUNDED
  , (119, MIP.StatusInfeasibleOrUnbounded) -- CPXMIP_INForUNBD
{-
  , (120, ) -- CPXMIP_FEASIBLE_RELAXED_SUM
  , (121, ) -- CPXMIP_OPTIMAL_RELAXED_SUM
  , (122, ) -- CPXMIP_FEASIBLE_RELAXED_INF
  , (123, ) -- CPXMIP_OPTIMAL_RELAXED_INF
  , (124, ) -- CPXMIP_FEASIBLE_RELAXED_QUAD
  , (125, ) -- CPXMIP_OPTIMAL_RELAXED_QUAD
  , (126, ) -- CPXMIP_ABORT_RELAXED
-}
  , (127, MIP.StatusFeasible)              -- CPXMIP_FEASIBLE
--  , (128, ) -- CPXMIP_POPULATESOL_LIM
  , (129, MIP.StatusOptimal)               -- CPXMIP_OPTIMAL_POPULATED
  , (130, MIP.StatusOptimal)               -- CPXMIP_OPTIMAL_POPULATED_TOL
  , (131, MIP.StatusFeasible)              -- CPXMIP_DETTIME_LIM_FEAS
--  , (132, ) -- CPXMIP_DETTIME_LIM_INFEAS
  , (133, MIP.StatusInfeasibleOrUnbounded) -- CPXMIP_ABORT_RELAXATION_UNBOUNDED
  ]

parse :: TL.Text -> MIP.Solution Scientific
parse t = parseDoc $ XML.parseText_ def t

readFile :: FilePath -> IO (MIP.Solution Scientific)
readFile fname = parseDoc <$> XML.readFile def (fromString fname)

