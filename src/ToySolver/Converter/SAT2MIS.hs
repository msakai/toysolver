{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE OverloadedStrings #-}
module ToySolver.Converter.SAT2MIS
  (
  -- * SAT to independent set problem conversion
    satToIS
  , SAT2ISInfo

  -- * 3-SAT to independent set problem conversion
  , sat3ToIS
  , SAT3ToISInfo

  -- * Maximum independent problem to MaxSAT/PB problem conversion
  , is2pb
  , mis2MaxSAT
  , IS2SATInfo
  ) where

import Control.Arrow ((&&&))
import Control.Monad
import Control.Monad.ST
import qualified Data.Aeson as J
import Data.Aeson ((.=), (.:))
import Data.Array.IArray
import Data.Array.ST
import Data.Array.Unboxed
import qualified Data.IntMap as IntMap
import qualified Data.IntSet as IntSet
import Data.IntSet (IntSet)
import Data.Maybe
import Data.STRef

import qualified Data.PseudoBoolean as PBFile

import ToySolver.Converter.Base
import ToySolver.Converter.SAT2KSAT
import qualified ToySolver.FileFormat.CNF as CNF
import ToySolver.Graph.Base
import ToySolver.Internal.JSON
import ToySolver.SAT.Internal.JSON
import ToySolver.SAT.Store.CNF
import ToySolver.SAT.Store.PB
import qualified ToySolver.SAT.Types as SAT

-- ------------------------------------------------------------------------

satToIS :: CNF.CNF -> ((Graph, Int), SAT2ISInfo)
satToIS x = (x2, (ComposedTransformer info1 info2))
  where
    (x1, info1) = sat2ksat 3 x
    (x2, info2) = sat3ToIS x1

type SAT2ISInfo = ComposedTransformer SAT2KSATInfo SAT3ToISInfo

-- ------------------------------------------------------------------------

sat3ToIS :: CNF.CNF -> ((Graph, Int), SAT3ToISInfo)
sat3ToIS cnf = runST $ do
  nRef <- newSTRef 0
  litToNodesRef <- newSTRef IntMap.empty
  nodeToLitRef <- newSTRef []
  let newNode lit = do
        n <- readSTRef nRef
        writeSTRef nRef $! n + 1
        modifySTRef' litToNodesRef (IntMap.alter (Just . (n :) . fromMaybe []) lit)
        modifySTRef nodeToLitRef (lit :)
        return n

  clusters <- forM (CNF.cnfClauses cnf) $ \clause -> do
    mapM newNode (SAT.unpackClause clause)

  litToNodes <- readSTRef litToNodesRef
  let es = concat $
        [ [(node1, node2, ()) | (node1, node2) <- pairs nodes] | nodes <- clusters ] ++
        [ [(node1, node2, ()) | node1 <- nodes1, node2 <- nodes2]
        | (lit, nodes1) <- IntMap.toList litToNodes
        , let nodes2 = IntMap.findWithDefault [] (- lit) litToNodes
        ]

  n <- readSTRef nRef
  let g = graphFromUnorderedEdges n es

  xs <- readSTRef nodeToLitRef
  let nodeToLit = runSTUArray $ do
        a <- newArray_ (0,n-1)
        forM_ (zip [n-1,n-2..] xs) $ \(i, lit) -> do
          writeArray a i lit
        return a

  return ((g, CNF.cnfNumClauses cnf), SAT3ToISInfo (CNF.cnfNumVars cnf) clusters nodeToLit)


data SAT3ToISInfo = SAT3ToISInfo Int [[Int]] (UArray Int SAT.Lit)
  deriving (Eq, Show)
-- Note that array <0.5.4.0 did not provided Read instance of UArray

instance Transformer SAT3ToISInfo where
  type Source SAT3ToISInfo = SAT.Model
  type Target SAT3ToISInfo = IntSet

instance ForwardTransformer SAT3ToISInfo where
  transformForward (SAT3ToISInfo _nv clusters nodeToLit) m = IntSet.fromList $ do
    nodes <- clusters
    let xs = [node | node <- nodes, SAT.evalLit m (nodeToLit ! node)]
    if null xs then
      error "not a model"
    else
      return (head xs)

instance BackwardTransformer SAT3ToISInfo where
  transformBackward (SAT3ToISInfo nv _clusters nodeToLit) indep_set = runSTUArray $ do
    a <- newArray (1, nv) False
    forM_ (IntSet.toList lits) $ \lit -> do
      writeArray a (SAT.litVar lit) (SAT.litPolarity lit)
    return a
    where
      lits = IntSet.map (nodeToLit !) indep_set

instance J.ToJSON SAT3ToISInfo where
  toJSON (SAT3ToISInfo nv clusters nodeToLit) =
    J.object
    [ "type" .= ("SAT3ToISInfo" :: J.Value)
    , "num_original_variables" .= nv
    , "clusters" .= clusters
    , "node_to_literal" .= (J.toJSONList
        [ (node, jLit lit)
        | (node, lit) <- assocs nodeToLit
        ])
    ]

instance J.FromJSON SAT3ToISInfo where
  parseJSON =
    withTypedObject "SAT3ToISInfo" $ \obj -> do
      xs <- obj .: "node_to_literal"
      SAT3ToISInfo
        <$> obj .: "num_original_variables"
        <*> obj .: "clusters"
        <*> (if null xs then pure (array (0, -1) []) else (array ((minimum &&& maximum) (map fst xs)) <$> mapM f xs))
    where
      f (node, val) = do
        lit <- parseLit val
        pure (node, lit)

-- ------------------------------------------------------------------------

is2pb :: (Graph, Int) -> (PBFile.Formula, IS2SATInfo)
is2pb (g, k) = runST $ do
  let (lb, ub) = bounds g
  db <- newPBStore
  vs <- SAT.newVars db (rangeSize (bounds g))
  forM_ (graphToUnorderedEdges g) $ \(node1, node2, _) -> do
    SAT.addClause db [- (node1 - lb + 1), - (node2 - lb + 1)]
  SAT.addPBAtLeast db [(1,v) | v <- vs] (fromIntegral k)
  formula <- getPBFormula db
  return
    ( formula
    , IS2SATInfo (lb, ub)
    )

mis2MaxSAT :: Graph -> (CNF.WCNF, IS2SATInfo)
mis2MaxSAT g = runST $ do
  let (lb,ub) = bounds g
      n = ub - lb + 1
  db <- newCNFStore
  vs <- SAT.newVars db n
  forM_ (graphToUnorderedEdges g) $ \(node1, node2, _) -> do
    SAT.addClause db [- (node1 - lb + 1), - (node2 - lb + 1)]
  cnf <- getCNFFormula db
  let top = fromIntegral n + 1
  return
    ( CNF.WCNF
      { CNF.wcnfNumVars = CNF.cnfNumVars cnf
      , CNF.wcnfNumClauses = CNF.cnfNumClauses cnf + n
      , CNF.wcnfTopCost = top
      , CNF.wcnfClauses =
          [(top, clause) | clause <- CNF.cnfClauses cnf] ++
          [(1, SAT.packClause [v]) | v <- vs]
      }
    , IS2SATInfo (lb,ub)
    )

newtype IS2SATInfo = IS2SATInfo (Int, Int)
  deriving (Eq, Show, Read)

instance Transformer IS2SATInfo where
  type Source IS2SATInfo = IntSet
  type Target IS2SATInfo = SAT.Model

instance ForwardTransformer IS2SATInfo where
  transformForward (IS2SATInfo (lb, ub)) indep_set = runSTUArray $ do
    let n = ub - lb + 1
    a <- newArray (1, n) False
    forM_ (IntSet.toList indep_set) $ \node -> do
      writeArray a (node - lb + 1) True
    return a

instance BackwardTransformer IS2SATInfo where
  transformBackward (IS2SATInfo (lb, ub)) m =
    IntSet.fromList [node | node <- range (lb, ub), SAT.evalVar m (node - lb + 1)]

instance ObjValueTransformer IS2SATInfo where
  type SourceObjValue IS2SATInfo = Int
  type TargetObjValue IS2SATInfo = Integer

instance ObjValueForwardTransformer IS2SATInfo where
  transformObjValueForward (IS2SATInfo (lb, ub)) k = fromIntegral $ (ub - lb + 1) - k

instance ObjValueBackwardTransformer IS2SATInfo where
  transformObjValueBackward (IS2SATInfo (lb, ub)) k = (ub - lb + 1) - fromIntegral k

instance J.ToJSON IS2SATInfo where
  toJSON (IS2SATInfo (lb, ub)) =
    J.object
    [ "type" .= ("IS2SATInfo" :: J.Value)
    , "node_bounds" .= (lb, ub)
    ]

instance J.FromJSON IS2SATInfo where
  parseJSON =
    withTypedObject "IS2SATInfo" $ \obj ->
      IS2SATInfo <$> obj .: "node_bounds"

-- ------------------------------------------------------------------------

pairs :: [a] -> [(a,a)]
pairs [] = []
pairs (x:xs) = [(x,x2) | x2 <- xs] ++ pairs xs

-- ------------------------------------------------------------------------
