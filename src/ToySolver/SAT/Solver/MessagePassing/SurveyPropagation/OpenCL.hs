{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_HADDOCK show-extensions #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.SAT.Solver.MessagePassing.SurveyPropagation.OpenCL
-- Copyright   :  (c) Masahiro Sakai 2016
-- License     :  BSD-style
--
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  non-portable
--
-- References:
--
-- * Alfredo Braunstein, Marc Mézard and Riccardo Zecchina.
--   Survey Propagation: An Algorithm for Satisfiability,
--   <http://arxiv.org/abs/cs/0212002>
--
-- * Corrie Scalisi. Visualizing Survey Propagation in 3-SAT Factor Graphs,
--   <http://classes.soe.ucsc.edu/cmps290c/Winter06/proj/corriereport.pdf>.
--
-----------------------------------------------------------------------------
module ToySolver.SAT.Solver.MessagePassing.SurveyPropagation.OpenCL
  (
  -- * The Solver type
    Solver
  , newSolver
  , deleteSolver

  -- * Problem information
  , getNVars
  , getNConstraints

  -- * Parameters
  , getTolerance
  , setTolerance
  , getIterationLimit
  , setIterationLimit

  -- * Computing marginal distributions
  , initializeRandom
  , initializeRandomDirichlet
  , propagate
  , getVarProb

  -- * Solving
  , fixLit
  , unfixLit
  ) where

import Control.Exception
import Control.Loop
import Control.Monad
import Control.Parallel.OpenCL
import Data.Bits
import Data.Int
import Data.IORef
import qualified Data.Vector as V
import qualified Data.Vector.Mutable as VM
import qualified Data.Vector.Storable as VS
import qualified Data.Vector.Storable.Mutable as VSM
import Data.Vector.Generic ((!))
import qualified Data.Vector.Generic as VG
import qualified Data.Vector.Generic.Mutable as VGM
import Foreign( castPtr, nullPtr, sizeOf )
import Foreign.C.Types( CFloat )
import Language.Haskell.TH (runIO, litE, stringL)
import Language.Haskell.TH.Syntax (addDependentFile)
import qualified Numeric.Log as L
import System.IO
import qualified System.Random.MWC as Rand
import qualified System.Random.MWC.Distributions as Rand
import Text.Printf

import qualified ToySolver.SAT.Types as SAT

data Solver
  = Solver
  { svOutputMessage :: !(String -> IO ())

  , svContext :: !CLContext
  , svDevice  :: !CLDeviceID
  , svQueue   :: !CLCommandQueue
  , svUpdateEdgeProb   :: !CLKernel
  , svUpdateEdgeSurvey :: !CLKernel
  , svComputeVarProb   :: !CLKernel

  , svVarEdges       :: !(VSM.IOVector CLint)
  , svVarEdgesWeight :: !(VSM.IOVector CFloat)
  , svVarOffset      :: !(VSM.IOVector CLint)
  , svVarLength      :: !(VSM.IOVector CLint)
  , svVarFixed       :: !(VSM.IOVector Int8)
  , svVarProb        :: !(VSM.IOVector (L.Log CFloat))
  , svClauseOffset   :: !(VSM.IOVector CLint)
  , svClauseLength   :: !(VSM.IOVector CLint)
  , svEdgeSurvey     :: !(VSM.IOVector (L.Log CFloat)) -- η_{a → i}
  , svEdgeProbU      :: !(VSM.IOVector (L.Log CFloat)) -- Π^u_{i → a} / (Π^u_{i → a} + Π^s_{i → a} + Π^0_{i → a})

  , svTolRef :: !(IORef Double)
  , svIterLimRef :: !(IORef (Maybe Int))
  }

newSolver :: (String -> IO ()) -> CLContext -> CLDeviceID -> Int -> [(Double, SAT.PackedClause)] -> IO Solver
newSolver outputMessage context dev nv clauses = do
  _ <- clRetainContext context
  queue <- clCreateCommandQueue context dev []

  let num_clauses = length clauses
      num_edges = sum [VG.length c | (_,c) <- clauses]

  (varEdgesTmp :: VM.IOVector [(Int,Bool,Double)]) <- VGM.replicate nv []
  clauseOffset <- VGM.new num_clauses
  clauseLength <- VGM.new num_clauses

  ref <- newIORef 0
  forM_ (zip [0..] clauses) $ \(i,(w,c)) -> do
    VGM.write clauseOffset i =<< liftM fromIntegral (readIORef ref)
    VGM.write clauseLength i (fromIntegral (VG.length c))
    forM_ (SAT.unpackClause c) $ \lit -> do
      e <- readIORef ref
      modifyIORef' ref (+1)
      VGM.modify varEdgesTmp ((e,lit>0,w) :) (abs lit - 1)

  varOffset <- VGM.new nv
  varLength <- VGM.new nv
  varFixed  <- VGM.new nv
  varEdges <- VGM.new num_edges
  varEdgesWeight   <- VGM.new num_edges
  let loop !i !offset
        | i >= nv   = return ()
        | otherwise = do
            xs <- VGM.read (varEdgesTmp) i
            let len = length xs
            VGM.write varOffset i (fromIntegral offset)
            VGM.write varLength i (fromIntegral len)
            VGM.write varFixed i 0
            forM_ (zip [offset..] (reverse xs)) $ \(j, (e,polarity,w)) -> do
              VGM.write varEdges j $ (fromIntegral e `shiftL` 1) .|. (if polarity then 1 else 0)
              VGM.write varEdgesWeight j (realToFrac w)
            loop (i+1) (offset + len)
  loop 0 0

  -- Initialize all surveys with non-zero values.
  -- If we initialize to zero, following trivial solution exists:
  --
  -- η_{a→i} = 0 for all i and a.
  --
  -- Π^0_{i→a} = 1, Π^u_{i→a} = Π^s_{i→a} = 0 for all i and a,
  --
  -- \^{Π}^{0}_i = 1, \^{Π}^{+}_i = \^{Π}^{-}_i = 0
  --
  edgeSurvey  <- VGM.replicate num_edges (L.Exp (log 0.5))
  edgeProbU   <- VGM.new num_edges

  varProb <- VGM.new (nv*2)

  tolRef <- newIORef 0.01
  maxIterRef <- newIORef (Just 1000)

  -- Compile
  let byteSize :: forall a. VSM.Storable a => VSM.IOVector a -> Int
      byteSize v = VGM.length v * sizeOf (undefined :: a)
  (maxConstantBufferSize :: Int) <- fromIntegral <$> clGetDeviceMaxConstantBufferSize dev
  let reqConstantBufferSize =
        byteSize varEdges + byteSize varEdgesWeight +
        byteSize varOffset + byteSize varLength +
        byteSize clauseOffset + byteSize clauseLength
  let flags =
        ["-DUSE_CONSTANT_BUFFER" | maxConstantBufferSize >= reqConstantBufferSize]
  -- programSource <- openBinaryFile "sp.cl" ReadMode >>= hGetContents
  let programSource = $(runIO (do{ h <- openFile "src/ToySolver/SAT/Solver/MessagePassing/SurveyPropagation/sp.cl" ReadMode; hSetEncoding h utf8; hGetContents h }) >>= \s -> addDependentFile "src/ToySolver/SAT/Solver/MessagePassing/SurveyPropagation/sp.cl" >> litE (stringL s))
  outputMessage $ "Compiling kernels with options: " ++ unwords flags
  program <- clCreateProgramWithSource context programSource
  finally (clBuildProgram program [dev] (unwords flags))
          (outputMessage =<< clGetProgramBuildLog program dev)
  update_edge_prob   <- clCreateKernel program "update_edge_prob"
  update_edge_survey <- clCreateKernel program "update_edge_survey"
  compute_var_prob   <- clCreateKernel program "compute_var_prob"

  return $
    Solver
    { svOutputMessage = outputMessage

    , svContext = context
    , svDevice  = dev
    , svQueue   = queue
    , svUpdateEdgeProb   = update_edge_prob
    , svUpdateEdgeSurvey = update_edge_survey
    , svComputeVarProb   = compute_var_prob

    , svVarEdges       = varEdges
    , svVarEdgesWeight = varEdgesWeight
    , svVarOffset      = varOffset
    , svVarLength      = varLength
    , svVarFixed       = varFixed
    , svVarProb        = varProb
    , svClauseOffset   = clauseOffset
    , svClauseLength   = clauseLength
    , svEdgeSurvey     = edgeSurvey
    , svEdgeProbU      = edgeProbU

    , svTolRef = tolRef
    , svIterLimRef = maxIterRef
    }

deleteSolver :: Solver -> IO ()
deleteSolver solver = do
  _ <- clReleaseKernel (svUpdateEdgeProb solver)
  _ <- clReleaseKernel (svUpdateEdgeSurvey solver)
  _ <- clReleaseKernel (svComputeVarProb solver)
  _ <- clReleaseCommandQueue (svQueue solver)
  _ <- clReleaseContext (svContext solver)
  return ()

initializeRandom :: Solver -> Rand.GenIO -> IO ()
initializeRandom solver gen = do
  n <- getNConstraints solver
  numLoop 0 (n-1) $ \i -> do
    off <- fromIntegral <$> VGM.unsafeRead (svClauseOffset solver) i
    len <- fromIntegral <$> VGM.unsafeRead (svClauseLength solver) i
    case len of
      0 -> return ()
      1 -> VGM.unsafeWrite (svEdgeSurvey solver) off (L.Exp 0)
      _ -> do
        let p :: Double
            p = 1 / fromIntegral len
        numLoop 0 (len-1) $ \i -> do
          d <- Rand.uniformR (p*0.5, p*1.5) gen
          VGM.unsafeWrite (svEdgeSurvey solver) (off+i) (L.Exp (realToFrac (log d)))

initializeRandomDirichlet :: Solver -> Rand.GenIO -> IO ()
initializeRandomDirichlet solver gen = do
  n <- getNConstraints solver
  numLoop 0 (n-1) $ \i -> do
    off <- fromIntegral <$> VGM.unsafeRead (svClauseOffset solver) i
    len <- fromIntegral <$> VGM.unsafeRead (svClauseLength solver) i
    case len of
      0 -> return ()
      1 -> VGM.unsafeWrite (svEdgeSurvey solver) off (L.Exp 0)
      _ -> do
        (ps :: V.Vector Double) <- Rand.dirichlet (VG.replicate len 1) gen
        numLoop 0 (len-1) $ \i -> do
          VGM.unsafeWrite (svEdgeSurvey solver) (off+i) (L.Exp (realToFrac (log (ps ! i))))

-- | number of variables of the problem.
getNVars :: Solver -> IO Int
getNVars solver = return $ VGM.length (svVarOffset solver)

-- | number of constraints of the problem.
getNConstraints :: Solver -> IO Int
getNConstraints solver = return $ VGM.length (svClauseOffset solver)

-- | number of edges of the factor graph
getNEdges :: Solver -> IO Int
getNEdges solver = return $ VGM.length (svEdgeSurvey solver)

getTolerance :: Solver -> IO Double
getTolerance solver = readIORef (svTolRef solver)

setTolerance :: Solver -> Double -> IO ()
setTolerance solver !tol = writeIORef (svTolRef solver) tol

getIterationLimit :: Solver -> IO (Maybe Int)
getIterationLimit solver = readIORef (svIterLimRef solver)

setIterationLimit :: Solver -> Maybe Int -> IO ()
setIterationLimit solver val = writeIORef (svIterLimRef solver) val

-- | Get the marginal probability of the variable to be @True@, @False@ and unspecified respectively.
getVarProb :: Solver -> SAT.Var -> IO (Double, Double, Double)
getVarProb solver v = do
  let i = v - 1
  pt <- (exp . realToFrac . L.ln) <$> VGM.read (svVarProb solver) (i*2)
  pf <- (exp . realToFrac . L.ln) <$> VGM.read (svVarProb solver) (i*2+1)
  return (pt, pf, 1 - (pt + pf))

propagate :: Solver -> IO Bool
propagate solver = do
  tol <- getTolerance solver
  lim <- getIterationLimit solver
  nv <- getNVars solver
  nc <- getNConstraints solver
  let ne = VGM.length (svEdgeSurvey solver)

  let context = svContext solver
      dev = svDevice solver
      queue = svQueue solver
  platform <- clGetDevicePlatform dev

  let infos = [CL_PLATFORM_PROFILE, CL_PLATFORM_VERSION, CL_PLATFORM_NAME, CL_PLATFORM_VENDOR, CL_PLATFORM_EXTENSIONS]
  forM_ infos $ \info -> do
    s <- clGetPlatformInfo platform info
    svOutputMessage solver $ show info ++ " = " ++ s
  devname <- clGetDeviceName dev
  svOutputMessage solver $ "DEVICE = " ++ devname

  (maxComputeUnits :: Int) <- fromIntegral <$> clGetDeviceMaxComputeUnits dev
  (maxWorkGroupSize :: Int) <- fromIntegral <$> clGetDeviceMaxWorkGroupSize dev
  maxWorkItemSizes@(maxWorkItemSize:_) <- fmap fromIntegral <$> clGetDeviceMaxWorkItemSizes dev
  svOutputMessage solver $ "MAX_COMPUTE_UNITS = " ++ show maxComputeUnits
  svOutputMessage solver $ "MAX_WORK_GROUP_SIZE = " ++ show maxWorkGroupSize
  svOutputMessage solver $ "MAX_WORK_ITEM_SIZES = " ++ show maxWorkItemSizes
  (globalMemSize :: Int) <- fromIntegral <$> clGetDeviceGlobalMemSize dev
  (localMemSize :: Int) <- fromIntegral <$> clGetDeviceLocalMemSize dev
  (maxConstantBufferSize :: Int) <- fromIntegral <$> clGetDeviceMaxConstantBufferSize dev
  (maxConstantArgs :: Int) <- fromIntegral <$> clGetDeviceMaxConstantArgs dev
  svOutputMessage solver $ "GLOBAL_MEM_SIZE = " ++ show globalMemSize
  svOutputMessage solver $ "LOCAL_MEM_SIZE = " ++ show localMemSize
  svOutputMessage solver $ "MAX_CONSTANT_BUFFER_SIZE = " ++ show maxConstantBufferSize
  svOutputMessage solver $ "MAX_CONSTANT_ARGS = " ++ show maxConstantArgs

  let defaultNumGroups = maxComputeUnits * 4

  (updateEdgeProb_kernel_workgroup_size :: Int)
      <- fromIntegral <$> clGetKernelWorkGroupSize (svUpdateEdgeProb solver) dev
  let updateEdgeProb_local_size    = min 32 updateEdgeProb_kernel_workgroup_size
      updateEdgeProb_num_groups    = min defaultNumGroups (maxWorkItemSize `div` updateEdgeProb_local_size)
      updateEdgeProb_global_size   = updateEdgeProb_num_groups * updateEdgeProb_local_size
  svOutputMessage solver $
    printf "update_edge_prob kernel: CL_KERNEL_WORK_GROUP_SIZE=%d -> groupSize=%d numGroups=%d globalSize=%d"
      updateEdgeProb_kernel_workgroup_size updateEdgeProb_local_size updateEdgeProb_num_groups updateEdgeProb_global_size

  (updateEdgeSurvey_kernel_workgroup_size :: Int)
      <- fromIntegral <$> clGetKernelWorkGroupSize (svUpdateEdgeSurvey solver) dev
  let updateEdgeSurvey_local_size  = min 32 updateEdgeSurvey_kernel_workgroup_size
      updateEdgeSurvey_num_groups  = min defaultNumGroups (maxWorkItemSize `div` updateEdgeSurvey_local_size)
      updateEdgeSurvey_global_size = updateEdgeSurvey_num_groups * updateEdgeSurvey_local_size
  svOutputMessage solver $
    printf "update_edge_survey kernel: CL_KERNEL_WORK_GROUP_SIZE=%d -> groupSize=%d numGroups=%d globalSize=%d"
      updateEdgeSurvey_kernel_workgroup_size updateEdgeSurvey_local_size updateEdgeSurvey_num_groups updateEdgeSurvey_global_size

  (computeVarProb_kernel_workgroup_size :: Int)
      <- fromIntegral <$> clGetKernelWorkGroupSize (svComputeVarProb solver) dev
  let computeVarProb_local_size    = min 32 computeVarProb_kernel_workgroup_size
      computeVarProb_num_groups    = min defaultNumGroups (maxWorkItemSize `div` computeVarProb_local_size)
      computeVarProb_global_size   = computeVarProb_num_groups * computeVarProb_local_size
  svOutputMessage solver $
    printf "compute_var_prob kernel: CL_KERNEL_WORK_GROUP_SIZE=%d -> groupSize=%d numGroups=%d globalSize=%d"
      computeVarProb_kernel_workgroup_size computeVarProb_local_size computeVarProb_num_groups computeVarProb_global_size

  let createBufferFromVector :: forall a. VSM.Storable a => [CLMemFlag] -> VSM.IOVector a -> IO CLMem
      createBufferFromVector flags v = do
        VSM.unsafeWith v $ \ptr ->
          clCreateBuffer context (CL_MEM_COPY_HOST_PTR : flags)
            (VGM.length v * sizeOf (undefined :: a), castPtr ptr)

      readBufferToVectorAsync :: forall a. VSM.Storable a => CLMem -> VSM.IOVector a -> IO CLEvent
      readBufferToVectorAsync mem vec = do
        VSM.unsafeWith vec $ \ptr -> do
          clEnqueueReadBuffer queue mem False
            0 (VSM.length vec * sizeOf (undefined :: a)) (castPtr ptr) []

      readBufferToVector :: forall a. VSM.Storable a => CLMem -> VSM.IOVector a -> IO ()
      readBufferToVector mem vec = do
        VSM.unsafeWith vec $ \ptr -> do
          ev <- clEnqueueReadBuffer queue mem True
            0 (VSM.length vec * sizeOf (undefined :: a)) (castPtr ptr) []
          _ <- clReleaseEvent ev
          return ()

  var_offset         <- createBufferFromVector [CL_MEM_READ_ONLY] $ svVarOffset solver
  var_degree         <- createBufferFromVector [CL_MEM_READ_ONLY] $ svVarLength solver
  var_fixed          <- createBufferFromVector [CL_MEM_READ_ONLY] $ svVarFixed solver
  var_edges          <- createBufferFromVector [CL_MEM_READ_ONLY] $ svVarEdges solver
  var_edges_weight   <- createBufferFromVector [CL_MEM_READ_ONLY] $ svVarEdgesWeight solver
  clause_offset      <- createBufferFromVector [CL_MEM_READ_ONLY] $ svClauseOffset solver
  clause_degree      <- createBufferFromVector [CL_MEM_READ_ONLY] $ svClauseLength solver
  edge_survey        <- createBufferFromVector [CL_MEM_READ_WRITE] $ svEdgeSurvey solver
  edge_prob_u        <- clCreateBuffer context [CL_MEM_READ_WRITE {-, CL_MEM_HOST_NOACCESS -}]
                          (ne * sizeOf (undefined :: CFloat), nullPtr)

  global_buf         <- clCreateBuffer context [CL_MEM_READ_WRITE {-, CL_MEM_HOST_NOACCESS -}]
                          (ne * sizeOf (undefined :: CFloat) * 2, nullPtr)
  var_prob           <- clCreateBuffer context [CL_MEM_WRITE_ONLY {-, CL_MEM_HOST_READONLY -}]
                          (nv * sizeOf (undefined :: CFloat) * 2, nullPtr)
  group_max_delta    <- clCreateBuffer context [CL_MEM_WRITE_ONLY {-, CL_MEM_HOST_READONLY -}]
                          (updateEdgeSurvey_num_groups * sizeOf (undefined :: CFloat), nullPtr)

  clSetKernelArgSto (svUpdateEdgeProb solver) 0 (fromIntegral nv :: CLint)
  clSetKernelArgSto (svUpdateEdgeProb solver) 1 var_offset
  clSetKernelArgSto (svUpdateEdgeProb solver) 2 var_degree
  clSetKernelArgSto (svUpdateEdgeProb solver) 3 var_fixed
  clSetKernelArgSto (svUpdateEdgeProb solver) 4 var_edges
  clSetKernelArgSto (svUpdateEdgeProb solver) 5 var_edges_weight
  clSetKernelArgSto (svUpdateEdgeProb solver) 6 global_buf
  clSetKernelArgSto (svUpdateEdgeProb solver) 7 edge_survey
  clSetKernelArgSto (svUpdateEdgeProb solver) 8 edge_prob_u

  clSetKernelArgSto (svUpdateEdgeSurvey solver) 0 (fromIntegral nc :: CLint)
  clSetKernelArgSto (svUpdateEdgeSurvey solver) 1 clause_offset
  clSetKernelArgSto (svUpdateEdgeSurvey solver) 2 clause_degree
  clSetKernelArgSto (svUpdateEdgeSurvey solver) 3 edge_survey
  clSetKernelArgSto (svUpdateEdgeSurvey solver) 4 edge_prob_u
  clSetKernelArgSto (svUpdateEdgeSurvey solver) 5 global_buf
  clSetKernelArgSto (svUpdateEdgeSurvey solver) 6 group_max_delta
  clSetKernelArg    (svUpdateEdgeSurvey solver) 7 (updateEdgeSurvey_local_size * sizeOf (undefined :: CFloat)) nullPtr -- reduce_buf

  clSetKernelArgSto (svComputeVarProb solver) 0 (fromIntegral nv :: CLint)
  clSetKernelArgSto (svComputeVarProb solver) 1 var_offset
  clSetKernelArgSto (svComputeVarProb solver) 2 var_degree
  clSetKernelArgSto (svComputeVarProb solver) 3 var_prob
  clSetKernelArgSto (svComputeVarProb solver) 4 var_edges
  clSetKernelArgSto (svComputeVarProb solver) 5 var_edges_weight
  clSetKernelArgSto (svComputeVarProb solver) 6 edge_survey

  (group_max_delta_vec :: VSM.IOVector CFloat) <- VGM.new updateEdgeSurvey_num_groups

  let loop !i
        | Just l <- lim, i >= l = return (False,i)
        | otherwise = do
            _ <- clReleaseEvent =<< clEnqueueNDRangeKernel queue (svUpdateEdgeProb solver)
                   [updateEdgeProb_global_size] [updateEdgeProb_local_size] []
            _ <- clReleaseEvent =<< clEnqueueNDRangeKernel queue (svUpdateEdgeSurvey solver)
                   [updateEdgeSurvey_global_size] [updateEdgeSurvey_local_size] []
            readBufferToVector group_max_delta group_max_delta_vec
            !delta <- VG.maximum <$> VS.unsafeFreeze group_max_delta_vec
            if realToFrac delta <= tol then do
              return (True,i)
            else
              loop (i+1)

  (b,_steps) <- loop 0

  _ <- clReleaseEvent =<< readBufferToVectorAsync edge_survey (svEdgeSurvey solver)
  when b $ do
    _ <- clReleaseEvent =<< clEnqueueNDRangeKernel queue (svComputeVarProb solver)
      [computeVarProb_global_size] [computeVarProb_local_size] []
    _ <- clReleaseEvent =<< readBufferToVectorAsync var_prob (svVarProb solver)
    return ()

  _ <- clFinish queue

  _ <- clReleaseMemObject var_offset
  _ <- clReleaseMemObject var_degree
  _ <- clReleaseMemObject var_edges
  _ <- clReleaseMemObject var_edges_weight
  _ <- clReleaseMemObject clause_offset
  _ <- clReleaseMemObject clause_degree
  _ <- clReleaseMemObject edge_survey
  _ <- clReleaseMemObject edge_prob_u
  _ <- clReleaseMemObject global_buf
  _ <- clReleaseMemObject var_prob
  _ <- clReleaseMemObject group_max_delta

  return b

fixLit :: Solver -> SAT.Lit -> IO ()
fixLit solver lit = do
  VGM.unsafeWrite (svVarFixed solver) (abs lit - 1) (if lit > 0 then 1 else -1)

unfixLit :: Solver -> SAT.Lit -> IO ()
unfixLit solver lit = do
  VGM.unsafeWrite (svVarFixed solver) (abs lit - 1) 0
