{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE ScopedTypeVariables #-}
module IPASIR where

import Control.Exception
import Control.Monad
import Data.Int
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import Data.IORef
import Foreign
import Foreign.C

import qualified ToySolver.SAT as SAT


type Solver = Ptr ()

type SolverRep = (SAT.Solver, IORef [Int32], IORef [Int32], IORef IntSet)

withSolverRep :: Solver -> (SolverRep -> IO a) -> IO a
withSolverRep ptr k = do
  let sptr :: StablePtr SolverRep
      sptr = castPtrToStablePtr ptr
  solver <- deRefStablePtr sptr
  k solver

ensureVars :: SAT.Solver -> [Int32] -> IO ()
ensureVars _solver [] = return ()
ensureVars solver lits = do
  let maxVar = maximum $ map (abs . fromIntegral) lits
  nv <- SAT.getNVars solver
  when (nv < maxVar) $ SAT.newVars_ solver (maxVar - nv)


foreign export ccall "toysat_ipasir_init" ipasir_init :: IO Solver

-- | Construct a new solver and return a pointer to it.
--
-- Use the returned pointer as the first parameter in each
-- of the following functions.
--
-- Required state: N/A
--
-- State after: @INPUT@
ipasir_init :: IO Solver
ipasir_init = do
  solver <- SAT.newSolver
  addBuf <- newIORef []
  assumptionRef <- newIORef []
  failedLitsRef <- newIORef IntSet.empty
  sptr <- newStablePtr (solver, addBuf, assumptionRef, failedLitsRef)
  return (castStablePtrToPtr sptr)


foreign export ccall "toysat_ipasir_release" ipasir_release :: Solver -> IO ()

-- | Release the solver, i.e., all its resoruces and
-- allocated memory (destructor). The solver pointer
-- cannot be used for any purposes after this call.
--
-- Required state: @INPUT@ or @SAT@ or @UNSAT@
--
-- State after: undefined
ipasir_release :: Solver -> IO ()
ipasir_release ptr = do
  let sptr :: StablePtr SolverRep
      sptr = castPtrToStablePtr ptr
  freeStablePtr sptr


foreign export ccall ipasir_add :: Solver -> Int32 -> IO ()

-- | Add the given literal into the currently added clause
-- or finalize the clause with a 0.
--
-- Clauses added this way cannot be removed. The addition of
-- removable clauses can be simulated using activation literals
-- and assumptions.
--
-- Required state: @INPUT@ or @SAT@ or @UNSAT@
--
-- State after: @INPUT@
--
-- Literals are encoded as (non-zero) integers as in the
-- DIMACS formats.  They have to be smaller or equal to
-- @INT_MAX@ and strictly larger than @INT_MIN@ (to avoid
-- negation overflow).  This applies to all the literal
-- arguments in API functions.
ipasir_add :: Solver -> Int32 -> IO ()
ipasir_add ptr lit = withSolverRep ptr $ \(solver, addBuf, _assumptionRef, _failedLitsRef) -> do
  if lit == 0 then do
    lits <- readIORef addBuf
    ensureVars solver lits
    SAT.addClause solver (map fromIntegral (reverse lits))
  else do
    modifyIORef addBuf (lit :)


foreign export ccall ipasir_assume :: Solver -> Int32 -> IO ()

-- | Add an assumption for the next SAT search (the next call
-- of ipasir_solve).
--
-- After calling 'ipasir_solve' all the previously added assumptions
-- are cleared.
--
-- Required state: @INPUT@ or @SAT@ or @UNSAT@
--
-- State after: @INPUT@
ipasir_assume :: Solver -> Int32 -> IO ()
ipasir_assume ptr lit = withSolverRep ptr $ \(_solver, _addBuf, assumptionRef, _failedLitsRef) -> do
  modifyIORef assumptionRef (lit :)


foreign export ccall ipasir_solve :: Solver -> IO CInt

-- | Solve the formula with specified clauses under the specified assumptions.
--
-- * If the formula is satisfiable the function returns 10 and the state of the solver is changed to @SAT@.
-- * If the formula is unsatisfiable the function returns 20 and the state of the solver is changed to @UNSAT@.
-- * If the search is interrupted (see 'ipasir_set_terminate') the function returns 0 and the state of the solver is changed to @INPUT@.
--
-- This function can be called in any defined state of the solver. 
-- Note that the state of the solver _during_ execution of @ipasir_solve@ is undefined. 
--
-- Required state: @INPUT@ or @SAT@ or @UNSAT@
--
-- State after: @INPUT@ or @SAT@ or @UNSAT@
ipasir_solve :: Solver -> IO CInt
ipasir_solve ptr = withSolverRep ptr $ \(solver, _addBuf, assumptionRef, failedLitsRef) -> do
  assumptions <- readIORef assumptionRef
  writeIORef assumptionRef []
  ensureVars solver (assumptions)
  writeIORef failedLitsRef IntSet.empty
  handle (\(_ :: SAT.Canceled) -> return 0) $ do
    ret <- SAT.solveWith solver (map fromIntegral assumptions)
    if ret then do
      return 10
    else do
      failedLits <- SAT.getFailedAssumptions solver
      writeIORef failedLitsRef (IntSet.fromList failedLits)
      return 20

foreign export ccall ipasir_val :: Solver -> Int32 -> IO CInt

-- | Get the truth value of the given literal in the found satisfying
-- assignment.
--
-- Return @lit@ if True, @-lit@ if False; 
-- @ipasir_val(lit)@ may return 0 if the found assignment is satisfying for both valuations of lit. 
-- Each solution that agrees with all non-zero values of @ipasir_val@ is a model of the formula. 
-- 
-- This function can only be used if 'ipasir_solve' has returned @10@
-- and no 'ipasir_add' nor 'ipasir_assume' has been called
-- since then, i.e., the state of the solver is SAT.
--
-- Required state: @SAT@
--
-- State after: @SAT@
ipasir_val :: Solver -> Int32 -> IO CInt
ipasir_val ptr lit = withSolverRep ptr $ \(solver, _addBuf, _assumptionRef, _failedLitsRef) -> do
  nv <- SAT.getNVars solver
  if nv < abs (fromIntegral lit) then do
    return 0
  else do
    m <- SAT.getModel solver
    if SAT.evalLit m (fromIntegral lit) then
      return (fromIntegral lit)
    else
      return (- fromIntegral lit)


foreign export ccall ipasir_failed :: Solver -> Int32 -> IO CInt

-- | Check if the given assumption literal was used to prove the
-- unsatisfiability of the formula under the assumptions
-- used for the last SAT search. Return 1 if so, 0 otherwise.
-- 
-- The formula remains unsatisfiable even just under assumption literals for which @ipasir_failed@ returns 1. 
-- Note that for literals @lit@ which are not assumption literals, the behavior of @ipasir_failed(lit)@ is not specified. 
-- 
-- This function can only be used if 'ipasir_solve' has returned 20 and
-- no 'ipasir_add' or 'ipasir_assume' has been called since then, i.e.,
-- the state of the solver is @UNSAT@.
--
-- Required state: @UNSAT@
--
-- State after: @UNSAT@
ipasir_failed :: Solver -> Int32 -> IO CInt
ipasir_failed ptr lit = withSolverRep ptr $ \(_solver, _addBuf, _assumptionRef, failedLitsRef) -> do
  failedLits <- readIORef failedLitsRef
  return $ if IntSet.member (fromIntegral lit) failedLits then 1 else 0


foreign export ccall ipasir_set_terminate :: Solver -> Ptr a -> FunPtr (Ptr a -> IO CInt) -> IO ()

-- | Set a callback function used to indicate a termination requirement to the
-- solver.
--
-- The solver will periodically call this function and check its return
-- value during the search. The @ipasir_set_terminate@ function can be called in any
-- state of the solver, the state remains unchanged after the call.
-- The callback function is of the form "@int terminate(void * data)@x"
--
-- * it returns a non-zero value if the solver should terminate.
-- * the solver calls the callback function with the parameter "data"
--   having the value passed in the @ipasir_set_terminate@ function (2nd parameter).
--
-- Required state: @INPUT@ or @SAT@ or @UNSAT@
--
-- State after: @INPUT@ or @SAT@ or @UNSAT@
ipasir_set_terminate :: Solver -> Ptr a -> FunPtr (Ptr a -> IO CInt) -> IO ()
ipasir_set_terminate ptr info funptr = withSolverRep ptr $ \(solver, _addBuf, _assumptionRef, _failedLitsRef) -> do
  if funptr == nullFunPtr then do
    SAT.clearTerminateCallback solver
  else do
    let callback = mkTerminateCallback funptr
    SAT.setTerminateCallback solver $ do
      ret <- callback info
      return (ret /= 0)


foreign export ccall ipasir_set_learn :: Solver -> Ptr a -> CInt -> FunPtr (Ptr a -> Ptr Int32 -> IO ()) -> IO ()

-- | Set a callback function used to extract learned clauses up to a given length from the
-- solver.
--
-- The solver will call this function for each learned clause that satisfies
-- the maximum length (literal count) condition. The @ipasir_set_learn@ function can be called in any
-- state of the solver, the state remains unchanged after the call.
-- The callback function is of the form "@void learn(void * data, int * clause)@"
--
-- * the solver calls the callback function with the parameter "data"
--   having the value passed in the @ipasir_set_learn@ function (2nd parameter).
-- * the argument "clause" is a pointer to a null terminated integer array containing the learned clause.
--   the solver can change the data at the memory location that "clause" points to after the function call.
--
-- Required state: @INPUT@ or @SAT@ or @UNSAT@
--
-- State after: @INPUT@ or @SAT@ or @UNSAT@
ipasir_set_learn :: Solver -> Ptr a -> CInt -> FunPtr (Ptr a -> Ptr Int32 -> IO ()) -> IO ()
ipasir_set_learn ptr info max_length funptr = withSolverRep ptr $ \(solver, _addBuf, _assumptionRef, _failedLitsRef) -> do
  if funptr == nullFunPtr then do
    SAT.clearLearnCallback solver
  else do
    let callback = mkLearnCallback funptr
    SAT.setLearnCallback solver $ \clause -> do
      when (length clause <= fromIntegral max_length) $ do
        withArray0 0 (map fromIntegral clause) (callback info)

foreign import ccall "dynamic" mkTerminateCallback :: FunPtr (Ptr a -> IO CInt) -> (Ptr a -> IO CInt)

foreign import ccall "dynamic" mkLearnCallback :: FunPtr (Ptr a -> Ptr Int32 -> IO ()) -> (Ptr a -> Ptr Int32 -> IO ())
