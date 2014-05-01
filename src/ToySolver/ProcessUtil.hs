{-# LANGUAGE CPP #-}
{-# OPTIONS_GHC -Wall #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.ProcessUtil
-- Copyright   :  (c) Masahiro Sakai 2014
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  non-portable (CPP)
--
-----------------------------------------------------------------------------
module ToySolver.ProcessUtil
  ( runProcessWithOutputCallback
  ) where

import Control.Concurrent
import Control.Concurrent.STM
import Control.Exception (SomeException, try, mask, throwIO)
import qualified Control.Exception as C
import Control.Monad
import Foreign.C
import System.Exit
import System.IO
import System.IO.Error
import System.Process

#ifdef __GLASGOW_HASKELL__
import GHC.IO.Exception ( IOErrorType(..), IOException(..) )
#endif

runProcessWithOutputCallback
  :: FilePath -- ^ Filename of the executable (see 'proc' for details)
  -> [String] -- ^ any arguments
  -> String   -- ^ standard input
  -> (String -> IO ()) -- ^ callback function which is called when a line is read from stdout
  -> (String -> IO ()) -- ^ callback function which is called when a line is read from stderr
  -> IO ExitCode
runProcessWithOutputCallback cmd args input putMsg putErr = do
  (Just inh, Just outh, Just errh, processh) <- createProcess
    (proc cmd args)
    { std_in  = CreatePipe
    , std_out = CreatePipe
    , std_err = CreatePipe
    }
  req <- newEmptyTMVarIO
  let f act = atomically (putTMVar req act)
      m1 = forever (hGetLine outh >>= \s -> f (putMsg s))
           `catchIOError` (\e -> if isEOFError e then return () else ioError e)
      m2 = forever (hGetLine errh >>= \s -> f (putErr s))
           `catchIOError` (\e -> if isEOFError e then return () else ioError e)
  withForkWait m1 $ \waitOut -> do
    withForkWait m2 $ \waitErr -> do
      -- now write any input
      unless (null input) $
        ignoreSigPipe $ hPutStr inh input
      -- hClose performs implicit hFlush, and thus may trigger a SIGPIPE
      ignoreSigPipe $ hClose inh

      hSetBuffering outh LineBuffering
      hSetBuffering errh LineBuffering
      let loop = join $ atomically $ msum $
            [ do act <- takeTMVar req
                 return $ act >> loop
            , do guard =<< isEmptyTMVar req
                 waitOut
                 waitErr
                 return $ return ()
            ]
      loop
      hClose outh
      hClose errh
  waitForProcess processh

withForkWait :: IO () -> (STM () ->  IO a) -> IO a
withForkWait async body = do
  waitVar <- newEmptyTMVarIO :: IO (TMVar (Either SomeException ()))
  mask $ \restore -> do
    tid <- forkIO $ try (restore async) >>= \v -> atomically (putTMVar waitVar v)
    let wait = takeTMVar waitVar >>= either throwSTM return
    restore (body wait) `C.onException` killThread tid

ignoreSigPipe :: IO () -> IO ()
#if defined(__GLASGOW_HASKELL__)
ignoreSigPipe = C.handle $ \e -> case e of
                                   IOError { ioe_type  = ResourceVanished
                                           , ioe_errno = Just ioe }
                                     | Errno ioe == ePIPE -> return ()
                                   _ -> throwIO e
#else
ignoreSigPipe = id
#endif
