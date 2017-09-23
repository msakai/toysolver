#!/usr/bin/env stack
-- stack --install-ghc runghc --package turtle
{-# LANGUAGE OverloadedStrings #-}

import Turtle
import qualified Control.Foldl as L
import Control.Monad
import Distribution.Package
import Distribution.PackageDescription
import Distribution.PackageDescription.Parse
import Distribution.Verbosity
import Data.Version

main :: IO ()
main = sh $ do
  let package_platform = "win32" -- "macos", "linux-x86_64"

  Just local_install_root <- fold (inproc "stack"  ["path", "--local-install-root"] empty) L.head

  ver <- liftIO $ liftM (showVersion . pkgVersion . package . packageDescription) $
           readPackageDescription silent "toysolver.cabal"  
  let pkg :: IsString a => a
      pkg = fromString $ "toysolver-" <> ver <> "-" <> package_platform
  b <- testfile pkg
  when b $ rmtree pkg
  mktree (pkg </> "bin")

  let binDir = fromText (lineToText local_install_root) </> "bin"
  files <- fold (ls binDir) L.list
  forM files $ \name -> do
    cp name (pkg </> "bin" </> filename name)
  
  cptree "samples" (pkg </> "samples")
  cp "COPYING-GPL" (pkg </> "COPYING-GPL")
  cp "README.md" (pkg </> "README.md")
  cp "CHANGELOG.markdown" (pkg </> "CHANGELOG.markdown")

  b <- testfile (pkg <.> "7z")
  when b $ rm (pkg <.> "7z")
  proc "7z" ["a", format fp (pkg <.> "7z"), pkg] empty
