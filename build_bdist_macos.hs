#!/usr/bin/env stack
-- stack --resolver lts-7.2 --install-ghc runghc --package turtle
{-# LANGUAGE OverloadedStrings #-}

import Turtle
import Control.Monad
import Distribution.Package
import Distribution.PackageDescription
import Distribution.PackageDescription.Parse
import Distribution.Verbosity
import Data.Version

main = sh $ do
  export "MACOSX_DEPLOYMENT_TARGET" "10.6"

  -- let flags = ["--flag=BuildToyFMF", "--flag=BuildSamplePrograms", "--flag=BuildMiscPrograms"]
  -- proc "cabal" ["sandbox", "init"] empty
  -- proc "cabal" ["update"] empty
  -- proc "cabal" (["install", "--only-dependencies"] ++ flags) empty
  -- proc "cabal" (["configure"] ++ flags) empty
  -- proc "cabal" ["build"] empty
  let flags = ["buildtoyfmf", "buildsampleprograms", "buildmiscprograms"]
  proc "stack" (["build"] ++ concat [["--flag", "toysolver:" <> flag] | flag <- flags]) empty

  ver <- liftIO $ liftM (showVersion . pkgVersion . package . packageDescription) $
           readPackageDescription silent "toysolver.cabal"  
  let pkg :: IsString a => a
      pkg = fromString $ "toysolver-" <> ver <> "-macos"
  b <- testfile pkg
  when b $ rmtree pkg
  mktree (pkg </> "bin")
  let prog_files =
          [ "htc"
          , "knapsack"
          , "nonogram"
          , "nqueens"
          , "toyconvert"
          , "sudoku"
          , "toyfmf"
          , "toysat"
          , "toysmt"
          , "toysolver"
          ]
  forM prog_files $ \name -> do
    --cp ("dist" </> "build" </> name </> name) (pkg </> "bin" </> name)
    cp (".stack-work" </> "install" </> "x86_64-osx" </> "lts-7.2" </> "8.0.1" </> "bin"</> name) (pkg </> "bin" </> name)
    proc "strip" [format fp (pkg </> "bin" </> name)] empty
  proc "cp" ["-r", "samples", format fp (pkg </> "samples")] empty
  cp "COPYING-GPL" (pkg </> "COPYING-GPL")
  cp "README.md" (pkg </> "README.md")
  cp "CHANGELOG.markdown" (pkg </> "CHANGELOG.markdown")

  b <- testfile (pkg <.> "zip")
  when b $ rm (pkg <.> "zip")
  proc "zip" ["-r", format fp (pkg <.> "zip"), pkg] empty
