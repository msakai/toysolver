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
import qualified System.Info as Info

main :: IO ()
main = sh $ do
  let package_platform = if Info.arch == "x86_64" then "win64" else "win32"
      exe_files =
        [ "toyconvert"
        , "toyfmf"
        , "toyqbf"
        , "toysat"
        , "toysmt"
        , "toysolver"
        ] ++
        [ "assign"
        , "htc"
        , "knapsack"
        , "nonogram"
        , "nqueens"
        , "numberlink"
        , "shortest-path"
        , "sudoku"
        ]

  Just local_install_root <- fold (inproc "stack"  ["path", "--local-install-root"] empty) L.head

  ver <- liftIO $ liftM (showVersion . pkgVersion . package . packageDescription) $
           readPackageDescription silent "toysolver.cabal"  
  let pkg :: IsString a => a
      pkg = fromString $ "toysolver-" <> ver <> "-" <> package_platform
  b <- testfile pkg
  when b $ rmtree pkg
  mktree (pkg </> "bin")

  let binDir = fromText (lineToText local_install_root) </> "bin"
  forM exe_files $ \name -> do
    cp (binDir </> name <.> "exe") (pkg </> "bin" </> name <.> "exe")
  
  cptree "samples" (pkg </> "samples")
  cp "COPYING-GPL" (pkg </> "COPYING-GPL")
  cp "README.md" (pkg </> "README.md")
  cp "CHANGELOG.markdown" (pkg </> "CHANGELOG.markdown")

  b <- testfile (pkg <.> "7z")
  when b $ rm (pkg <.> "7z")
  proc "7z" ["a", format fp (pkg <.> "7z"), pkg] empty
