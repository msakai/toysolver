-- stack --install-ghc runghc --package turtle build_artifacts.hs
{-# LANGUAGE CPP #-}
{-# LANGUAGE OverloadedStrings #-}

-- script for building artifacts on AppVeyor and Travis-CI

import Turtle
import qualified Control.Foldl as L
import Control.Monad
import Distribution.Package
import Distribution.PackageDescription
#if MIN_VERSION_Cabal(2,2,0)
import Distribution.PackageDescription.Parsec
import Distribution.Pretty
#else
import Distribution.PackageDescription.Parse
#endif
import Distribution.Version
import Distribution.Verbosity
import qualified System.Info as Info

main :: IO ()
main = sh $ do
  let (package_platform, exeSuffix, archive) =
        case Info.os of
          "mingw32" -> (if Info.arch == "x86_64" then "win64" else "win32", Just "exe", archive7z)
          "linux"   -> ("linux-" ++ Info.arch, Nothing, archiveTarXz)
          "darwin"  -> ("macos", Nothing, archiveTarXz)
          _ -> error ("unknown os: " ++ Info.os)
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

  let addExeSuffix name =
        case exeSuffix of
          Just s -> name <.> s
          Nothing -> name

  Just local_install_root <- fold (inproc "stack"  ["path", "--local-install-root"] empty) L.head

#if MIN_VERSION_Cabal(2,2,0)
  ver <- liftIO $ liftM (prettyShow . pkgVersion . package . packageDescription) $
#else
  ver <- liftIO $ liftM (showVersion . pkgVersion . package . packageDescription) $
#endif
           readGenericPackageDescription silent "toysolver.cabal"
  let pkg :: Turtle.FilePath
      pkg = fromString $ "toysolver-" <> ver <> "-" <> package_platform
  b <- testfile pkg
  when b $ rmtree pkg

  mktree (pkg </> "bin")
  let binDir = fromText (lineToText local_install_root) </> "bin"
  forM exe_files $ \name -> do
    cp (binDir </> addExeSuffix name) (pkg </> "bin" </> addExeSuffix name)

  mktree (pkg </> "lib")
  let libDir = fromText (lineToText local_install_root) </> "lib"
  when (Info.os == "mingw32") $ do
    cp (libDir </> "toysat-ipasir.dll") (pkg </> "bin" </> "toysat-ipasir.dll")

  cptree "samples" (pkg </> "samples")
  cp "COPYING-GPL" (pkg </> "COPYING-GPL")
  cp "README.md" (pkg </> "README.md")
  cp "CHANGELOG.markdown" (pkg </> "CHANGELOG.markdown")

  archive pkg

archive7z :: Turtle.FilePath -> Shell ()
archive7z name = do
  b <- testfile (name <.> "7z")
  when b $ rm (name <.> "7z")
  proc "7z" ["a", format fp (name <.> "7z"), format fp name] empty
  return ()

archiveZip :: Turtle.FilePath -> Shell ()
archiveZip name = do
  b <- testfile (name <.> "zip")
  when b $ rm (name <.> "zip")
  proc "zip" ["-r", format fp (name <.> "zip"), format fp name] empty
  return ()

archiveTarXz :: Turtle.FilePath -> Shell ()
archiveTarXz name = do
  b <- testfile (name <.> "tar.xz")
  when b $ rm (name <.> "tar.xz")
  proc "tar" ["Jcf", format fp (name <.> "tar.xz"), format fp name] empty
  return ()
