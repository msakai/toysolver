{-# LANGUAGE CPP #-}
{-# LANGUAGE OverloadedStrings #-}

-- script for building artifacts on AppVeyor and Travis-CI

import Turtle
import qualified Control.Foldl as L
import Control.Monad
#if MIN_VERSION_turtle(1,6,0)
import qualified Data.Text as T
#endif
import Distribution.Package
import Distribution.PackageDescription
import Distribution.PackageDescription.Parsec
import Distribution.Pretty
#if MIN_VERSION_Cabal(3,8,0)
import Distribution.Simple.PackageDescription (readGenericPackageDescription)
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
          "darwin"  -> ("macos-" ++ Info.arch, Nothing, archiveTarXz)
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

  ver <- liftIO $ liftM (prettyShow . pkgVersion . package . packageDescription) $
           readGenericPackageDescription silent "toysolver.cabal"
  let pkg :: Turtle.FilePath
      pkg = fromString $ "toysolver-" <> ver <> "-" <> package_platform
  b <- testfile pkg
  when b $ rmtree pkg

  mktree (pkg </> "bin")
#if MIN_VERSION_turtle(1,6,0)
  let binDir = T.unpack (lineToText local_install_root) </> "bin"
#else
  let binDir = fromText (lineToText local_install_root) </> "bin"
#endif
  forM exe_files $ \name -> do
    cp (binDir </> addExeSuffix name) (pkg </> "bin" </> addExeSuffix name)

  mktree (pkg </> "lib")
#if MIN_VERSION_turtle(1,6,0)
  let libDir = T.unpack (lineToText local_install_root) </> "lib"
#else
  let libDir = fromText (lineToText local_install_root) </> "lib"
#endif
  when (Info.os == "mingw32") $ do
    cp (libDir </> "toysat-ipasir.dll") (pkg </> "bin" </> "toysat-ipasir.dll")
    proc "stack"
      [ "exec", "--", "dlltool"
      , "--dllname", "toysat-ipasir.dll"
      , "--input-def", "app/toysat-ipasir/ipasir.def"
      , "--output-lib", format fp (pkg </> "lib" </> "toysat-ipasir.dll.a")
      ]
      empty
    return ()

  cptree "samples" (pkg </> "samples")
  cp "COPYING-GPL" (pkg </> "COPYING-GPL")
  cp "README.md" (pkg </> "README.md")
  cp "INSTALL.md" (pkg </> "INSTALL.md")
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
