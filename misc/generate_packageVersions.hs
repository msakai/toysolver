-- stack --install-ghc runghc --package Cabal generate_packageVersions.hs
{-# LANGUAGE CPP #-}
module Main where

import Control.Monad
import Data.Maybe
import qualified Data.Set as Set
import Distribution.Package
import Distribution.PackageDescription
#if MIN_VERSION_Cabal(2,2,0)
import Distribution.PackageDescription.Parsec
#else
import Distribution.PackageDescription.Parse
#endif
import Distribution.Simple.Configure
import Distribution.Simple.LocalBuildInfo
#if MIN_VERSION_Cabal(2,0,0)
import Distribution.Types.CondTree
#endif
import qualified Distribution.Verbosity as Verbosity
import System.Environment

main :: IO ()
main = generate_packageVersions "toysolver.cabal"

generate_packageVersions :: FilePath -> IO ()
generate_packageVersions cabalFile = do
#if MIN_VERSION_Cabal(2,0,0)
  pkgDesc <- readGenericPackageDescription Verbosity.normal cabalFile
#else
  pkgDesc <- readPackageDescription Verbosity.normal cabalFile
#endif
  let pkgs1 =
        case condLibrary pkgDesc of
          Nothing -> Set.empty
          Just tree -> Set.fromList [unPackageName pkgName | constr <- constrs tree, Dependency pkgName _verRange <- constr]
      pkgs2 = Set.unions $
        [ Set.fromList [unPackageName pkgName | constr <- constrs tree, Dependency pkgName _verRange <- constr]
        | (_name, tree) <- condExecutables pkgDesc
        ]
      pkgs = Set.delete "toysolver" $ Set.union pkgs1 pkgs2

  putStrLn "packageVersions :: [(String, String)]"
  putStrLn "packageVersions = sort $ tail"
  putStrLn "  [ (undefined, undefined) -- dummy"
  forM_ pkgs $ \name -> do
    let name2 = map (\c -> if c == '-' then '_' else c) name
    putStrLn $ "#ifdef VERSION_" ++ name2
    putStrLn $ "  , (\"" ++ name ++ "\", VERSION_" ++ name2 ++")"
    putStrLn $ "#endif"
  putStrLn "  ]"

constrs :: CondTree v c a -> [c]
constrs (CondNode _a constr children) =
#if MIN_VERSION_Cabal(2,0,0)
  constr : concat [constrs tree | CondBranch _cond thenTree elseTree <- children, tree <- thenTree : maybeToList elseTree]
#else
  constr : concat [constrs tree | (_cond, thenTree, elseTree) <- children, tree <- thenTree : maybeToList elseTree]
#endif
