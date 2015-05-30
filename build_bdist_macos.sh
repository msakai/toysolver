#!/bin/bash

cabal sandbox init
cabal update
cabal install --only-dependencies --flag=BuildToyFMF --flag=BuildSamplePrograms --flag=BuildMiscPrograms
cabal configure --ghc-options="-optl-mmacosx-version-min=10.6" --flag=BuildToyFMF --flag=BuildSamplePrograms --flag=BuildMiscPrograms
cabal build

VER=`ghc -e ":m + Control.Monad Distribution.Package Distribution.PackageDescription Distribution.PackageDescription.Parse Distribution.Verbosity Data.Version" -e 'putStrLn =<< liftM (showVersion . pkgVersion . package . packageDescription) (readPackageDescription silent "toysolver.cabal")'`

PKG=toysolver-$VER-macos

rm -r $PKG
mkdir $PKG
cp dist/build/htc/htc dist/build/knapsack/knapsack dist/build/lpconvert/lpconvert dist/build/nqueens/nqueens dist/build/pbconvert/pbconvert dist/build/sudoku/sudoku dist/build/toyfmf/toyfmf dist/build/toysat/toysat dist/build/toysolver/toysolver $PKG/
zip -r $PKG.zip $PKG
