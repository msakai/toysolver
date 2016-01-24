#!/bin/bash

export MACOSX_DEPLOYMENT_TARGET=10.6

cabal sandbox init
cabal update
cabal install --only-dependencies --flag=BuildToyFMF --flag=BuildSamplePrograms --flag=BuildMiscPrograms
cabal configure --flag=BuildToyFMF --flag=BuildSamplePrograms --flag=BuildMiscPrograms
cabal build

VER=`ghc -ignore-dot-ghci -e ":m + Control.Monad Distribution.Package Distribution.PackageDescription Distribution.PackageDescription.Parse Distribution.Verbosity Data.Version" -e 'putStrLn =<< liftM (showVersion . pkgVersion . package . packageDescription) (readPackageDescription silent "toysolver.cabal")'`

PKG=toysolver-$VER-macos

rm -r $PKG
mkdir $PKG
mkdir $PKG/bin
cp dist/build/htc/htc dist/build/knapsack/knapsack dist/build/lpconvert/lpconvert dist/build/nonogram/nonogram dist/build/nqueens/nqueens dist/build/pbconvert/pbconvert dist/build/sudoku/sudoku dist/build/toyfmf/toyfmf dist/build/toysat/toysat dist/build/toysmt/toysmt dist/build/toysolver/toysolver $PKG/bin
cp -a samples $PKG/
cp COPYING-GPL README.md CHANGELOG.markdown $PKG/
zip -r $PKG.zip $PKG
