#!/bin/bash
sudo apt-get update
sudo apt-get install wine wget cabal-install

wget https://www.haskell.org/platform/download/2014.2.0.0/HaskellPlatform-2014.2.0.0-i386-setup.exe
wine HaskellPlatform-2014.2.0.0-i386-setup.exe

# https://plus.google.com/+MasahiroSakai/posts/RTXUt5MkVPt
#wine cabal update
cabal update
cp -a ~/.cabal/packages ~/.wine/drive_c/users/`whoami`/Application\ Data/cabal/

wine cabal sandbox init
wine cabal install --only-dependencies --flag=BuildToyFMF --flag=BuildSamplePrograms --flag=BuildMiscPrograms
wine cabal configure --flag=BuildToyFMF --flag=BuildSamplePrograms --flag=BuildMiscPrograms
wine cabal build

VER=`wine ghc -e ":m + Control.Monad Distribution.Package Distribution.PackageDescription Distribution.PackageDescription.Parse Distribution.Verbosity Data.Version System.IO" -e "SetBinaryMode stdout True" -e 'putStrLn =<< liftM (showVersion . pkgVersion . package . packageDescription) (readPackageDescription silent "toysolver.cabal")'`

PKG=toysolver-$VER-win32

rm -r $PKG
mkdir $PKG
cp dist/build/htc/htc.exe dist/build/knapsack/knapsack.exe dist/build/lpconvert/lpconvert.exe dist/build/nqueens/nqueens.exe dist/build/pbconvert/pbconvert.exe dist/build/sudoku/sudoku.exe dist/build/toyfmf/toyfmf.exe dist/build/toysat/toysat.exe dist/build/ToySolver/toysolver.exe $PKG/
zip $PKG.zip $PKG
