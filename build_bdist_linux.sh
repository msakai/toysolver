#!/bin/bash
export CABALVER=1.18
export GHCVER=7.8.4

sudo add-apt-repository -y ppa:hvr/ghc
sudo apt-get update

sudo apt-get install cabal-install-$CABALVER ghc-$GHCVER
export PATH=/opt/ghc/$GHCVER/bin:/opt/cabal/$CABALVER/bin:~/.cabal/bin:$PATH

sudo apt-get install happy-1.19.4 alex-3.1.3
export PATH=/opt/alex/3.1.3/bin:/opt/happy/1.19.4/bin:$PATH

cabal sandbox init
cabal update
cabal install --only-dependencies --flag=BuildToyFMF --flag=BuildSamplePrograms --flag=BuildMiscPrograms
#cabal configure --disable-shared --ghc-options="-static -optl-static -optl-pthread" --flag=BuildToyFMF --flag=BuildSamplePrograms --flag=BuildMiscPrograms
cabal configure -fLinuxStatic --flag=BuildToyFMF --flag=BuildSamplePrograms --flag=BuildMiscPrograms
cabal build

VER=`ghc -ignore-dot-ghci -e ":m + Control.Monad Distribution.Package Distribution.PackageDescription Distribution.PackageDescription.Parse Distribution.Verbosity Data.Version" -e 'putStrLn =<< liftM (showVersion . pkgVersion . package . packageDescription) (readPackageDescription silent "toysolver.cabal")'`
OS=`ghc -ignore-dot-ghci -e ":m +System.Info" -e "putStrLn os"`
ARCH=`ghc -ignore-dot-ghci -e ":m +System.Info" -e "putStrLn arch"`

PKG=toysolver-${VER}-${OS}-${ARCH}

rm -r $PKG
mkdir $PKG
cp dist/build/htc/htc dist/build/knapsack/knapsack dist/build/lpconvert/lpconvert dist/build/nonogram/nonogram dist/build/nqueens/nqueens dist/build/pbconvert/pbconvert dist/build/sudoku/sudoku dist/build/toyfmf/toyfmf dist/build/toysat/toysat dist/build/toysolver/toysolver $PKG/
tar Jcf $PKG.tar.xz $PKG --owner=sakai --group=sakai
