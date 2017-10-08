#!/bin/bash

STACK_YAML=stack.yaml
RESOLVER=lts-9.2

# wget -qO- https://get.haskellstack.org/ | sh
PATH=$HOME/.local/bin:$PATH

stack --stack-yaml=$STACK_YAML --resolver=$RESOLVER --install-ghc build \
  --flag toysolver:BuildToyFMF \
  --flag toysolver:BuildSamplePrograms

VER=`stack exec ghc -- -ignore-dot-ghci -e ":m + Control.Monad Distribution.Package Distribution.PackageDescription Distribution.PackageDescription.Parse Distribution.Verbosity Data.Version" -e 'putStrLn =<< liftM (showVersion . pkgVersion . package . packageDescription) (readPackageDescription silent "toysolver.cabal")'`
STACK_LOCAL_INSTALL_ROOT=`stack --stack-yaml=$STACK_YAML --resolver=$RESOLVER path --local-install-root`
OS=`stack exec ghc -- -ignore-dot-ghci -e ":m +System.Info" -e "putStrLn os"`
ARCH=`stack exec ghc -- -ignore-dot-ghci -e ":m +System.Info" -e "putStrLn arch"`
PLATFORM=$ARCH-$OS

PKG=toysolver-${VER}-${OS}-${ARCH}

rm -r $PKG
mkdir $PKG
mkdir $PKG/bin
cp $STACK_LOCAL_INSTALL_ROOT/bin/{toyconvert,toyfmf,toyqbf,toysat,toysmt,toysolver} $PKG/bin/
cp $STACK_LOCAL_INSTALL_ROOT/bin/{assign,htc,knapsack,nonogram,nqueens,numberlink,sudoku} $PKG/bin/
cp -a samples $PKG/
cp COPYING-GPL README.md CHANGELOG.markdown $PKG/
tar Jcf $PKG.tar.xz $PKG --owner=sakai --group=sakai
