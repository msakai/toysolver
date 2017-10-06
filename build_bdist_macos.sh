#!/bin/bash

export MACOSX_DEPLOYMENT_TARGET=10.11

STACK_YAML=stack.yaml
RESOLVER=lts-9.2

# curl -sSL https://get.haskellstack.org/ | sh
PATH=$HOME/.local/bin:$PATH

stack --stack-yaml=$STACK_YAML --resolver=$RESOLVER --install-ghc build \
  --flag toysolver:BuildToyFMF \
  --flag toysolver:BuildSamplePrograms \
  --flag toysolver:OpenCL

VER=`stack exec ghc -- -ignore-dot-ghci -e ":m + Control.Monad Distribution.Package Distribution.PackageDescription Distribution.PackageDescription.Parse Distribution.Verbosity Data.Version" -e 'putStrLn =<< liftM (showVersion . pkgVersion . package . packageDescription) (readPackageDescription silent "toysolver.cabal")'`
STACK_LOCAL_INSTALL_ROOT=`stack --stack-yaml=$STACK_YAML --resolver=$RESOLVER path --local-install-root`

PKG=toysolver-$VER-macos

rm -r $PKG
mkdir $PKG
mkdir $PKG/bin
cp $STACK_LOCAL_INSTALL_ROOT/bin/{toyconvert,toyfmf,toyqbf,toysat,toysmt,toysolver} $PKG/bin/
cp $STACK_LOCAL_INSTALL_ROOT/bin/{assign,htc,knapsack,nonogram,nqueens,numberlink,sudoku} $PKG/bin/
cp -a samples $PKG/
cp COPYING-GPL README.md CHANGELOG.markdown $PKG/
zip -r $PKG.zip $PKG
