#!/bin/bash

STACK_YAML=stack.yaml
RESOLVER=lts-9.2
ARCH=win64

if [ ! -f stack-windows-x86_64.zip ]; then
  curl -ostack-windows-x86_64.zip -L --insecure http://www.stackage.org/stack/windows-x86_64
fi
unzip stack-windows-x86_64.zip stack.exe

#sudo apt-get update
#sudo apt-get install wine

wine stack --stack-yaml=$STACK_YAML --resolver=$RESOLVER --install-ghc build \
  --flag toysolver:BuildToyFMF \
  --flag toysolver:BuildSamplePrograms

VER=`wine stack exec ghc -- -ignore-dot-ghci -e ":m + Control.Monad Distribution.Package Distribution.PackageDescription Distribution.PackageDescription.Parse Distribution.Verbosity Data.Version System.IO" -e "hSetBinaryMode stdout True" -e 'putStrLn =<< liftM (showVersion . pkgVersion . package . packageDescription) (readPackageDescription silent "toysolver.cabal")'`
STACK_LOCAL_INSTALL_ROOT=`wine stack --stack-yaml=$STACK_YAML --resolver=$RESOLVER path --local-install-root`

PKG=toysolver-${VER}-$ARCH

rm -r $PKG
mkdir $PKG
mkdir $PKG/bin
cp $STACK_LOCAL_INSTALL_ROOT/bin/{toyconvert,toyfmf,toyqbf,toysat,toysmt,toysolver}.exe $PKG/bin/
cp $STACK_LOCAL_INSTALL_ROOT/bin/{assign,htc,knapsack,nonogram,nqueens,numberlink,sudoku}.exe $PKG/bin/
cp -a samples $PKG/
cp COPYING-GPL README.md CHANGELOG.markdown $PKG/
zip -r $PKG.zip $PKG
