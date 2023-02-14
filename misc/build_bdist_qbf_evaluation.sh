#!/bin/bash
set -eux

STACK_ARGS="--docker"
FLAGS="--flag toysolver:LinuxStatic --flag toysolver:ForceChar8 --flag toysolver:-WithZlib --flag toysolver:-BuildForeignLibraries"

stack build $STACK_ARGS $FLAGS
LOCAL_INSTALL_ROOT=`stack path $STACK_ARGS --local-install-root`

PKG=toyqbf-qbfeval`date +%Y`-`date +%Y%m%d`-`git rev-parse --short HEAD`
if [ -d $PKG ]; then
  rm -r $PKG
fi
mkdir $PKG
cp $LOCAL_INSTALL_ROOT/bin/toyqbf $PKG/
cp misc/qbf/README.md $PKG/
cp COPYING $PKG/

tar Jcf $PKG.tar.xz $PKG
