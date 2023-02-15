#!/bin/bash
set -eux

STACK_ARGS="--docker"
FLAGS="--flag toysolver:LinuxStatic --flag toysolver:ForceChar8 --flag toysolver:-WithZlib --flag toysolver:-BuildForeignLibraries"

stack build $STACK_ARGS $FLAGS
LOCAL_INSTALL_ROOT=`stack path $STACK_ARGS --local-install-root`

PKG=toysat-pb`date +%Y`-`date +%Y%m%d`-`git rev-parse --short HEAD`
if [ -d $PKG ]; then
  rm -r $PKG
fi
mkdir $PKG
cp $LOCAL_INSTALL_ROOT/bin/toysat $PKG/
cp COPYING misc/pb/README.md $PKG/

tar Jcf $PKG.tar.xz $PKG
