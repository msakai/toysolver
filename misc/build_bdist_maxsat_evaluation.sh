#!/bin/bash
set -eux

STACK_ARGS="--docker"
FLAGS="--flag toysolver:LinuxStatic --flag toysolver:ForceChar8 --flag toysolver:-WithZlib --flag toysolver:-BuildForeignLibraries"

stack build $STACK_ARGS $FLAGS
LOCAL_INSTALL_ROOT=`stack path $STACK_ARGS --local-install-root`

PKG=toysat-maxsat`date +%Y`-`date +%Y%m%d`-`git rev-parse --short HEAD`
if [ -d $PKG ]; then
  rm -r $PKG
fi
mkdir $PKG
cp $LOCAL_INSTALL_ROOT/bin/toysat $PKG/toysat_main
cp COPYING misc/maxsat/toysat/README.md misc/maxsat/toysat/toysat $PKG/
tar Jcf $PKG.tar.xz $PKG

if [ ! -f ubcsat-beta-12-b18.tar.gz ]; then
  wget http://ubcsat.dtompkins.com/downloads/ubcsat-beta-12-b18.tar.gz
fi
if [ -d ubcsat-beta-12-b18 ]; then
  rm -r ubcsat-beta-12-b18
fi
mkdir ubcsat-beta-12-b18
cd ubcsat-beta-12-b18
tar zxf ../ubcsat-beta-12-b18.tar.gz
docker run --rm --platform linux/amd64 -v `pwd`:/work -w /work gcc:12.2.0 gcc -Wall -O3 -static -o ubcsat src/adaptnovelty.c src/algorithms.c src/ddfw.c src/derandomized.c src/g2wsat.c src/gsat-tabu.c src/gsat.c src/gwsat.c src/hsat.c src/hwsat.c src/irots.c src/jack.c src/mt19937ar.c src/mylocal.c src/novelty+p.c src/novelty.c src/parameters.c src/paws.c src/random.c src/reports.c src/rgsat.c src/rnovelty.c src/rots.c src/samd.c src/saps.c src/sparrow.c src/ubcsat-help.c src/ubcsat-internal.c src/ubcsat-io.c src/ubcsat-mem.c src/ubcsat-reports.c src/ubcsat-time.c src/ubcsat-triggers.c src/ubcsat-version.c src/ubcsat.c src/vw.c src/walksat-tabu.c src/walksat.c src/weighted.c -lm
cd ..

PKG=toysat_ls-maxsat`date +%Y`-`date +%Y%m%d`-`git rev-parse --short HEAD`
if [ -d $PKG ]; then
  rm -r $PKG
fi
mkdir $PKG
cp $LOCAL_INSTALL_ROOT/bin/toysat $PKG/toysat_main
cp COPYING misc/maxsat/toysat_ls/README.md misc/maxsat/toysat_ls/toysat_ls $PKG/
cp ubcsat-beta-12-b18/ubcsat $PKG/
tar Jcf $PKG.tar.xz $PKG
