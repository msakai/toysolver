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
cabal install --only-dependencies
cabal configure --disable-shared --ghc-options="-static -optl-static -optl-pthread"
cabal build

PKG=toysat-maxsat`date +%Y`-`date +%Y%m%d`
rm -r $PKG
mkdir $PKG
cp dist/build/toysat/toysat $PKG/toysat_main
cp misc/maxsat/toysat/README.md misc/maxsat/toysat/toysat $PKG/
tar Jcf $PKG.tar.xz $PKG --owner=sakai --group=sakai

wget -c http://ubcsat.dtompkins.com/downloads/ubcsat-beta-12-b18.tar.gz
rm -r ubcsat-beta-12-b18
mkdir ubcsat-beta-12-b18
cd ubcsat-beta-12-b18
tar zxf ../ubcsat-beta-12-b18.tar.gz
gcc -Wall -O3 -static -o ubcsat src/adaptnovelty.c src/algorithms.c src/ddfw.c src/derandomized.c src/g2wsat.c src/gsat-tabu.c src/gsat.c src/gwsat.c src/hsat.c src/hwsat.c src/irots.c src/jack.c src/mt19937ar.c src/mylocal.c src/novelty+p.c src/novelty.c src/parameters.c src/paws.c src/random.c src/reports.c src/rgsat.c src/rnovelty.c src/rots.c src/samd.c src/saps.c src/sparrow.c src/ubcsat-help.c src/ubcsat-internal.c src/ubcsat-io.c src/ubcsat-mem.c src/ubcsat-reports.c src/ubcsat-time.c src/ubcsat-triggers.c src/ubcsat-version.c src/ubcsat.c src/vw.c src/walksat-tabu.c src/walksat.c src/weighted.c -lm
cd ..

PKG=toysat_ls-maxsat`date +%Y`-`date +%Y%m%d`
rm -r $PKG
mkdir $PKG
cp dist/build/toysat/toysat $PKG/toysat_main
cp misc/maxsat/toysat_ls/README.md misc/maxsat/toysat_ls/toysat_ls $PKG/
cp ubcsat-beta-12-b18/ubcsat $PKG/
tar Jcf $PKG.tar.xz $PKG --owner=sakai --group=sakai
