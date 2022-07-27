# Installation

## Installation from binaries

Binary distributions for Windows, Mac, and Linux, can be downloaded from [releases](https://github.com/msakai/toysolver/releases) page.

## Installation from Hackage

`cabal install toysolver` or `stack install toysolver`

## Installation from source using `stack`

1. [Install `stack`](https://docs.haskellstack.org/en/stable/README/#how-to-install)
2. `git clone --recursive https://github.com/msakai/toysolver.git`
3. `cd toysolver`
4. `stack install`

## Installation from source using `cabal-install`

1. Install [GHC](https://www.haskell.org/ghc/) and [cabal](https://www.haskell.org/cabal/#install-upgrade) (You can use [ghcup](https://gitlab.haskell.org/haskell/ghcup-hs#installation) for installing them)
2. `git clone --recursive https://github.com/msakai/toysolver.git`
3. `cd toysolver`
4. `cabal install`

## Docker image

The Docker images can be found at [dockerhub](https://hub.docker.com/repository/docker/msakai/toysolver).

To run `toysat` using Docker for solving `samples/pbs/normalized-j3025_1-sat.opb`:

```
docker run -it --rm -v `pwd`:/data msakai/toysolver toysat samples/pbs/normalized-j3025_1-sat.opb
```
