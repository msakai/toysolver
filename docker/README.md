# Dockerfile usage

## Building docker image for a released version

### Example

```
$ docker build -t TAG -f docker/Dockerfile .
```

### Examples with explicit specifications

```
$ docker build --platform linux/amd64 --build-arg GHC_VERSION=9.0.2 --build-arg TOYSOLVER_VERSION=0.8.0 -t TAG -f docker/Dockerfile .
```

```
$ docker build --platform linux/arm64 --build-arg GHC_VERSION=9.2 --build-arg TOYSOLVER_VERSION=0.8.0 -t TAG -f docker/Dockerfile .
```

## Building docker image from working directory

Using stack:
```
$ stack sdist
$ cp $(stack path --dist-dir)/toysolver-*.tar.gz toysolver.tar.gz
$ docker build -t TAG -f docker/working-dir.Dockerfile .
```

Using cabal:
```
$ cabal sdist
$ cp dist-newstyle/sdist/toysolver-*.tar.gz toysolver.tar.gz
$ docker build -t TAG -f docker/working-dir.Dockerfile .
```
