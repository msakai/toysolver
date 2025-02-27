# Release process

## Preparation

* Run `ruby misc/remove-trailing-space.rb`
* Run `ruby misc/collect-language-pragmas.rb` and update `Other-Extensions` in `.cabal` if necessary
* Run `ruby misc/collect-min-version-macro.rb` and remove `#if`s that are always satisfied by the versions specified by `Build-Depends`
* Update `CHANGELOG.markdown`
* Bump version in `toysolver.cabal` if necessary.

## Set environment variables

```shell-session
$ export GHC_VERSION=9.4
$ export TOYSOLVER_VERSION=X.Y.Z
```

## Make git tag and push it

```shell-session
$ git tag v${TOYSOLVER_VERSION}
$ git push origin v${TOYSOLVER_VERSION}
```

## Check draft release generated by GitHub Actions

.

## Upload to Hackage

```shell-session
$ stack upload .`
```

## Make the draft release public

.

## Update [homebrew-tap](https://github.com/msakai/homebrew-tap)

e.g. https://github.com/msakai/homebrew-tap/pull/3

## Update docker image

On AMD64 machine:

```shell-session
$ docker build --platform linux/amd64 \
  --build-arg GHC_VERSION --build-arg TOYSOLVER_VERSION \
  -t msakai/toysolver:${TOYSOLVER_VERSION}-amd64 -f docker/Dockerfile .
$ docker push msakai/toysolver:${TOYSOLVER_VERSION}-amd64
```

On macOS with Apple Silicon:

```shell-session
$ docker build --platform linux/arm64 \
  --build-arg GHC_VERSION --build-arg TOYSOLVER_VERSION \
  -t msakai/toysolver:${TOYSOLVER_VERSION}-arm64 -f docker/Dockerfile .
$ docker push msakai/toysolver:${TOYSOLVER_VERSION}-arm64
```

On any machine:

```shell-session
$ docker manifest create msakai/toysolver:${TOYSOLVER_VERSION} \
  --amend msakai/toysolver:${TOYSOLVER_VERSION}-amd64 \
  --amend msakai/toysolver:${TOYSOLVER_VERSION}-arm64
$ docker manifest push msakai/toysolver:${TOYSOLVER_VERSION}
$ docker manifest create msakai/toysolver:latest \
  --amend msakai/toysolver:${TOYSOLVER_VERSION}-amd64 \
  --amend msakai/toysolver:${TOYSOLVER_VERSION}-arm64
$ docker manifest push msakai/toysolver:latest
```

## Update `ersatz-toysat` and `satchmo-toysat`  if necessary

.

