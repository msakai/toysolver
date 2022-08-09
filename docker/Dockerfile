ARG GHC_VERSION=8.10.7

FROM haskell:$GHC_VERSION

ARG TOYSOLVER_VERSION=0.8.0

RUN cabal update && cabal install toysolver-${TOYSOLVER_VERSION} --flags="BuildToyFMF BuildSamplePrograms BuildMiscPrograms"
WORKDIR /data
CMD ["bash"]
