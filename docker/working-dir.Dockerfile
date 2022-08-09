ARG GHC_VERSION=8.10.7

FROM haskell:$GHC_VERSION

COPY toysolver.tar.gz /tmp/cabal/

RUN \
  cd /tmp && \
  tar zxf cabal/toysolver.tar.gz && \
  cd toysolver-* && \
  cabal update && \
  cabal install --flags="BuildToyFMF BuildSamplePrograms BuildMiscPrograms" && \
  cd .. && \
  rm -r toysolver-* cabal/toysolver.tar.gz

WORKDIR /data
CMD ["bash"]
