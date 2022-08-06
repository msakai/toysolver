ARG GHC_VERSION=8.10.7

FROM haskell:$GHC_VERSION

ARG TOYSOLVER_VERSION=0.8.0

# https://github.com/haskell/docker-haskell/issues/81
RUN if [ "$(dpkg-architecture --query DEB_BUILD_GNU_CPU)" = "aarch64" ]; then \
      apt-get update && \
      apt-get install -y --no-install-recommends libnuma-dev && \
      apt-get clean && rm -rf /var/lib/apt/lists/*; \
    fi

RUN cabal update && cabal install toysolver-${TOYSOLVER_VERSION} --flags="BuildToyFMF BuildSamplePrograms BuildMiscPrograms"
WORKDIR /data
CMD ["bash"]
