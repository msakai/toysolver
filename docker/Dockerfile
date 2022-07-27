FROM haskell:8.10.7
RUN cabal update && cabal install toysolver --flags="BuildToyFMF BuildSamplePrograms BuildMiscPrograms"
WORKDIR /data
CMD ["bash"]
