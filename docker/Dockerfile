FROM haskell:8.10.2
RUN cabal update && cabal install toysolver --flags="BuildToyFMF BuildSamplePrograms BuildMiscPrograms"
WORKDIR /data
CMD ["bash"]
