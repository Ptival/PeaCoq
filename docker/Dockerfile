FROM haskell:latest
RUN cabal update
RUN apt-get update
RUN apt-get install -y git-core wget unzip pkg-config coq
RUN git clone https://github.com/Ptival/PeaCoq.git
WORKDIR PeaCoq
RUN ./setup.sh
RUN cabal install
EXPOSE 4242
CMD peacoq -p 4242

