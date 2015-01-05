PeaCoq
======

Building PeaCoq
---------------

You will need a somewhat recent `ghc` and `cabal`. You can find them in the Haskell Platform ( https://www.haskell.org/platform/ ).
You will also need `wget` to run `setup.sh`. You should be able to find it in your software distribution.

```
  git clone https://github.com/Ptival/PeaCoq.git
  cd PeaCoq
  ./setup.sh
  cabal install
```
  
Running PeaCoq
--------------

```
  peacoq -p <PORT>
```
  
Then open your browser at `http://localhost:<PORT>/<FILE>.html` if you want to access `web/<FILE>.html`.
