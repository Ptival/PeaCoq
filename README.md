PeaCoq
======

Building PeaCoq
---------------

You will need a somewhat recent `ghc` and `cabal`.

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
