PeaCoq
======

[![Build Status](https://travis-ci.org/Ptival/PeaCoq.svg)](https://travis-ci.org/Ptival/PeaCoq)

[![Docker Hub](https://www.docker.com/sites/default/files/legal/small_h.png =100x)](https://hub.docker.com/r/ptival/peacoq/)

Building PeaCoq
---------------

To build PeaCoq, first ensure you have a recent
[GHC](https://www.haskell.org/downloads) (at least 7.10), and
[Coq 8.4](https://coq.inria.fr/download).
Ensure that `coqtop` is somewhere in your `PATH`.
You will also need `wget` to fetch
all the necessary JavaScript libraries.

Once all dependencies are satisfied,
the following sequence of commands should
download and build PeaCoq:
```
  $ git clone https://github.com/Ptival/PeaCoq.git
  $ cd PeaCoq
  $ ./setup.sh
  $ cabal install
```

Running PeaCoq
--------------

```
  peacoq -p <PORT>
```

Then open `http://localhost:<PORT>` to start using PeaCoq!
You can also navigate your browser to
`http://localhost:<PORT>/<FILE>.html`
to access `web/<FILE>.html` from this repo.
