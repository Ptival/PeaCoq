PeaCoq
======

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

In addition to the build dependencies,
running the server also requires git.

```
  peacoq -p <PORT>
```

Then open `http://localhost:<PORT>` to start using PeaCoq!
You can also navigate your browser to
`http://localhost:<PORT>/<FILE>.html`
to access `web/<FILE>.html` from this repo.
