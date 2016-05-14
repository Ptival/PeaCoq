![PeaCoq logo](http://goto.ucsd.edu/~vrobert/peacoq.png) PeaCoq
===============================================================

[![Build Status](https://travis-ci.org/Ptival/PeaCoq.svg)](https://travis-ci.org/Ptival/PeaCoq)

# [![Docker Hub](http://goto.ucsd.edu/~vrobert/docker.png)](https://hub.docker.com/r/ptival/peacoq/)

Getting ready (everyone)
------------------------

```
$ git clone https://github.com/Ptival/PeaCoq.git
$ cd PeaCoq
```

Dependencies (NixOS)
--------------------

For all of you 1337 hax0rz, `shell.nix` should pull all the necessary
dependencies.

```
$ nix-shell
# brace yourself, this might take a while the first time!
```

Dependencies (other distributions)
----------------------------------

Using your package manager of choice, pull the following dependencies:

| Dependency    | Version | Bound | Comment                                      |
| ------------- | ------- |:-----:| -------------------------------------------- |
| cabal-install | 1.22    | ~     | Use the most recent available                |
| Camlp5        | 6.14    | ?     | Not sure, just get the most recent available |
| Coq           | 8.5     | +     | Will **definitely** not work on < 8.5        |
| GHC           | 7.10.2  | ~+    | I believe I use some of the recent features  |
| NodeJS (npm)  | 3.8.6   | ?     | Any version might work                       |
| OCaml         | 4.02.3  | ~+    | Might work on anything >= 4, if Coq builds   |

Plus, the following cabal dependencies must be pulled manually:

```
$ cabal install alex happy
```

Building (everyone)
-------------------

Optionally (but recommended), you can run `cabal update`, then:

```
$ ./setup.sh
```

`setup.sh` will perform a lot of operations:

1. Check that the required software is present and versions

2. Clean up existing installations of `peacoqtop` and `peacoq-server`

3. Build and install `peacoqtop`, a wrapper around `coqtop`

4. Build and install `peacoq-server`, a small server to communicate with the
  front-end

5. `make` the OCaml plugin that enriches Coq's protocol for PeaCoq

6. `npm install` some JavaScript modules needed by the front-end

7. `typings install` some TypeScript definitions needed to type-check the front-end

8. `tsc -p .` transpiles the front-end from TypeScript to JavaScript

9. Finally a configuration file will be created in your home directory

So it will take a while the first time, and steps 3, 4, 6, and 7 will
require an Internet connection.

Running PeaCoq
--------------

```
./peacoq-server/dist/build/peacoq-server/peacoq-server -p <PORT>
```

Then navigate to `http://localhost:<PORT>/index.html` to start using PeaCoq!

Shortcuts
---------

`<C>` will refer to a `Ctrl` or `Command` key.
`<M>` will refer to a `Alt` or `Option` key.

Note: certain shortcuts offer a poor user experience on Windows and possibly MacOS.

They will eventually be re-bind-able. Feel free to alter them in
`web/js/peacoq-ts/editor/keybindings.ts`.

| Shortcut        | Action        |
| --------------- | ------------- |
| `<C> <M> L`     | Load a file   |
| `<C> <M> S`     | Save a file   |
| `<C> <M> Up`    | Step backward |
| `<C> <M> Right` | Step to caret |
| `<C> <M> Down`  | Step forward  |
| `<C> <M> +`     | Increase font |
| `<C> <M> -`     | Decrease font |

