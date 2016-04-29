![PeaCoq logo](http://goto.ucsd.edu/~vrobert/peacoq.png) PeaCoq
===============================================================

[![Build Status](https://travis-ci.org/Ptival/PeaCoq.svg)](https://travis-ci.org/Ptival/PeaCoq)

[![Docker Hub](http://goto.ucsd.edu/~vrobert/docker.png)](https://hub.docker.com/r/ptival/peacoq/)

Dependencies (NixOS)
--------------------

For all of you 1337 hax0rz, a `nix-shell` should pull all the necessary dependencies.
You will need cabal2nix to turn `peacoq.cabal` into `peacoq.nix`:

```
$ cabal2nix . > peacoq.nix
$ nix-shell
# brace yourself, this might take a while the first time!
```

Dependencies (other distributions)
----------------------------------

Using your package manager of choice, pull the following dependencies:

* Camlp5       v. 6.14   +   (not sure, just get the most recent available for you)
* Coq          v. 8.5    +   (will **definitely** not work on <= 8.4)
* npm (nodejs) v. 3.8.6  +/- (likely to work on earlier versions)
* OCaml        v. 4.02.3 +   (might work on 4.01 if Coq builds with it)

Building (everyone)
-------------------

Optionally, you can run `cabal update`, then:

```
$ git clone https://github.com/Ptival/PeaCoq.git
$ cd PeaCoq
$ ./setup.sh
$ cabal install
```

`setup.sh` will perform a lot of operations:
1. `cabal configure` to make sure PeaCoq is build-able
2. `cabal build` PeaCoq's server-side
3. `make` the OCaml plugin that enriches Coq's protocol for PeaCoq
4. `npm install` some JavaScript modules needed by the front-end
5. `bower install` some JavaScript modules needed by the front-end
6. `typings install` some TypeScript definitions needed to type-check the front-end
7. `tsc -p .` transpiles the front-end from TypeScript to JavaScript
8. Finally a configuration file will be created in your home directory

So it will take a while the first time, and steps 1, 4, 5, and 6 will
require an Internet connection.

Running PeaCoq
--------------

```
./dist/build/peacoq/peacoq -p <PORT>
```

Then navigate to `http://localhost:<PORT>/index.html` to start using PeaCoq!

Shortcuts
---------

`<C>` will refer to a `Ctrl` or `Command` key.
`<M>` will refer to a `Alt` or `Option` key.

Note: certain shortcuts offer a poor user experience on Windows and possibly MacOS.

They will eventually be re-bind-able. Feel free to alter them in
`web/js/peacoq-ts/editor/keybindings.ts`.

| Shortcut      | Action        |
| ------------- | ------------- |
| <C> <M> L     | Load a file   |
| <C> <M> S     | Save a file   |
| <C> <M> Up    | Step backward |
| <C> <M> Right | Step to caret |
| <C> <M> Down  | Step forward  |
| <C> <M> +     | Increase font |
| <C> <M> -     | Decrease font |
