# Blond in OCaml

This is Blond written in OCaml.

The file `./lib/evaluator.ml` contains the main interpreter, whlie `./lib/init.ml` contains
the built in functions and special forms of Blond implemented in OCaml. 
The file `./lib/blond.ml` puts everything together.

To run the program, first build it by `dune build` in this directory, then run `./_build/default/bin/main.exe`.
