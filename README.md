# MUNTA -- Fully Verified Model Checker for Timed Automata

## Introduction
MUNTA is
- a model checker for the popular realtime systems modeling formalism of Timed Automata
- formally verified with Isabelle/HOL: there is a machine-checked proof that it only computes correct results!

MUNTA is at an early stage of development. Nevertheless, you can:
- run the model checker on a number of benchmarks
- browse the Isabelle/HOL proof
- try its graphical user interface [here](https://wimmers.github.io/munta-frontend/)

## Graphical User Interface
MUNTA now features a graphical user interface:
- [try it](https://wimmers.github.io/munta-frontend/)
- [source code](https://github.com/wimmers/munta-frontend)
- [instructions on how to run the verification server](#verification-server)

## Building

The following instructions should work on all Unix systems.

#### To build the checker:
Install the [MLton compiler](http://mlton.org/). Then run:
```
cd ML
make
```

#### To build the checker with OCaml:
Replace `Big_int` with `Big_int_Z` in `UPPAAL_Model_Checker.ml` and `to_int` with `int_of_big_int`.
Then run
```
cd ML
ocamlfind ocamlopt -package zarith -package angstrom -linkpkg nums.cmxa -linkpkg UPPAAL_Model_Checker.ml -linkpkg Checker.ml
```

#### To browse the sources interactively in Isabelle:
Install [Isabelle](https://isabelle.in.tum.de/) and the [AFP](https://www.isa-afp.org/using.shtml). Then run:
```
isabelle jedit -l Refine_Imperative_HOL
```
and open one of the `.thy` files.

#### To build the Isabelle sources and extract the checker source code:
Install [Isabelle](https://isabelle.in.tum.de/) and the [AFP](https://www.isa-afp.org/using.shtml). Then run:
```
isabelle build -d . TA_Code
```
and build the checker as described above.

## Verification Server
After building, you can run the verification server via:
```
cd ML
python server.py
```
The server will run under port 3069 and communicates with the GUI.

## Running
Pick one of the files from `benchmarks` and run:
```
ML/munta < benchmarks/<the_benchmark>.munta
```

## Documentation

### Input Format
MUNTA is aimed at understanding bytecode produced by [UPPAAL](http://uppaal.org/).
However, for the time being, this bytecode needs to be pre-processed slightly.
You can find some pre-processed benchmarks in `benchmarks`.
The input format is documented in `UPPAAL_Asm.thy` and `ML/Checker.sml`.

### Isabelle Formalizations
Human readable `.pdf` documents (with textual annotations) of the formalizations can be produced by Isabelle.
Run
```
isabelle build -d . TA
isabelle build -d . TA_All
```
and you will get the following:
- `output/abstract_reachability.pdf`: the abstract formalization of reachability checking for Timed Automata
- `output/model_checking.pdf`: the formalization of MUNTA and the route from the abstract formalization to the correctness proof for MUNTA
- `output/abstract_reachability_proofs.pdf`, `output/model_checking_proofs.pdf`: variants of the above documents with proofs

## Benchmarks
The benchmarks are derived from the [UPPAAL](https://www.it.uu.se/research/group/darts/uppaal/benchmarks/) and
[TChecker](http://www.labri.fr/perso/herbrete/tchecker/) benchmarks.
