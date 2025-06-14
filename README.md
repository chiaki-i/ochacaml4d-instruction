# ochacaml4d-instruction

This repository contains implementations of Delimited continuation operators' Abstract Machine (DAM) for a new language called OchaCaml4D.

DAM extends the [ZINC Abstract Machine](https://caml.inria.fr/pub/papers/xleroy-zinc.pdf) instruction set with four delimited continuation operators.
A distinctive feature of DAM is that it is derived through a series of straightforward program transformations from a [continuation-passing-style definitional interpreter](https://link.springer.com/article/10.1007/s10990-007-9010-4).

## Structure of this repository

The repository contains multiple implementation versions that follow derivation paths.
Each implementation corresponds to the specific derivation steps in the paper.

## Installation and usage

### Prerequisites

- Save [OcamlMakefile](https://github.com/mmottl/ocaml-makefile/blob/master/OCamlMakefile) as `~/include/OCamlMakefile`
  - If you want to save OcamlMakefile in a different location, modify the `OCAMLMAKEFILE` value in each `eval*/Makefile` to the desired local path.

### Running the interpreter

- Navigate to the implementation folder you want to run (e.g., `eval01a`).

```bash
$ cd eval01a
```

- Compile the code, which will create an executable file named `./interpreter` in the same folder.

```bash
$ make
```

- Launch the interpreter and input the code you want to execute, then press Control-D at the end of your input, to run the code.
  - The supported syntax includes:
    - Integers and their basic arithmetic operations (`+`, `-`, `*`, `/`)
    - Function abstraction (`fun x -> ...`; the same as the anonymous functions in OCaml)
    - Function application
    - Delimited continuation operators (`shift k -> ...`, `control k -> ...`, `shift0 k -> ...`, `control0 k -> ...`, `reset ...`)

```bash
$ ./interpreter
(fun f -> (fun z -> f (z + 4)) 2 3) (fun x -> fun y -> x * y) # press Control-D
Parsed : ((fun f -> ((fun z -> (f (z + 4))) 2 3)) (fun x -> (fun y -> (x * y))))
Result : 18
$ ./interpreter
reset (2 * reset (1 + (shift h -> (shift f -> h (f 3))))) # press Control-D
Parsed : reset ((2 * reset ((1 + (shift h -> (shift f -> (h (f 3))))))))
Result : 8
```

- To remove the interpreter executables:

```bash
$ make clean
```

### Running the automated test suite for the interpreter

The `test-suite` folder contains code for testing the behavior of this interpreter.

- To run all test cases at once, navigate to the folder you want to test (e.g., `eval01a`) and execute the `make test` command.
  - This will run all the prepared test cases and output their logs.

```bash
$ cd eval01a
$ make test
Passed: /.../ochacaml4d-instruction/test-suite/0/appterm.ml
Passed: /.../ochacaml4d-instruction/test-suite/0/nested-app.ml
...
Passed: /.../ochacaml4d-instruction/test-suite/4/test4.ml
33 test(s) passed
0 test(s) failed
```
