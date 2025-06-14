# ochacaml4d-instruction

This repository contains implementations of Delimited continuation operators' Abstract Machine (DAM).
DAM extends the ZINC Abstract Machine instruction set with four delimited continuation operators.

## Structure of this repository

The repository contains multiple implementation versions that follow different derivation paths.
Each implementation represents a specific stage in the development of DAM.
The folders are organized chronologically and by feature implementation, allowing you to trace the evolution of the abstract machine design.

## Installation and usage

### Prerequisites

- Save [OcamlMakefile](https://github.com/mmottl/ocaml-makefile/blob/master/OCamlMakefile) as `~/include/OCamlMakefile`
  - If you want to save OcamlMakefile in a different location, modify the `OCAMLMAKEFILE` value in each `step*/Makefile` to the desired local path.

### Running the interpreter

- Navigate to the implementation folder you want to run (e.g., `eval1a`).

```bash
$ cd eval1a
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
(fun f -> (fun z -> f (z + 4)) 2 3) (fun x -> fun y -> x * y) (* press Control-D at the end of your input *)
Parsed : ((fun f -> ((fun z -> (f (z + 4))) 2 3)) (fun x -> (fun y -> (x * y))))
Result : 18
$ ./interpreter
reset (2 * reset (1 + (shift h -> (shift f -> h (f 3))))) # press Control-D at the end of your input
Parsed : reset ((2 * reset ((1 + (shift h -> (shift f -> (h (f 3))))))))
Result : 8
```

- To remove the interpreter executables:

```bash
$ make clean
```

### Running the automated test suite for the interpreter

The `test-suite` folder contains code for testing the behavior of this interpreter.

- To run all test cases at once, navigate to the folder you want to test (e.g., `eval1a`) and execute the `make test` command.
  - This will run all the prepared test cases and output their logs.

```bash
$ cd eval1a
$ make test
Passed: /.../ochacaml4d-derive-instruction/test-suite/0/appterm.ml
Passed: /.../ochacaml4d-derive-instruction/test-suite/0/nested-app.ml
...
Passed: /.../ochacaml4d-derive-instruction/test-suite/4/test4.ml
33 test(s) passed
0 test(s) failed
```
