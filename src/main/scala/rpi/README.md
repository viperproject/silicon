# Inference

This inference is work in progress. A description will be added once the work is complete. 

## Dependencies and Build Instructions

As the inference is part of the Silicon verifier, the dependencies and build instructions are the same:

 * Install a recent version of [sbt](https://www.scala-sbt.org/).
 * Get an executable of the [Z3](https://github.com/Z3Prover/z3/releases) SMT solver.
 * Clone the [Silver](https://github.com/viperproject/silver) and the [Silicon](https://github.com/viperproject/silicon) repositories to your computer, ideally into the same parent directory.
 * Within the Silicon directory, create a symbolic link to the Silver directory:
    * On Linux or Mac, run `ln -s <relative path to silver> silver`.
    * On Windows, run `mklink /D silver <relative path to silver>`.
 * Compile by running `sbt compile`.

## Running the Inference

 * In order to avoid stack overflows it is recommended to run the inference with the VM option `-Xss515m`.
 * Tell the inference where it can find the Z3 executable by either
   1. setting the environment variable `Z3_EXE`, or
   2. using the command line option `--z3`.