# Benchmark Set

This folder contains benchmark examples taken from *Verification Algorithms for Automated Separation Logic Verifiers* (https://github.com/marcoeilers/CAV24-data).
Test annotations have been added for expected failures.
There are examples from Nagini, Prusti, VerCors and some product programs.
There is only one Gobra example currently, because most other examples require `--assumeInjectivityOnInhale`.

The cases here are run together with a group of standard test cases, for 10 repetitions.
The whole benchmark should take less than 30mins on a standard laptop, so there are not many long-running examples.