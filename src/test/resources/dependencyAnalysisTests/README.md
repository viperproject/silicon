# Dependency Analysis Test

## Soundness Tests

The programs for annotated tests can be found in the folders `all`, `unitTests`, and `mce`.

Pruning tests are executed against all annotated tests and additionally the programs in folder `real-world-examples`.

Both are executed using `src/test/scala/AssumptionAnalysisTests.scala`.

By default, only expected dependencies are checked (`@dependency` annotations).
Setting `CHECK_PRECISION=true` additionally checks precision through `@irrelevant` annotations and reports false positives as an error.

## Precision Benchmark

The base programs are defined in folder `unitTests` and interferences in `precisionTests\scripts\interferences.txt`.

Executing the benchmark:

1. Generate test programs: `python precisionTests\scripts\precision_test_generator.py`
   1. Generates a number of subfolders in `precisionTests`.
   
1. Execute precision benchmark using `src/test/scala/AssumptionAnalysisPrecisionBenchmark.scala`.
   1. Results are written to `precisionTests\results\results_{timestamp}.out`

1. Plot the result: `python precisionTests\scripts\precision_benchmark_plotter.py`
   1. Input file name: name of the result file (e.g., `result_2025-09-22_20-07-27.out`)
   1. Each table cell represents the precision computed as `#(real dependencies) / #(reported dependencies)`.
      Real dependencies are computed as `#(reported dependencies) - #(reported dependencies annotated as irrelevant)`.


To analyze the cause of imprecision, `src/test/scala/AssumptionAnalysisTests.scala` with `CHECK_PRECISION=true` can be executed on the program of interest.
Imprecise results are reported as `Unexpected dependency` and make the test fail.