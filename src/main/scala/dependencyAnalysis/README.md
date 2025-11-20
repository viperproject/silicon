# Dependency Analysis


# Running Silicon with Dependency Analysis

Dependency Analysis is enabled thorough the following configuration options:
`--enableDependencyAnalysis --disableInfeasibilityChecks --proverArgs "proof=true unsat-core=true"`

Additionally, to retrieve the results and query the dependency graph, use:
- `--startDependencyAnalysisTool` 
  - Automatically starts the command-line tool once verification terminates.
- `--dependencyAnalysisExportPath [PATH TO EXPORT FOLDER]`
  - e.g., `--dependencyAnalysisExportPath "graphExports"`
  - Exports the graph to a folder named after the verified program under the given path (e.g. `graphExports/src_test_resources_andrea_quickTest` for input program `src/test/resources/andrea/quickTest.vpr`)

For debugging dependency analysis results, the option `--enableDependencyAnalysisDebugging` can be used which disables the merging of nodes.
As a result, the graph used for query computation and the exported graph contain all low-level details.


# Command-Line Tool

Requires `--startDependencyAnalysisTool`.

Example queries for program `src/test/resources/dependencyAnalysisTests/unitTests/B-permissions.vpr`:
- `dep 99` 
  - Returns all dependencies of assertions on line 99.
- `dep B-permissions@19` 
  - Uniquely identifies the given line when there are many source files.
  - This notation can be used in every command.
- `dep 66 71` 
  - Query multiple lines.
- `downDep 14` 
  - Returns all dependents of assumptions on line 14.
- `hasDep 64 66 71` 
  - Returns true iff there is any dependency between any two queried lines and false otherwise.
- `cov`
  - Prints proof coverage and uncovered nodes of each method.
- `cov perm5` 
  - Prints proof coverage and uncovered nodes of method `perm5`.
- `covL perm5 71` 
  - Prints proof coverage (and uncovered nodes) of assertions on line 71 in method `perm5`.
- `prune 66 71` 
  - Exports the program pruned with respect to lines 66 and 71.
  - exportFileName: path and file name for the pruned program (e.g. `prunedPrograms/test.vpr`


# Neo4j Scripts and Usage

Graphs exported when using `--dependencyAnalysisExportPath [PATH TO EXPORT FOLDER]` can be imported to a [Neo4j database]({https://neo4j.com/) using the `neo4j_importer.py` script.

Importing dependency graphs to Neo4j:

1. [Create your own Neo4j instance](https://neo4j.com/docs/aura/getting-started/create-account/).

1. Replace `[NEO4J_URI]` with the URI to your instance (e.g., `neo4j+ssc://df123ab4.databases.neo4j.io`)
 
1. Set your environment variable `NEO4J-PW` to the password of your instance.

1. Make sure the instance is up and running.
 
1. Execute `python src/main/scala/dependencyAnalysis/neo4j_importer.py` and when queried provide the following inputs:
   1. foldername: relative path to the export folder of the dependency graph (e.g. `graphExports/src_test_resources_andrea_quickTest`)
   1. node_label: label to be given to the nodes created in Neo4j
   1. Note that existing nodes with the same label are deleted!
   
1. Login to Neo4j are explore the graphs. The script creates three graphs, each using a different label for its nodes:
   1. \[label\]: Graph as defined in the export files.
   1. \[label\]_NonInternal: Graph that does not contain any internal nodes and low-level nodes with identical source are already merged into one node.
   1. \[label\]_Explicit: Graph that only contains explicit assumption nodes (and all assertions) and low-level nodes with identical source are already merged into one node.
   1. For a quick start, open the Explore tool and search for `label_NonInternal-(any)-label_NonInternal`. The tool presents the graph described in (ii).
   1. Some query templates, which can be imported to Neo4j, can be found in `neo4j_query_saved_cypher_2025-9-17.csv`.

