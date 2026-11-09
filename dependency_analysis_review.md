# Dependency analysis branch: design review

**Scope:** main sources of Silicon and Silver on `keuscha/dependency_analysis_merge`, compared with `origin/master`. Tests, the test framework and Gobra are excluded.

| Repo | Reviewed commit | Base | Main-source diff |
|---|---|---|---|
| Silicon | `61588f57` | `ff386aec` | 90 files, +6048/−1031 |
| Silver | `f346c075` | `c4f54b84` | 11 files, +623/−182 |

**Method:** I read the code but ran nothing for this review. Nothing here has been reproduced, and suspected bugs are labelled as such. Links are relative to the Silicon root.

## Status

Updated on 2026-11-09, after the fixes on top of `e0fbd85b`. Line links in the files changed by these fixes have been updated, so they no longer match the reviewed commit. Sections that aren't listed here describe the code as reviewed.

| Items | Status |
|---|---|
| B2, B3, L4 | Fixed: `Config` rejects `SoftConstraints` and `maskHeapMode` together with the analysis. |
| B4 | Resolved: `createLabel` is deleted, so derived chunks always get a fresh label. |
| B6, L6 | **Not in this repo's history yet.** The fix is an uncommitted change in `viperserver/carbon/silver`. `silicon/silver` at `f346c075` still has `equals = false`. |
| L1 | Done. The scan remains when terms are given, see D6. |
| L2, L3 | Done. See the verification note below. |
| L5 | Partly done, see the L5 row. |
| L10, C8 | Done. |
| Everything else | Open. |

**Verification of L2, L3, L5, L10 and C8.** Old and new builds ran on the 61 programs in `dependencyAnalysisTests/{all,real-world-examples,verificationProgressTests,guidance}`, using `silicon/silver`:
- The output of `graphSize`, `progress` and `failures`, and of `dep` and `downDep` on every line, was identical once timings and paths were removed.
- Exported nodes were identical. Exported edges were identical except for the dangling edges described under L3.
- Every other CLI command, including interactive mode, gave identical output on `all/branches.vpr`. The exceptions are `benchmark` and `precisionEval`, which were not run because they need interactive prompts and a ground-truth folder.
- `DependencyAnalysisTests` passed, 61 of 61.

## Summary

The analysis is well separated at the class level, through the `DependencyAnalysisAware*` subclasses. It is much less separated in behaviour. These are the three problems I would address first:

1. An analysis run verifies a different problem than a normal run, and nothing checks that the two agree (D1).
2. Dead-path execution is spread across the rules as many small special cases (D2).
3. Several inputs that make the results wrong or incomplete are accepted with only a warning, or with no message at all (D5).

Most of the highest-value low-risk fixes are done. What remains is listed under [Low-risk improvements](#low-risk-improvements).

## Biggest design flaws

### D1. An analysis run is not the same verification as a normal run

With `--dependencyAnalysis`, Silicon changes what it sends to Z3 and which paths it explores:

- **Chunk permissions are rewritten.** They become `Ite(label, perm, NoPerm)` with a fresh label ([DependencyAnalyzer.scala:199](src/main/scala/dependencyAnalysis/DependencyAnalyzer.scala#L199), [:207](src/main/scala/dependencyAnalysis/DependencyAnalyzer.scala#L207)).
- **Known-true checks are weakened.** `isKnownToBeTrue` only accepts `True`, so the path-condition lookup is skipped ([DependencyAnalysisAwareDeciderProvider.scala:89](src/main/scala/decider/DependencyAnalysisAwareDeciderProvider.scala#L89)).
- **More fresh symbols are created.** Assignments are always made SSA ([Executor.scala:825](src/main/scala/rules/Executor.scala#L825)), and call arguments get fresh variables ([Executor.scala:646](src/main/scala/rules/Executor.scala#L646)).
- **Dead paths are explored,** unless `--disableInfeasiblePaths` is set (D2).

**Why it matters:** the graph describes the proof found in the instrumented run. Rules that inspect permission terms syntactically now see an `Ite`, and Z3 gets a different problem. A program could verify in one mode and fail or time out in the other, or the reported dependencies could differ from the proof a normal run finds. I haven't shown that this happens, but nothing rules it out.

**Suggested change:**
- Document this as a known property of the analysis, including which mode's verdict is authoritative.
- Compare verdicts between both modes on the existing Viper corpus, for example as a scheduled job.
- Record the reasoning for each instrumentation in one place, so each can be justified or removed individually.

**Risk:** the comparison and the documentation carry no risk to production code. Removing instrumentation carries high risk.

### D2. Dead-path handling is scattered through the symbolic execution rules

`Verifier.config.analyzeInfeasiblePaths` appears at 18 sites in `rules/`, plus `isPathMarkedInfeasible` guards and `handleInfeasiblePath` calls. Each site decides locally how to continue on a dead path, and they differ:

- `lookup` invents a fresh snapshot ([ChunkSupporter.scala:284](src/main/scala/rules/ChunkSupporter.scala#L284)).
- `consume` continues with `None` as the snapshot ([ChunkSupporter.scala:151](src/main/scala/rules/ChunkSupporter.scala#L151)). See B1.
- Quantifier evaluation invents a fresh variable ([Evaluator.scala:574](src/main/scala/rules/Evaluator.scala#L574)).
- Function-application joins filter entries by infeasibility node ([Evaluator.scala:1416](src/main/scala/rules/Evaluator.scala#L1416)).

**Why it matters:** this is the largest change to core rule logic, and it conflicts with any upstream change to those rules. A new rule that forgets the case stops exploring the path, and the dependencies of that path's obligations are then missing from the graph. The config comment itself says this mode may affect performance heavily and hasn't been tested without the analysis.

**Suggested change:** add one small abstraction with named operations, such as `deadPath.continueWithFreshSnapshot(...)`, `deadPath.continueWithoutResult(...)` and `deadPath.terminate(...)`. The default implementation would keep today's behaviour of stopping. The rules would then state *what* happens on a dead path, not *whether* the analysis is on.

**Risk:** medium. Doing it one rule at a time keeps each step reviewable.

### D3. Six overlapping on/off mechanisms

| Mechanism | Where |
|---|---|
| Subclass selection | [Silicon.scala:138](src/main/scala/Silicon.scala#L138) |
| Config checks in rules | `Verifier.config.dependencyAnalysis.isDefined`, 7 sites in `Executor` and `Brancher`, plus `FunctionData` |
| Null object per member | `NoDependencyAnalyzer`, chosen in `initDependencyAnalyzer` |
| Runtime query | `isDependencyAnalysisEnabled` |
| Flag inside the infos | `analysisEnabled`, combined with the config in `isAnalysisEnabled` |
| Pattern match on the decider | `decider match { case _: DependencyAnalysisHandler => ... }` in the `DependencyAnalyzer` object |

**Why it matters:** the mechanisms can disagree. If a member disables the analysis through its annotation, it still gets the weakened `isKnownToBeTrue`, the fresh-symbol encoding, dead-path exploration and the Z3-only prover. So a disabled member isn't verified the same way as in a normal run. `Joiner` and [MagicWandSupporter.scala:563](src/main/scala/rules/MagicWandSupporter.scala#L563) also use `DefaultInfos`, which is enabled by default, regardless of the member's setting.

**Suggested change:** define two explicit concepts: *analysis mode for the run* (decides the classes, set once) and *analysis active for this member* (a single query on the decider). Replace the config checks in the rules with named decider or policy queries such as `usesFreshCallArguments`. Decide and document what a disabled member should get.

**Risk:** low to medium. Moving each check is mechanical, but the member-level decision may change behaviour.

### D4. Silver annotates every AST, in every run, for every backend

[Translator.scala:198](silver/src/main/scala/viper/silver/parser/Translator.scala#L198) now wraps nearly every statement, and passes a dependency type through expression translation. `QuantifiedPermissions`, `Program` and `DecreasesCheck` are changed as well. This also runs when no analysis is requested, including for Carbon.

Layering is affected too:
- The generic rewriter now imports the ADT plugin ([Rewritable.scala:11](silver/src/main/scala/viper/silver/ast/utility/rewriter/Rewritable.scala#L11)), and special-cases its nodes in a `match` next to the `FuncApp` cases.
- `dependencyAnalysis` in core Silver imports the `refute` plugin ([DependencyAnalysisInfo.scala:14](silver/src/main/scala/viper/silver/dependencyAnalysis/DependencyAnalysisInfo.scala#L14)).

**Why it matters:**
- All users pay the memory cost, because each source info keeps a reference to its AST node.
- This is the hardest part of the branch to get accepted upstream, since a dependency-analysis concept enters Silver's parser translation.
- `attachMeta` builds each statement twice, which adds to the diff and the cost.

**Suggested change:** move the annotation into a separate pass over `ast.Program` that only runs when the analysis is enabled. Gobra already works this way, with `DependencyAnalysisAnnotationTransformer`. The pass can carry the dependency type down as context. For `Rewritable`, let nodes supply their extra metadata arguments through an overridable method, so plugin classes aren't named in the core.

**Risk:** medium. Viper-level results depend on these annotations, so the pass has to produce identical infos. Comparing exported graphs before and after would verify that.

### D5. Inputs that invalidate results fail silently

The code's own documentation says that a missing source info or dependency type "might" make the analysis unsound. Yet several cases fail without a hard error:

- **Missing infos only log a warning.** The node gets `"Unknown"` as its source and `AssumptionType.Unknown` as its type ([DependencyAnalysisInfos.scala:162](src/main/scala/dependencyAnalysis/DependencyAnalysisInfos.scala#L162)). By default, nodes sharing a source info also share a merge info, so unrelated `"Unknown"` nodes get connected.
- **Infos scoping is manual.** Since `analysisInfos` moved into `State`, each update site restores it by hand. A missed restore compiles, and neither `State.merge` nor `joiner.join` reports it.
- **Vacuous proofs are recorded and then lost.** `processUnsatCoreAndAddDependencies` records them, `getVacuousProofs` is `@unused` ([DependencyGraph.scala:194](src/main/scala/dependencyAnalysis/graph/DependencyGraph.scala#L194)), and `buildAndGetMergedGraph` doesn't copy them. A proof that only holds because of contradictory assumptions looks the same as a normal one.
- **Pruning compares file name and line only** ([DependencyAnalysisPruningSupporter.scala:25](src/main/scala/dependencyAnalysis/graphInterpretation/DependencyAnalysisPruningSupporter.scala#L25), [extractPositionString](silver/src/main/scala/viper/silver/dependencyAnalysis/DependencyAnalysisSourceInfo.scala#L14)). Two statements on the same line can't be told apart, and neither can files with the same name in different folders.

**Suggested change:** add a strict mode, on under `--enableDependencyAnalysisDebugging`, that turns missing infos into errors and asserts that the infos are restored in `eval`, `exec`, `produce` and `consume`. Decide what vacuous proofs mean for users.

**Risk:** low, since strict mode only affects debugging runs.

### D6. `DependencyGraph` has no indexes and only looks type-safe

[DependencyGraph.scala:117](src/main/scala/dependencyAnalysis/graph/DependencyGraph.scala#L117) is a mutable class with several weaknesses:

- **Redundant state:** `allEdges` must stay equal to the union of three other maps, which only a comment states ([:121](src/main/scala/dependencyAnalysis/graph/DependencyGraph.scala#L121)).
- **Weak phase markers:** `Init`, `IntraProcedural` and `Final` are phantom types, but all methods exist in every phase, and a cast changes the phase ([DependencyAnalyzer.scala:312](src/main/scala/dependencyAnalysis/DependencyAnalyzer.scala#L312)).
- **In-place building:** `buildFinalGraph` mutates the graph, so it can't safely be called twice.
- **Remaining linear scans:** L1 to L3 removed the worst costs, but `getNodeIdsByTerm` still scans all nodes whenever it is given terms, and `getNodes` rebuilds a set from both node maps on every call.
- **Deep keys:** source infos hold whole AST nodes and are used as `groupBy` keys, for example in `DependencyGraphJoiner`. Each lookup hashes and compares by those fields.

**Suggested change:** split the graph into a mutable builder used during verification and an immutable, indexed result with forward and reverse adjacency. Derive `allEdges` rather than storing it, and give source infos a stable, cheap key.

**Risk:** the split is medium risk, but its behaviour can be checked by comparing graph exports.

### D7. Tools and experiment code live in the verifier's main sources

- **In the production JAR:** `BenchmarkDependencyAnalysisCliExtension`, `TestDependencyAnalysisCliExtension`, `DebugDependencyAnalysisCliExtension` and `DependencyGraphTestSupporter`. `neo4j_importer.py` also sits in `src/main/scala`.
- **Verifier blocking on a terminal:** `afterVerification` runs the command tool, whose `interactive` command reads from the console ([DependencyAnalysisCliTool.scala:94](src/main/scala/dependencyAnalysis/cliTool/DependencyAnalysisCliTool.scala#L94)). If that option reaches a verifier hosted by a server, it would wait on stdin.
- **Results bypass the reporter:** the default console writes results to standard output rather than through `Reporter`, so server clients don't receive them. C8 makes the console replaceable, but no reporter-backed console exists yet.
- **A command language inside a config string:** `--dependencyAnalysis` takes commands such as `export>dir` and `computeGraphOnly`, parsed at run time. Invalid commands can't be rejected by `Config`.
- **An incomplete entry point:** `DependencyAnalysisTool.main` uses the placeholder name `"test"`, and its TODO says it "doesn't fully work yet".

**Suggested change:** separate *compute the graph* from *query the graph*. Silicon should compute it and hand it over through the reporter, while the CLI, benchmark and import tools move to a separate source set or module. Validate commands in `Config`.

**Risk:** low to medium. Mostly moving code, plus adjusting how options are parsed.

### D8. Base interfaces still carry analysis concepts

- `AnalysisInfos` is abstract, but its API names `DependencyAnalysisSourceInfo`, `DependencyType` and join and merge infos ([DependencyAnalysisInfos.scala:47](src/main/scala/dependencyAnalysis/DependencyAnalysisInfos.scala#L47)). Another analysis couldn't implement it meaningfully.
- 148 functions without a state still take the infos, including the entire `ChunkFactory`, whose default implementation ignores them.
- The graph result is attached to the verification result through a mutable field ([DependencyAnalysisAwareMethodVerificationUnitProvider.scala](src/main/scala/supporters/DependencyAnalysisAwareMethodVerificationUnitProvider.scala)).
- `PathConditionStack` holds analysis labels and infeasibility node IDs.
- `AssumptionType` is also used for assertion types, and assertion nodes store it in a field called `assumptionType` ([DependencyType.scala:95](silver/src/main/scala/viper/silver/dependencyAnalysis/DependencyType.scala#L95)).

**Suggested change:** don't aim for full separation, because the earlier discussion showed the decider argument has no cheap fix. Do rename `AssumptionType` to something neutral such as `DependencyKind`. Keep `AnalysisInfos` minimal or fold it back until a second analysis actually exists, so the abstraction isn't designed against one user.

**Risk:** the rename is low risk but touches many lines.

## Suspected bugs to confirm

None of these has been reproduced.

| ID | Issue | Effect | Suggested check or fix |
|---|---|---|---|
| B1 | On a newly detected dead path or with further errors, `consume` passes `None` as the snapshot even if `returnSnap` is true ([ChunkSupporter.scala:151](src/main/scala/rules/ChunkSupporter.scala#L151), [:163](src/main/scala/rules/ChunkSupporter.scala#L163)). Callers call `.get`, e.g. [Evaluator.scala:666](src/main/scala/rules/Evaluator.scala#L666), [PredicateSupporter.scala:85](src/main/scala/rules/PredicateSupporter.scala#L85) and [Executor.scala:683](src/main/scala/rules/Executor.scala#L683). | Possible `NoSuchElementException` while exploring a dead path | Test a function call or `fold` in a branch that becomes infeasible at that consume. Return a fresh snapshot when `returnSnap` is set, as `lookup` does. |
| B2 | **Fixed.** `--assertionMode SoftConstraints` wasn't rejected, but it doesn't name the goal or refresh the unsat core. | First assert throws a `NullPointerException`. Later asserts reuse an old core, giving wrong edges and false vacuous-proof records. | Reject the combination in `Config`. |
| B3 | **Fixed by rejecting the option.** `--maskHeapMode` wasn't rejected, but `createBasicMaskHeapChunk` adds no label ([DependencyAnalysisAwareChunkFactory.scala:113](src/main/scala/state/chunks/DependencyAnalysisAwareChunkFactory.scala#L113), `TODO ake`). `substitute` has a similar TODO. | Permission dependencies may be missing, which would make results incomplete | Reject the combination until it is supported, or add tests showing it's correct. |
| B4 | **Resolved by deleting the parameter.** `createLabel` was ignored in `registerDerivedChunk` ([DependencyAnalysisAwareDeciderProvider.scala:155](src/main/scala/decider/DependencyAnalysisAwareDeciderProvider.scala#L155)), so callers passing `createLabel = false` still get a fresh label and node. | Extra overhead at the least. It may not match what those callers intended. | Decide the intent, then implement it or delete the parameter (L5). |
| B5 | `getNodeIdsByTerm` finds source nodes by structural term equality across the whole member graph ([DependencyAnalyzer.scala:169](src/main/scala/dependencyAnalysis/DependencyAnalyzer.scala#L169)). | The same term assumed on another branch also becomes a dependency, which is imprecise rather than unsound | Check whether this appears in practice. |
| B6 | **Fixed only in the uncommitted `carbon/silver` working copy.** `NoDependencyAnalysisSourceInfo.equals` is always false, even for the same object ([DependencyAnalysisSourceInfo.scala:71](silver/src/main/scala/viper/silver/dependencyAnalysis/DependencyAnalysisSourceInfo.scala#L71)). | Breaks the `equals` contract for a value used in sets and `groupBy` keys | Make it a plain class with identity equality (L6). |
| B7 | `DecreasesCheck` now gives generated nodes a source position and info instead of the defaults, in all runs ([DecreasesCheck.scala:90](silver/src/main/scala/viper/silver/plugin/standard/termination/transformation/DecreasesCheck.scala#L90)). | Could change termination error locations outside the analysis | Compare termination error output with master. |

## Low-risk improvements

Listed in the order I'd do them.

| ID | Change | Where | Benefit |
|---|---|---|---|
| L1 | **Done.** Return early from `getNodeIdsByTerm` when `terms` is empty. Every chunk creation used to scan all nodes, even though `getOrCreateAnalysisLabelNode()` passes no terms. | [DependencyAnalyzer.scala:169](src/main/scala/dependencyAnalysis/DependencyAnalyzer.scala#L169) | Removes a likely quadratic cost during verification |
| L2 | **Done.** In graph queries, track queued nodes in a mutable set rather than `queue.toSet`, compute infeasibility IDs once, and avoid `toMap` copies of the edges. Build a reverse index for dependents instead of scanning all edges per layer. | [computeDependencies](src/main/scala/dependencyAnalysis/graph/DependencyGraph.scala#L279), [computeDependents](src/main/scala/dependencyAnalysis/graph/DependencyGraph.scala#L313), [getDirectDependenciesInternal](src/main/scala/dependencyAnalysis/graph/DependencyGraph.scala#L297), `DependencyGraphJoiner` | Faster queries, same results |
| L3 | **Done,** for label and internal nodes. Remove nodes in one batch rather than scanning all four edge maps per node. One intended difference: when removed nodes form a cycle, the old code could leave edges pointing at already deleted nodes, and these are gone now (32 edges across 7 of the 61 test programs). Dependencies between remaining nodes are unchanged. | [removeAllEdgesForNodes](src/main/scala/dependencyAnalysis/graph/DependencyGraph.scala#L339) | Faster graph finalisation |
| L4 | **Done.** Add `validateOpt` checks for `SoftConstraints` and `maskHeapMode` with the analysis. | [Config.scala:894](src/main/scala/Config.scala#L894) | Clear error instead of wrong results (B2, B3) |
| L5 | **Partly done.** `createLabel` and the `sourceChunks` parameters of `registerInhaleChunk` and `registerExhaleChunk` are gone. `registerDerivedChunk` keeps `sourceChunks` because the B4 fix passes it to `getOrCreateAnalysisLabelNode`, but `createLabelNode` ignores it, so it still has no effect. Either link labels to their source chunks in `createLabelNode`, or remove the parameter along the whole path, where `registerDerivedChunk` then duplicates `registerChunk`. | [DependencyAnalyzer.scala:33](src/main/scala/dependencyAnalysis/DependencyAnalyzer.scala#L33), [DependencyAnalysisAwareDeciderProvider.scala:28](src/main/scala/decider/DependencyAnalysisAwareDeciderProvider.scala#L28) | Signatures stop implying tracking that doesn't happen |
| L6 | **Fixed only in the uncommitted `carbon/silver` working copy** (see B6). Fix `NoDependencyAnalysisSourceInfo` equality. | [DependencyAnalysisSourceInfo.scala:71](silver/src/main/scala/viper/silver/dependencyAnalysis/DependencyAnalysisSourceInfo.scala#L71) | Correct contract (B6) |
| L7 | Use one parameter order for `getAllEdges`. The trait says upward then downward, while the class says downward then upward. All current callers are inside the class, so nothing is wrong yet. | [DependencyGraph.scala:73](src/main/scala/dependencyAnalysis/graph/DependencyGraph.scala#L73), [:145](src/main/scala/dependencyAnalysis/graph/DependencyGraph.scala#L145) | Prevents a future swapped-flag bug |
| L8 | Keep one infeasibility accessor on the path condition stack (`infeasibilityNodeId` and `getCurrentInfeasibilityNode` duplicate each other) and fix `Option[Mark]`, which should be `Option[Int]`. | [PathConditions.scala:543](src/main/scala/decider/PathConditions.scala#L543), [:661](src/main/scala/decider/PathConditions.scala#L661) | Removes duplication and a misleading type |
| L9 | Either surface vacuous proofs or delete the tracking. | [DependencyGraph.scala:194](src/main/scala/dependencyAnalysis/graph/DependencyGraph.scala#L194) | No more data that's collected and lost |
| L10 | **Done.** Add `DependencyAnalyzer.isAnalysisLabel(v: Var)` and use it instead of matching the name prefix. This covers both sites, including the function verification unit provider. | [FunctionData.scala:212](src/main/scala/supporters/functions/FunctionData.scala#L212) | One definition of what a label is |
| L11 | Correct the docs: the scaladoc says all merge infos are propagated, but `getMergeInfo` uses only the head. | [DependencyAnalysisInfos.scala:90](src/main/scala/dependencyAnalysis/DependencyAnalysisInfos.scala#L90), [:190](src/main/scala/dependencyAnalysis/DependencyAnalysisInfos.scala#L190) | Docs match behaviour |
| L12 | Add a helper for the repeated failed-assertion pattern, after checking that the 33 `handleFailedAssertion` sites fit it. | `SymbolicExecutionRules` | Less duplicated logic and fewer infos arguments |
| L13 | Revert unrelated import reordering in upstream files, such as `Config`, `DefaultMainVerifier`, `Ast`, `Program` and `CfgGenerator`. | Several | Smaller diff, fewer merge conflicts |
| L14 | Move `neo4j_importer.py` out of `src/main/scala`, for example to `scripts/`. | [neo4j_importer.py](src/main/scala/dependencyAnalysis/neo4j_importer.py) | Cleaner source tree |
| L15 | Resolve the open `TODO ake` and `XXX ake` comments, 27 in Silicon including test files. Start with those that question behaviour: "why do we need this?" ([DependencyAnalyzer.scala:331](src/main/scala/dependencyAnalysis/DependencyAnalyzer.scala#L331)), the mask heap TODOs, and the `DefaultInfos` use at [MagicWandSupporter.scala:563](src/main/scala/rules/MagicWandSupporter.scala#L563). | Several | Exposes undecided behaviour before merging |

## Class structure and decoupling of the analysis code

This section looks only at analysis-specific code: `dependencyAnalysis/`, the `DependencyAnalysisAware*` classes in Silicon, and `viper.silver.dependencyAnalysis`.

**Verdict: the split is good at the package level, but only partly good at the class level, and decoupling is incomplete.** The packages name sensible areas, but several central classes have too many jobs, and the base code still reaches the analysis through downcasts and global state.

**What already works well:**
- The packages `graph`, `graphInterpretation` and `cliTool` separate the graph, its queries and its tools.
- `DependencyAnalysisAware*` subclasses add behaviour through overrides, and the recent prover and decider refactors keep labels out of the base classes.
- `ReadOnlyDependencyGraph` gives consumers a read-only view of the graph.
- `DependencyNodeFactory` is the single place that assigns node IDs and applies the `assertOnly` filter.
- The Silver info types (`DependencyTypeInfo`, the join and merge infos, source infos) are small and focused.

### C1. `DependencyAnalyzer` does too many jobs

[DependencyAnalyzer.scala](src/main/scala/dependencyAnalysis/DependencyAnalyzer.scala) combines:

| Job | Examples |
|---|---|
| SMT label encoding and decoding | `createAssumptionLabel`, `getIdFromLabel` |
| Annotation parsing | `extractEnableAnalysisFromInfo` |
| Static dispatch on the decider | `addAssumption`, `wrapWithDependencyAnalysisLabel` |
| Recording nodes during verification | `addAssumption`, `createLabelNode` |
| Building instrumented chunks | `registerInhaleChunk` and `registerExhaleChunk` build the `Ite` term |
| Interpreting unsat cores | `processUnsatCoreAndAddDependencies` |
| Finalising the graph | `buildFinalGraph`, `buildAndGetMergedGraph`, `addTransitiveEdges` |

The interface is also too wide for its users:
- `NoDependencyAnalyzer` needs a no-op for every method, invents a fake method for `getMember`, and still allocates a graph because the trait holds one ([:21](src/main/scala/dependencyAnalysis/DependencyAnalyzer.scala#L21)).
- The preamble analyzer is `new DefaultDependencyAnalyzer(None)` ([DependencyAnalysisAwareZ3ProverStdIO.scala:43](src/main/scala/decider/DependencyAnalysisAwareZ3ProverStdIO.scala#L43)), so `getMember`, which calls `member.get`, would throw if used there. Only the axiom methods are safe, which the types don't express.

**Proposed split:**
- `SmtLabels`: encoding and decoding of labels.
- `DependencyRecorder`: the small trait the decider writes to, with a no-op implementation.
- `PreambleAxiomRecorder`: axioms only, with no member.
- `ChunkInstrumentation`: the `Ite` wrapping, used by the chunk factory.
- `IntraproceduralGraphBuilder`: a function from the recorded graph to the finished graph, which also fixes the mutation in D6.

**Risk:** medium, though it's mostly moving code. Start with `SmtLabels` and the graph builder, which are independent.

### C2. `DependencyGraph` mixes storage, algorithms and file formats

[DependencyGraph.scala](src/main/scala/dependencyAnalysis/graph/DependencyGraph.scala) holds the data, every traversal and the CSV export. The format is therefore defined twice: written in `exportNodes` and read by column number in [DependencyGraphImporter.scala](src/main/scala/dependencyAnalysis/cliTool/DependencyGraphImporter.scala). Export is also on `ReadOnlyDependencyGraph`, so the query interface includes file output.

Nodes are tied to the symbolic execution engine through `Term` and `Chunk`. The importer shows the cost: it creates a `dummyVar` and placeholder terms only to satisfy the constructors. The code's own comments say `term` is "only used for debugging", and that the chunk and label on permission nodes are "not strictly needed anymore". `getNodeIdsByTerm` is the exception, since it does use `term`.

**Proposed change:**
- Keep storage in `DependencyGraph` and move traversals to `DependencyGraphQueries`.
- Put reading and writing in one `DependencyGraphCsv` object, so the format has a single definition.
- Make low-level data optional, for example `debugInfo: Option[NodeDebugInfo]` on nodes, once `getNodeIdsByTerm` no longer needs it or uses a separate lookup kept by the recorder.

**Risk:** low for the CSV move, medium for the node change.

### C3. `DependencyGraphInterpreter` is a catch-all, with circular references

[DependencyGraphInterpreter.scala](src/main/scala/dependencyAnalysis/graphInterpretation/DependencyGraphInterpreter.scala) answers queries, filters nodes, exports files, computes join candidates and creates its own helpers:

- **Circular references:** it creates `DependencyAnalysisPruningSupporter(this)` and `DependencyAnalysisProgressSupporter(this)` in its constructor, and both call back into it.
- **Mixed phases:** its own TODO says join candidates are only needed for intraprocedural graphs, yet every instance computes them. The type parameter `T` doesn't stop anyone calling a final-graph operation on an intraprocedural interpreter.
- **Test code in production:** `DependencyGraphTestSupporter` lives in the same package.
- **Hard-to-read naming:** the progress results are called `Peter` and `Lea` in the CLI and its export. Descriptive names would explain the two measures.

**Proposed change:**
- Split it into `IntraproceduralGraphResult` (graph, errors, member, join candidates) and `FinalGraphQueries` (user-level queries).
- Make pruning and progress standalone classes that take `FinalGraphQueries` as a parameter, and let callers create them.
- Move the test supporter to the test sources.

**Risk:** low to medium, and the compiler will find all callers.

### C4. Dependencies point the wrong way

- **Package cycle:** `dependencyAnalysis` imports `decider` to match on `DependencyAnalysisHandler` ([DependencyAnalyzer.scala:9](src/main/scala/dependencyAnalysis/DependencyAnalyzer.scala#L9)), and `decider` imports `dependencyAnalysis`.
- **Value object with global dependencies:** `DependencyAnalysisInfos` reads `Verifier.config` and logs through `SiliconRunner.logger` ([DependencyAnalysisInfos.scala:102](src/main/scala/dependencyAnalysis/DependencyAnalysisInfos.scala#L102), [:168](src/main/scala/dependencyAnalysis/DependencyAnalysisInfos.scala#L168)). A data class therefore depends on the command-line runner and can't be used without global setup.
- **Global config in algorithms:** `DependencyGraphJoiner` ([:71](src/main/scala/dependencyAnalysis/DependencyGraphJoiner.scala#L71)) and `buildFinalGraph` ([DependencyAnalyzer.scala:312](src/main/scala/dependencyAnalysis/DependencyAnalyzer.scala#L312)) read `Verifier.config` directly. They could be plain, independently testable functions.
- **Verifier calls a tool:** `afterVerification` calls `DependencyAnalysisTool` ([DependencyAnalysisAwareVerifier.scala](src/main/scala/verifier/DependencyAnalysisAwareVerifier.scala)), so the verifier depends on the CLI package. See D7.

**Proposed change:**
- Pass settings explicitly, using a small `DependencyAnalysisOptions` created once from `Config`.
- Remove logging from `DependencyAnalysisInfos`. Getters could report a missing source info through the recorder, or an `Option` result could leave the decision to the caller.
- Let `analysisEnabled` alone decide. For that, `DefaultInfos` must start disabled and be enabled explicitly, because it's currently enabled by default (see D3).
- Keep a one-way dependency: base code depends on an interface, and `dependencyAnalysis` implements it.

**Risk:** low for passing options. Changing `DefaultInfos` needs care, because a few sites rely on the default being enabled.

### C5. Base code reaches the analysis through downcasts

Rules use static helpers that pattern-match on the decider. The counts below cover `rules`, `supporters`, `resources`, `state`, `decider` and `verifier`:

| Helper | Uses |
|---|---|
| `handleAndGetUpdatedAnalysisInfos` | 10 |
| `wrapWithDependencyAnalysisLabel` | 8 |
| `addCustomDependenciesBetweenMergeInfos` | 3 |

Provers and verifiers have similar checks: [Domains.scala:130](src/main/scala/supporters/Domains.scala#L130), [DependencyAnalysisAwareFunctionVerificationUnitProvider.scala:59](src/main/scala/supporters/functions/DependencyAnalysisAwareFunctionVerificationUnitProvider.scala#L59), [DependencyAnalysisAwareVerificationPoolManager.scala:18](src/main/scala/verifier/DependencyAnalysisAwareVerificationPoolManager.scala#L18) and [DependencyAnalysisAwareVerifier.scala:52](src/main/scala/verifier/DependencyAnalysisAwareVerifier.scala#L52).

Also, `handleAndGetUpdatedAnalysisInfos` both computes a value and adds nodes as a side effect, which its name only partly suggests.

**Proposed change:** replace the matches with one interface on the decider, with a no-op default and an analysis implementation:

```scala
trait AnalysisHooks {
  def enterNode(infos: AnalysisInfos, info: ast.Info, node: ast.Node): AnalysisInfos
  def withLabel(term: Term, sourceTerms: Iterable[Term]): Term
  def linkMergeInfos(sources: Seq[ast.Exp], targets: Seq[ast.Exp]): Unit
}
```

For axioms, give `ProverLike` an overridable method that takes the axiom infos and ignores them by default, so `Domains` no longer needs a match. Where the concrete type is known, as in the verifier classes, a type member could replace the casts, the same way `type P` replaced them in the decider.

**Risk:** low. The change is mechanical and the compiler checks it, while behaviour stays the same.

### C6. `DependencyAnalysisHandler` and the chunk factory are tied to the decider

[`DependencyAnalysisHandler`](src/main/scala/decider/DependencyAnalysisAwareDeciderProvider.scala#L19) combines three roles: analyzer lifecycle, chunk registration and label creation. `DependencyAnalysisAwareChunkFactory` then needs a whole `Decider with DependencyAnalysisHandler` ([:20](src/main/scala/state/chunks/DependencyAnalysisAwareChunkFactory.scala#L20)), although it only registers chunks. Similarly, `DependencyAnalysisProverHandler` mixes prover forwarding with owning an analyzer, and it lives in the Z3 prover's file.

**Proposed change:**
- Split the handler into an analyzer lifecycle part and a `ChunkInstrumentation` part from C1.
- Give the chunk factory only `ChunkInstrumentation`.
- Move the prover trait to its own file, using `PreambleAxiomRecorder` from C1 for the node storage.

**Risk:** low.

### C7. Node classes repeat the same fields, and results are returned through a mutable reporter

- **Repeated parameters:** every node class takes `sourceInfo`, `assumptionType`, `mergeInfo`, `joinInfos` and `memberStr`. Every analyzer method extracts the same values from `AnalysisInfos`.
- **Type checks:** `isInstanceOf` and `getNodeType` strings decide behaviour in the graph, analyzer and importer. `DependencyAnalysisNode` also isn't `sealed`, so the compiler can't check that matches are complete.
- **Duplicate work in the providers:** the method and function providers share nearly identical pre-node and result-building code ([method provider](src/main/scala/supporters/DependencyAnalysisAwareMethodVerificationUnitProvider.scala), [function provider](src/main/scala/supporters/functions/DependencyAnalysisAwareFunctionVerificationUnitProvider.scala)).
- **Results via downcast:** `afterVerification` matches on [`DependencyAnalysisReporter`](src/main/scala/dependencyAnalysis/DependencyAnalysisReporter.scala) and sets a mutable field. That reporter ignores all messages and has an unused `path` parameter.
- **Placeholder join type:** `EvalStackDependencyAnalysisJoin` is a join info whose `matches` always throws `sys.error`, because it must be resolved first. Unresolved and resolved joins would be safer as separate types.
- **Small duplicate:** `toSourceSet` and `toSourceMemberSet` are identical in [UserLevelDependencyAnalysisNode.scala](src/main/scala/dependencyAnalysis/UserLevelDependencyAnalysisNode.scala).

**Proposed change:**
- Add `NodeMetadata(sourceInfo, kind, mergeInfo, joinInfos, member)`, built in one place from `AnalysisInfos`.
- Seal the node hierarchy and use pattern matching or properties rather than strings.
- Extract one helper for the shared provider code.
- Report the final graph through a `viper.silver.reporter.Message`, so any reporter can receive it.

**Risk:** low to medium. `NodeMetadata` touches all node classes but is mechanical.

### C8. The CLI has two command systems (done)

**Implemented:**
- Every command is now a `DependencyAnalysisCliCommand`. [DependencyAnalysisCliTool.scala](src/main/scala/dependencyAnalysis/cliTool/DependencyAnalysisCliTool.scala) receives the commands and extensions through its constructor, and `DependencyAnalysisCliTool.apply` assembles the default set.
- The core commands live in [CoreDependencyAnalysisCliCommands.scala](src/main/scala/dependencyAnalysis/cliTool/CoreDependencyAnalysisCliCommands.scala).
- `DependencyAnalysisCliSupport` replaces the helper inheritance.
- Commands return a `DependencyAnalysisCliResult`, which `DependencyAnalysisCliConsole` writes out.

- The pruning, progress and test supporters report through a function they are given, so all CLI output goes through the console or a command result. `DependencyAnalysisCliTool.runCommands` handles command lists.

`benchmark`, `precisionEval` and the test commands write to the console while they run, by design: they prompt for input, report progress, or may fail with an assertion after reporting findings. The supporters default to `println` where tests call them directly.

Not verified by running: this step was compiled only.

### Target structure

```text
silver.dependencyAnalysis        Info types only: source, merge, join, kinds
silicon.dependencyAnalysis
  AnalysisHooks                  Interface used by base code, with a no-op default
  DependencyAnalysisOptions      Settings, created once from Config
  recording/                     DependencyRecorder, PreambleAxiomRecorder, ChunkInstrumentation, SmtLabels
  graph/                         Sealed nodes, NodeMetadata, DependencyGraph
  building/                      IntraproceduralGraphBuilder, DependencyGraphJoiner
  query/                         FinalGraphQueries, progress, pruning
  io/                            DependencyGraphCsv, graph result message
tools (separate source set)      CLI, benchmark, import
```

Dependencies should point in one direction: `tools` → `query` → `graph`, and `recording` → `graph`. Base code should know only `AnalysisHooks` and `AnalysisInfos`, while the `DependencyAnalysisAware*` classes connect the two sides.

### Suggested order for these changes

| Step | Changes | Why this order |
|---|---|---|
| 1 | C5 `AnalysisHooks`, C4 options | Removes the downcasts and the package cycle without changing behaviour, and the rest becomes easier to move |
| 2 | C1 `SmtLabels` and graph builder, C2 CSV object | Independent extractions with little risk |
| 3 | C3 interpreter split | Prepares the tool separation in D7 |
| 4 | C1 remaining split, C6 | Depends on the hooks from step 1 |
| 5 | C7 `NodeMetadata`, optional debug data from C2 | Touches the most classes, and is easier once the code has moved |

## Suggested order

1. **Confirm bugs:** check B1, then B7. Commit the B6 fix to Silver.
2. **Safe fixes:** finish L5, then L7 and L8. Each is small, and the existing tests cover most of the behaviour.
3. **Cleanup:** L9 and L11 to L15.
4. **Before proposing upstream:** D4 and D7, which change the most for people outside this feature.
5. **Larger refactors:** D3, D2 and D6, one at a time. Compare graph exports before and after, so that any behaviour change is visible.
6. **Ongoing:** the D1 comparison and the D5 strict mode, which make all of the above safer. They're cheap enough to start early.



