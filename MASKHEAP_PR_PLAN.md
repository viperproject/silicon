# Plan: maskHeapMode → master PR

Goal: merge `meilers_silicarbon_clean_claude` into master as a reviewable PR in which
(1) standard Silicon is provably unchanged when the option is off, and
(2) code — at least in the `rules` package — never branches on `Verifier.config.maskHeapMode()`;
mode-dependent behavior lives behind `v.heapSupporter` (and a function-encoding strategy).

Status quo: branch is 38 commits ahead of merge-base `c8e18fee`; master is 62 commits ahead
(23 touch src/main/scala); 24 files modified on both sides.

The invariant check used throughout: for a fixed set of representative .vpr files, standard-mode
prover output (`--proverLogFile`) must stay **byte-identical** across each refactoring step, and
identical to master's output after the merge (modulo master's own changes). This catch-all found
the MWSF-ordering and trigger-filter leaks; keep using it.

---

## Phase 0 — Baseline & bookkeeping (half a day)

- [x] All work committed (HEAD e6a7bb39).
- [ ] Record baselines on this branch: full standard `SiliconTests` result (user's machine),
      maskHeap incompleteness scan (currently: 1/137 = list_insert.vpr, pre-existing timeout),
      maskHeap key-file timings (lseg 3.9s, linkedlists 4.9s, hdt 4.1s, llqp ~25s, recursive_unrolling 3.6s).
- [ ] Pick a snapshot of ~10 standard-mode .vpr files + record their `--proverLogFile` output
      as the byte-identity reference set (include: a wand file, a QP file, a triggers file,
      a plain functions file).

## Phase 1 — Merge origin/master (1–3 days)

Do the merge **before** the cleanup refactor: the refactor moves code, and doing it first would
turn every master conflict into a conflict against moved code.

Textual conflicts expected in 24 files; the four *semantic* hotspots (details from PR descriptions):

1. **#995 Optional greedy QP algorithm** (Limbeck thesis; 838 changed lines in
   QuantifiedChunkSupport, plus HeapSupporter and StateConsolidator) — new `--exhaleModeQP`
   flag (default 1 = standard, greedy paths bypassed by default), and **new chunk fields**:
   quantified chunks gain `orgCondition` and `tag`, non-quantified chunks gain `tag`. The
   chunk-signature changes WILL conflict with `BasicMaskHeapChunk` / Chunks.scala changes —
   BasicMaskHeapChunk must implement the new members. Also: master now has a
   `SiliconTestsGreedyQP` suite (28 QP tests in pure greedy mode) — must stay green.
   Check whether the singletonRcvr Seq[Seq] issue from the old qp-greedy branch audit was
   fixed in the upstream version (a previous local merge, d29b77a0, silently dropped that
   fix — re-audit rather than trusting a clean textual merge).
2. **#985 Quantified wands using MWSFs** — replaces the pair-of-snaps QP-wand snapshot with a
   snap→snap function, parameterizing snapshot-map definitions by the LHS snapshot
   (`lookup(sm(lhs), r) == e(lhs)`), and adds a **new State field `packagingWandSnapshots`**.
   This rewrites exactly the `createWandChunkAndRecordResults` QP-wand branch
   (singletonSnapshotMap area) where the maskHeap branch substitutes a BasicMaskHeapChunk,
   and where our MWSF-ordering fix (dc4617fd) lives. Re-derive both on top of master's new
   structure; decide how maskHeap QP-wand snapshots interact with the new parameterization
   (maskHeap stores Combine(lhsSnap, rhsSnap) in a pred-heap — check whether the multiple-
   applications unsoundness #985 fixes can bite the maskHeap encoding too, since it shares
   the pair-of-snaps idea). Re-run the wand cluster in BOTH modes.
3. **#982 Preserve correct trigger terms after quantifier evaluation (incl. #980)** — fixes
   trigger terms being discarded during quantifier evaluation (issue #857). Overlaps our
   `evalHeapTrigger` Seq[Seq[Term]] restructure and `toTriggerForm`. Merge master's version
   as the base and re-apply the maskHeap additions around it.
4. **#940 Backend-independent counterexample format** (merged by Marco, Aug 2026 — own code) —
   SiliconRawCounterexample/SiliconResolvedCounterexample, big evaluateTerm extension, and
   notably: **QuantifiedChunkSupport avoids macros for permission terms when counterexamples
   are requested**. Interaction to check: maskHeap's `createAlias` tmpTerm macros should
   plausibly also be suppressed when CE extraction is on, or CE term evaluation will hit
   opaque macros (relates to the known QP term-eval gaps in maskHeap CE extraction).

Also: silver submodule — master's silver is ahead (many "Update silver submodule" commits);
the branch must build against master's silver commit. Any silver-side changes this branch
depends on need their own silver PR first (check: none known, but verify).

Exit criteria for Phase 1 (status 2026-08-20, merge commit 15844ced):
- [PENDING] standard `SiliconTests` green on Marco's machine (local 16-file leak set + spot
  checks all match annotations, incl. new #985 test cases);
- [DROPPED] byte-identity reference set (wiped by tmp cleanup; superseded by SiliconTests run);
- [DONE] maskHeap incompleteness scan: 0/137 — IMPROVED over pre-merge (list_insert.vpr's
  pre-existing timeout dissolved with the merge, now 6s);
- [DONE] linked-list-qp-append.vpr standard mode: fixed by master (#982), 8s (was >300s).
Known-issues register is now EMPTY on the maskHeap side.

## Phase 2 — Kill the mode branches (the bulk; ~1–2 weeks incremental)

Current inventory: ~50 explicit `maskHeapMode()` sites + ~28 implicit ones (matches on
`MaskMapTerm`/`HeapMapTerm`/`BasicMaskHeapChunk` outside MaskHeapSupporter). Ordered so each
step is independently shippable and byte-identity-checkable:

### 2a. Snapshot-format API on HeapSupportRules (biggest win, ~17 sites)
New methods (default impl = today's standard path, maskHeap impl = today's branch code):
- `unitSnapshot` (Consumer.unitTerm), `emptySnapshotAssumption` (Producer dead-branch sf===Unit),
- `adaptProduceSnapshot(sf, tlcs)` (Producer:142 HeapMapTerm conversion),
- `splitProduceSnapshot` (Producer:172),
- `unfoldBodySnapFunction(snap, predicate, tArgs)` (PredicateSupporter:247, Evaluator:765),
- `predicateTriggerArg(...)` incl. the pre-unfold-heap rule (PredicateSupporter fold/unfold,
  Evaluator:736) — keep the pre-unfold semantics from e6a7bb39,
- `functionCallSnapArgs(...)` (Evaluator:650),
- a `SnapshotAccumulator` object for Consumer.consumeTlcs replacing the resMap /
  `mergePreservingFirstOrder` / `isRecursive` threading (standard impl: Combine-fold;
  maskHeap impl: mask accumulation + convertToSnapshot at top level).
This step also dissolves most of the 28 implicit type-matches.

### 2b. Heap merging & wands (~8 sites)
- `heapSupporter.mergeHeaps(h1, h2, v, s)` — collapses MagicWandSupporter:562/593,
  Executor:580, and the `BasicMaskHeapChunk` case in State.mergeHeap.
- `heapSupporter.createWandChunk(...)` — packageWand chunk construction (both the QP-wand and
  plain branch), including the maskHeap PredHeapSort snapshot vs. MWSF choice; keeps the
  MWSF-creation-before-conservedPcs ordering explicit in the default impl.
- applyWand snapshot-lookup branch (MagicWandSupporter:500) → supporter hook.
- Executor:452 empty-heap assertions → `heapSupporter.assertStructure(s)` or just drop.

### 2c. Trigger evaluation (~4 sites)
- `heapSupporter.resourceTriggerTerms(ra, s, v)` for the two evalHeapTrigger cases;
- `heapSupporter.adaptTriggerTerms(terms, s)` for `toTriggerForm` (Evaluator:1407ff);
- Terms.scala `Quantification.apply` filter: Terms can't reach the verifier — either move the
  `isPossibleTrigger` filtering to the maskHeap trigger-construction sites (preferred: then
  Quantification.apply loses the config check entirely) or keep it as the one documented
  exception outside `rules`.

### 2d. Predicate infra (1 site)
- trigger-function signature sort (PredicateVerificationUnit:40) → `heapSupporter` or
  PredicateData factory parameter.

### 2e. Function encoding strategy (~20 sites, most invasive)
NOT heapSupporter material — introduce `FunctionEncoding` (Default vs MaskHeap) owned by
FunctionData, holding: snapArgs/arity, statelessVersion arity, frame/preconditionFrame/
qpFrame functions & axioms (incl. the predicateTriggers.nonEmpty gating), definitional-axiom
trigger construction (decoupled pattern + coverage fallback), transformToHeapVersion,
getFrameVersion. Folds in the branches in FunctionSupporter, FunctionVerificationUnit,
SymbolConverter.toFunction, ExpressionTranslator:176, HeapAccessReplacingExpressionTranslator:165.
The current `= null` members for the off-mode disappear.

### 2f. Final sweep
- grep gate: `maskHeapMode()` allowed only in Config, BaseVerifier (the dispatch),
  MaskHeapSupporter, MaskHeapFunctionsContributor, the FunctionEncoding factory, and (if kept)
  Terms.scala — everything else fails review. Add a comment at the dispatch site documenting
  the rule. Same grep for `MaskMapTerm|HeapMapTerm|BasicMaskHeapChunk` outside supporter files.

After each sub-step: build, byte-identity check (standard), key-file maskHeap set; full scans
at 2a, 2b/2c, 2e boundaries.

## Phase 3 — PR packaging (2–3 days)

- History: propose squashing into a small series of logical commits
  (1 merge, 1 maskHeap core, 1 function axiomatization, 1 supporter-API refactor, tests/docs);
  the 38-commit WIP history is not reviewable.
- CI/testing story: decide how maskHeapMode is tested upstream. Suggestion: a second
  SiliconTests instance (like SiliconTestsMoreJoins etc.) running with --maskHeapMode over a
  curated subset, with IgnoreFile-style exclusions for known-incomplete files. Known list:
  list_insert.vpr (timeout, also Carbon-ignored via issue 102).
- Docs: Config help text for --maskHeapMode; a design note covering the heap model, snapshot
  format (per-resource HeapToSnap trees, mask-on-consume/heap-on-produce), function
  axiomatization (heap args, frame/preconditionFrame, decoupled predicate triggers,
  pre-unfold trigger heaps, ext axiom role) — much of this exists in this week's session
  notes and can be distilled.
- Performance due diligence: standard-mode benchmark vs. master (expect zero delta — code
  paths identical; the refactor adds virtual dispatch only), plus a maskHeap-vs-standard
  table on the benchmark set for the PR description.
- Known-issues register in the PR description: list_insert timeout (maskHeap),
  any remaining standard-mode divergences (target: none).

## Decisions (resolved 2026-08-20)

1. Merge origin/master into THIS branch first; squashed PR branch cut from the result later.
2. heapSupporter API refactor = separate preparatory PR against master (pure refactor,
   byte-identical standard behavior); maskHeapMode PR lands on top.
3. maskHeapMode CI = curated subset suite, following the existing pattern
   (SiliconTestsGreedyQP / parallelizeBranches / moreCompleteExhale / oldPermSemantics).

## Scope simplifications (from Marco, 2026-08-20)

- **Counterexamples ∧ maskHeapMode: unsupported.** Config must reject --counterexample
  (mapped/raw/resolved) together with --maskHeapMode. Removes the #940 macro-suppression
  interaction entirely; maskHeap CE code paths can be left as-is or stripped.
- **Wand unification:** following #985's direction (non-quantified MWSF encoding used for
  everything), the maskHeap wand code should ALSO drop its quantified/non-quantified branch
  and use the non-quantified path for all wands. While doing this, check the identified
  soundness candidate: apply-time `snapLhs === First(lookup)` pinning may force two distinct
  LHS snapshots equal when the same wand is packaged twice and chunks are merged
  (MaskSum/MergeHeaps in Executor's package handling) — same bug class #985 fixed upstream.
  Write the targeted test (package same wand twice with different captured state, apply
  twice, try to derive false).
- **Greedy QP:** expected logically orthogonal (standard chunks + standard consolidation only,
  which maskHeapMode doesn't use). Merge work is then mechanical: BasicMaskHeapChunk
  implements the new `tag` member (and quantified-chunk changes don't apply); keep
  SiliconTestsGreedyQP green.
- **Completeness freeze:** current maskHeapMode completeness is accepted. Remaining
  incompletenesses (e.g. list_insert.vpr timeout) are excluded from the CI subset, not fixed.
  Unsoundnesses must still be fixed — note: the scans so far only checked the completeness
  direction (old-passes/new-fails). A soundness sweep = running the annotation-checking
  subset suite in maskHeapMode (expected errors must still be reported); building the CI
  subset suite doubles as this audit.
