# Verification status

Native corollaries are native for CPU rows only. Cached CPU certificates supply
CPU equations and decoder lookup; bigint, extended-round, G and special5 worker
equations remain no-cache flat-constraint premises. Split Keccak uses direct
imported worker constraints and source setup certificates, with no compiler capture.
Compiler preservation covers 11 cached compilations.

All three targets currently cover one initialization/teardown instance, with
several windows allowed within that instance. Rust accepts several such instances
and checks distinct windows across the concatenated list; that aggregation is
not covered. Generalizing the boundary and boot-seed proof to a list remains
pending. `workerFamilies` and absent split pools restrict submitted circuit
instances; they are not derived solely from public program no-call premises.

## Proofs

All three machine targets are proved.
Their definitions stay unchanged. Cached Review claims remain.
Uncached-only Review cases and statements are removed with user approval.
The split Keccak source certificates are proved.
Exact lookup, request and RAM premises stay explicit.
The verified base is `c1a662222cafcd96db4383dce737edb79fa62b09`.
Production functions match the base. Only additive artifact exports and their
required serialization derives remain outside the formal model and CI.
The initialization-window defect is fixed upstream by #548 in this base. The
redundant branch-only repair is removed; see [FINDINGS.md](FINDINGS.md).

## Current checkpoint

The 4 November specification review makes the existing one-instance
initialization and submitted-pool premises explicit. Native corollaries certify
CPU rows only; standard worker equations remain no-cache flat constraints and
split workers have no compiler capture. A new Review statement forwards the
existing 361-call native split permutation theorem without changing its premises.
Current-guide links/anchors, workflow export lists and replay-stack settings pass
static checks. The wrapper and current source tree still require Lean CI validation.


The 4 November production-scope cleanup restores every existing production
function to the base. A static diff audit checks exact restored bytes, unchanged
setup bodies and serialization-only derives. Exporter formatting passes.
The ten native source receipt mismatches from cleanup were requalified by
run [41832547126](https://github.com/matter-labs/zksync-airbender/actions/runs/41832547126)
on `6c53a9a1201b579bebd341f29866d87da6d528c4`: all twelve exact native
generators, sixteen complete setup comparisons and scoped dep-info checks passed.
The setup manifest is the exact downloaded qualified manifest, SHA-256
`20f680f0a08551ad3f1a3674686988f7fcac53ebec4117c8bdaea75bb53cad3e`.
All 28 execution receipt hashes and all sixteen downloaded payloads were checked.
Compiler receipt requalification also passed in that run: all 33 payload files
reproduced byte for byte and all eleven retained cached native identities passed.
The exact downloaded compiler manifest's SHA-256 is
`ba55c93d53f3a689abccf6b628331f9df07ea8c779e3595f0efce04db914df71`.
Both exact verified manifests pass their strict checkers locally. Current Lean
validation and final full assurance remain pending.
No full FV result qualifies this cleanup yet.

Warm run [41815044934](https://github.com/matter-labs/zksync-airbender/actions/runs/41815044934)
passed preflight and bootstrap, then failed on the known stale native source
receipts. Explicit setup requalification now prepares an unqualified snapshot,
keeps the retained manifest unchanged during native work, and promotes source
pins only after all 28 native jobs, complete payload comparisons and dep-info
coverage pass. The workflow also uses the decoder smoke test's current module.
These requalification changes initially passed 47 lightweight tests. The actual
native re-export has now passed in the run above; current proof validation remains pending.

Run [41818079338](https://github.com/matter-labs/zksync-airbender/actions/runs/41818079338)
passed five native circuit comparisons and then hit the footprint limit in the
subword generator. The attempted chunked adapter then failed complete circuit
identity in [41823630219](https://github.com/matter-labs/zksync-airbender/actions/runs/41823630219):
its cleared content index made native table sizes zero. That adapter and its
example are removed; original native constructors and all twelve exact generator
tests are restored. Production functions remain at the base.

Native artifact, compiler-capture and mixed decoder-data jobs now use a separate
explicit 8,192 / 12,288 MiB memory profile, with the same 900-second limit and
single-worker lock. A per-job Linux capacity check requires 14 GiB effective
capacity/available memory, including cgroup hard limits and reclaimable file
cache. Lean source, proof audits and kernel replay retain 2,560 / 5,120 MiB limits.
Native reconstruction runs before Lean cache restore. Ninety-three focused
Python guard/provenance/preflight controls pass. Complete setup equality is now
qualified, as are the compiler input receipts after exact payload reproduction.
No full FV result qualifies the current proof revision.

Run [41832547126](https://github.com/matter-labs/zksync-airbender/actions/runs/41832547126)
later failed in `Proofs/UnifiedReduced/WindowProjection.lean`: the local names
`parts` (line 88) and `start` (line 109) collided with imported parser tokens.
The failed build exited in 4.96 seconds at 411.79 MiB charged footprint.
Those names and the same local binding patterns in the remaining private proofs
are now quoted. Normalizing identifier quotes gives exactly the previous source;
Review files, theorem names, production code and qualified artifact manifests
are unchanged. This syntax repair still requires Lean CI validation.

Run [41846991839](https://github.com/matter-labs/zksync-airbender/actions/runs/41846991839)
on `5141cfccce167f536bea4b99f385a2783f295ce5` passed native reconstruction,
compiler capture and bootstrap, then rejected an ordinary `start` parameter in
`Proofs/UnifiedReduced/SupportedUsePrefix.lean:18`. The earlier binding-pattern
scan missed ordinary parameters. The repair now quotes every remaining bare
`start` and `parts` code identifier in private proofs opening the affected Sail
namespaces: 130 occurrences across seventeen files. Quote-normalized source is
identical; Review statements and qualified artifacts are unchanged. The guarded
failure took 5.76 seconds at 441.29 MiB charged footprint. Diagnostic upload ran
before cache saving as intended. This wider syntax repair requires Lean CI;
the environment/axiom audit and final full assurance remain pending.

Run [41853518121](https://github.com/matter-labs/zksync-airbender/actions/runs/41853518121)
on `c4eb40e66` passed native setup/compiler checks, then failed in
`Tests/BigintMemory.lean:63`: constructed timestamp triples started at 217 instead
of the native column 216. Borrow bits and predecessor clocks were shifted by one.
The same fixture offset is corrected in `DelegationTimestamps` and
`DynamicCopyLoopNative`. The failing leaf took 31.44 seconds at 608.83 MiB charged
footprint; the source stage had run for 116 minutes before reaching it. CI now
frontloads these three actual Lean fixtures through the existing guarded frontend
before the complete source/runtime traversal. Review statements, production code,
artifact manifests and all resource/trust limits are unchanged. Current fixture
validation, the environment/axiom audit and final full assurance remain pending.

Run [41877076050](https://github.com/matter-labs/zksync-airbender/actions/runs/41877076050)
on `0400e0f36` passed the corrected `BigintMemory` and `DelegationTimestamps`
modules. The early fixture phase then found obsolete CPU auxiliary-column
assignments in `DynamicCopyLoopNative`: six equation checks and subsequent
lookup/clock checks failed. The COPY and Path-G candidate assignments are corrected
against the native column names and pooled definitions; Path-G native acceptance
is added to the early scoped check. A supplementary source-parsed audit passes
all sixteen COPY rows' native equations, ranges, timestamps and eighty complete
pooled queries against retained native setup data. This does not replace Lean
validation. Review statements, production behavior, artifacts and all trust and
resource limits are unchanged. Full source/runtime validation, the environment
audit and final full assurance remain pending.

Run [41882490544](https://github.com/matter-labs/zksync-airbender/actions/runs/41882490544)
on `e94380e9f` passed the corrected COPY native-acceptance fixture, then failed
at `PathGLoopNativeBase.lean:262:49` on an unquoted `start` parameter. Remaining
test identifiers are quoted, with actual macro keywords preserved. Static review
also found stale 129-equation Path-G certificate bounds; the native list has 120.
The repaired chunks cover exactly indices 0–119 across all 41 finite groups,
retaining the complete imported-list conclusion. No Review statement, production
function, native artifact, resource limit or trust gate changes. Path-G/full
source validation, the environment audit and final full assurance remain pending.

Run [41887174299](https://github.com/matter-labs/zksync-airbender/actions/runs/41887174299)
on `1daf1d67e` passed `PathGLoopNativeBase`, then failed at
`PathGLoopCPU/Shared.lean:44:34` on the separate reserved identifier `stop`.
Its 93 remaining identifier uses in fifteen certificate files are now quoted;
the real macro keyword remains. These are byte-identical source edits after
quote normalization. The 120 native equations and every Review premise, resource
limit and trust gate are unchanged. Remaining Path-G/full source validation,
the environment audit and final full assurance are still pending.

Run [41891337613](https://github.com/matter-labs/zksync-airbender/actions/runs/41891337613)
on `fd7c0fee5` passed `Tests.PathGLoopCPU.Equations`: all 120 native CPU equations
for 228 rows and three variants are checked. It then failed in the query helpers
at `PathGLoopNativeQueries.lean:195:4`, which still referenced old auxiliary
positions. The thirteen range coordinates, five pooled support/stencil regions
and three timestamp-borrow coordinates are aligned with the current native JSON
and corrected witness. Structural checks pin every range/support entry to that
JSON; the worker section is unchanged. No query, Review premise, production
behavior, artifact, resource limit or trust gate is removed or weakened. Complete
query/acceptance, source/runtime, environment and final full assurance validation
remain pending.

Run [41898007151](https://github.com/matter-labs/zksync-airbender/actions/runs/41898007151)
on `a99f6c4ce` typechecked the corrected query helpers and rejected only an
unused `notStore` simp argument at `PathGLoopNativeQueries.lean:305:77`.
The unused argument and its unused local proof are removed. CI now offers
explicit `diagnose_modules` selection for proof-only diagnosis with normal Lake
freshness and unchanged per-child guards. It skips native reconstruction and
the complete source/runtime, generated/decoder, environment/axiom and assurance
stages, reports that partial scope, and never uploads a large Lean cache.
It rejects combinations with assurance, cold-build, baseline-refresh and
requalification flags. This mode does not qualify the PR; standard warm
verification, the environment audit and final full assurance remain pending.

The connected delegation, comparison and control-preparation test witnesses
also used obsolete CPU auxiliaries. Eleven test files now use native borrow
columns 123–125, multiplication scratch 78, the pooled slots at 82–121 and
current comparison/control scratch positions. The wrapped-PC comparison keeps
the actual low-limb carry at 122. An independent source parser checked 84
representative constructed rows against every native equation, range/timestamp
query, port clock bound and complete pooled row in the retained setup JSON.
This is supplementary diagnosis, not Lean validation of their theorems. No
theorem, native constraint, Review statement, production function or artifact
is changed. The affected modules still require Lean CI.

The remaining arithmetic, memory, ROM, branch/jump, binary, shift and modular
execution examples had the same obsolete layout. Fifteen further test files
now use the native auxiliary positions; inline initialization/teardown fields
move from 134–141 to 126–133. Theorems and proof bodies are unchanged. A
supplementary source-parsed audit checks sixty additional rows against all
native equations and their applicable range/clock queries. Fixed pooled rows
are compared in full with the retained setup JSON; the three dynamic-ROM
examples instead check their explicit public words. Three core-only rows have
no clock-acceptance claim and receive no added one. Shift/bitwise helpers are
evaluated independently with their declared bit-vector semantics. These checks
do not replace Lean CI or final assurance.

Diagnosis [41905482598](https://github.com/matter-labs/zksync-airbender/actions/runs/41905482598)
on `a23f1aa01` failed at `ControlPreparationBase.lean:291:26`: a test still called
the removed public alias `prepared_round_masks_soundness`. It now calls the
existing `Caller.Proofs.prepared_round_masks` directly, with the same arguments,
premises and conclusion. The leaf exited 1 in 37.01 seconds at 917.14 MiB, with
no owned processes left. No resource or trust gate was involved. The repair
requires another Lean diagnosis; full verification and assurance are pending.

A declaration audit also found three obsolete public alias names used by
connected tests. Eight preparation proofs now compose their existing
`HashControlPreparation` source certificates with the current public
`hash_control_preparation_soundness` theorem. Two caller-cycle tests call the
existing `Caller.Proofs.caller_cycles` theorem with their original arguments.
The test statements, acceptance/initialization/alignment premises and Review
API remain unchanged. These proof applications await Lean CI validation.
`Tests.NativeCPUFixtures` now imports the complete affected CPU test set and
its dependencies for one selected-module diagnosis. It adds no statements or
assumptions and does not replace full verification or assurance.

The finite certificate audit also found the old 129-equation bounds in
`AirbenderUnifiedNative` and `PathGConsumedMessage.Core`. Their chunks now cover
exactly native indices 0–119, with eight equations in the last chunk. Only the
obsolete outside-domain 128 certificates are removed; the full imported-list
conclusions remain unchanged. The consumed-message store's word-address scratch
moves from 78 to native 74. The fixture gate now includes this derivative.
Four lightweight inventory controls compare bounds and interval coverage with
the native JSON, including missing/overlapping/outside-domain negative controls.
CI runs them before toolchain and native work. Lean validation remains pending.

Diagnosis [41909111177](https://github.com/matter-labs/zksync-airbender/actions/runs/41909111177)
on `6dba399d9` compiled the corrected native program certificates and Path-G
acceptance, then failed in the consumed-message transport helpers. Their tag
lists still named old columns 88/92/101/110/119; they now name native
82/86/95/104/113. A preflight control derives those tag coordinates from the
native lookup AST and checks both helper contracts and their five applications.
The proof tolerates simplification having already removed conditional branches.
The failed leaf exited 1 in 32.62 seconds at 575.23 MiB, with no owned children
left; the selected-source phase took 899.54 seconds. Complete derivative,
fixture-set, warm and full-assurance validation remain pending.

Focused diagnosis [41914965398](https://github.com/matter-labs/zksync-airbender/actions/runs/41914965398)
on `01734ad19` compiled consumed-message Core and Inputs. It then found the
separate native-permutation stencil still assigning word address 24 at old
column 78 (`Native.lean:207:79`). The stencil now uses native column 74, matching
the already-validated data assignment. A preflight control binds both versions
to the native range-column AST. Worker column 78 is unchanged. The leaf exited
1 in 61.12 seconds at 889.54 MiB with no owned children; the focused phase took
308.06 seconds. Complete derivative and standard verification remain pending.

Focused diagnosis [41917429432](https://github.com/matter-labs/zksync-airbender/actions/runs/41917429432)
on `2092e29db` passed the complete consumed-message derivative and dependencies,
including Core, Inputs, Native and the top-level theorem module. Its selected
source phase took 399.51 seconds; final freshness/object checks passed with no
owned children left. This remains partial evidence.

Standard warm [41919500084](https://github.com/matter-labs/zksync-airbender/actions/runs/41919500084)
on the same head passed native/setup reconstruction, compiler provenance and
the early Lean fixture phase, then failed at `Tests/GKRNativeROM.lean:3:5`.
The test had no import despite opening `Airbender.Compiler.ROMNative.WordMemory`.
It now imports the existing `WordMemoryRows` proof module explicitly. No test
statement or proof changes. The failed leaf exited 1 in 1.10 seconds at 131.93
MiB with no owned children; complete-source work reached 1037.92 seconds after
the 144.16-second fixture phase. Standard verification and assurance are pending.

The same zero-import pattern affected four more GKR smoke tests. All five
entry points now import their actual dependency explicitly. The subword test
also referenced removed helper namespaces; it now checks the same half/byte
ROM and decoder tags directly on the existing materialized setup, and proves
zero padding for every one of the row's nine generic coordinates. No Review
statement or premise changes. A lightweight boundary control checks all test
entry points that open the project namespace for missing imports.

Focused diagnosis [41926270665](https://github.com/matter-labs/zksync-airbender/actions/runs/41926270665)
on `6c6ab2f79` passed `GKRNativeROM`, then found that the subword test also needs
the existing `ColumnSlices` projection theorem import for `generic_cell_value`.
That dependency is now explicit; the assertions and proofs are unchanged.
The leaf exited 1 in 3.90 seconds at 314.51 MiB with no owned children; the
focused phase took 75.77 seconds. The five-test diagnosis and standard FV
remain pending.

All five GKR smoke tests subsequently passed in focused run
[41927650659](https://github.com/matter-labs/zksync-airbender/actions/runs/41927650659)
on `7c222110c` (111.76 seconds for selected sources). Standard warm
[41929058872](https://github.com/matter-labs/zksync-airbender/actions/runs/41929058872)
then passed native/compiler and early fixtures but found stale dependencies
and removed decoder helpers in `Tests.NativeSetupSemantics`. The test now
imports the current decoder/ROM models explicitly, checks the first imported
instruction against original Sail decoding, and rejects PC 16 over the entire
16,777,216-row decoder domain using the retained PC column and its sentinel
tail. No production or Review changes. The failed leaf exited 1 in 4.03 seconds
at 322.81 MiB with no owned children; complete-source work took 1105.42 seconds
after 29.55 seconds of early fixtures. The new test proofs await focused CI.

Focused run [41935450679](https://github.com/matter-labs/zksync-airbender/actions/runs/41935450679)
on `447c6c720` resolved those imports and accepted the positive decoder/ROM
checks. The full-domain rejection proof then failed on vector projections;
direct reduction also reached the existing recursion limit. A private PC
projection lemma now separates normalization from the imported column, and
query equality uses the vector projection lemmas explicitly. The resource
limits, rejection statement and complete domain are unchanged. The failed
leaf took 6.04 seconds at 406.13 MiB, with no owned children; focused source
work took 57.91 seconds. The projection repair awaits focused CI.

Run [41937231684](https://github.com/matter-labs/zksync-airbender/actions/runs/41937231684)
on `feacc685b` accepted the query projection but found an unspecified bound in
the PC helper and missing zero-offset arithmetic rewrites. Those steps now
name the vector/index and prove the imported metadata separately, then apply
`Nat.zero_add`. No resource increase or domain change. The failed leaf took
4.80 seconds at 399.63 MiB, with no owned children; sources took 57.39 seconds.

Run [41938404494](https://github.com/matter-labs/zksync-airbender/actions/runs/41938404494)
on `8c4ecfe2a` accepted those metadata and vector bounds. The finite-prefix
kernel-decision calls retained local proof variables, and the padding branch
was not selected before reduction. The proof now splits the row condition
first and rewrites kernel-proved equalities for both imported PC block streams;
the four prefix entries use simplification. The failed leaf took 5.07 seconds
at 406.68 MiB with no owned children; sources took 56.55 seconds.

Run [41939704941](https://github.com/matter-labs/zksync-airbender/actions/runs/41939704941)
on `e0e5d1815` accepted the prefix and branch-selection repairs. Only padding
reduction still reached the recursion limit. The bounded padding index is now
abstracted before simplifying its constant column, keeping subtraction by
1,048,576 outside that reduction. The failed leaf took 5.52 seconds at
416.78 MiB with no owned children; sources took 58.10 seconds.

The complete decoder/ROM test passed in focused run
[41940857292](https://github.com/matter-labs/zksync-airbender/actions/runs/41940857292)
on `e89dfdb32`: source work took 62.07 seconds, with the repaired module taking
4.93 seconds at 347.57 MiB charged footprint. Final freshness/object checks
passed and no owned children remained.

Complete warm [41942022978](https://github.com/matter-labs/zksync-airbender/actions/runs/41942022978)
on the same head passed native/compiler checks, early fixtures and 114 guarded
source stages before `Tests.UnifiedModularExecution` exposed a stale forged-FMA
overlay. Its auxiliary writes still used columns 78/80; the native layout uses
74/78. Only those two private witness coordinates change. The local-validity
and shared-history-rejection statements and proofs are unchanged. The failed
leaf took 120.26 seconds at 702.84 MiB charged footprint, with no owned children;
complete sources reached 2805.36 seconds after 29.47 seconds of early fixtures.
Complete source/audit validation and final assurance remain pending.

The modular trace and forged-FMA controls passed in focused run
[41950041857](https://github.com/matter-labs/zksync-airbender/actions/runs/41950041857)
on [the FMA repair commit](https://github.com/matter-labs/zksync-airbender/commit/d8abd3d9d30c1406191b02f39b371c1656783370): selected sources took 240.00 seconds, with the module taking
124.31 seconds at 830.74 MiB charged footprint. Final freshness/object checks
passed and no owned children remained. Ordinary PR checks also passed.

Complete warm [41951803857](https://github.com/matter-labs/zksync-airbender/actions/runs/41951803857)
then exposed the private `Tests.UnifiedShift.queryValues` helper still reading
the old 88/92 pools while the native layout uses 82/86. Its row-index bounds
failed and later proof searches hit the existing heartbeat limit. Only helper
coordinates change; a lightweight guard now compares them to all five pooled
queries in the actual native JSON. Every theorem statement and proof and all
resource limits remain unchanged. The failed leaf took 777.00 seconds at
708.08 MiB charged footprint, with no owned children; sources took 1045.20 seconds.
Nineteen focused controls pass. Source-derived checks also verify all seven
native CPU rows, all 35 projected queries and their complete native table rows;
the logical fixed-table indices stay below 524545. Lean confirmation is pending.

The shift test subsequently passed in focused run
[41956480731](https://github.com/matter-labs/zksync-airbender/actions/runs/41956480731):
selected sources took 283.31 seconds; the module took 168.87 seconds at 1039.26 MiB
charged footprint, with no owned children and final freshness/object checks passed.
The two abbreviated commit references rejected by the spelling check now use
commit links; that gate passed on the documentation repair.

Complete warm [41957810422](https://github.com/matter-labs/zksync-airbender/actions/runs/41957810422)
on [the shift proof revision](https://github.com/matter-labs/zksync-airbender/commit/2484ebebfdd8481aa46484be195aebb33f2aa982)
then found undefined input-wrapper names in `Tests.UpstreamPlatformCompatibility`.
Its test adapters now target actual `BootInputsWith` and `ExecutionInputsWith`.
The six-field profile adapter accepts boot data to build the complete current
input record; its callers retain their existing boot data and every ordinary
address, configuration, register, code and instruction-profile condition.
Arbitrary original handlers and all Review statements/premises remain unchanged.
The failed leaf took 6.17 seconds at 424.84 MiB charged footprint, with no owned
children; source work took 311.51 seconds. Focused Lean confirmation is pending.

The runtime checker's import-only cleanup reduces direct imports from 74 to
20. Its executable body and every assertion are byte-identical in that change;
none of the 54 removed test imports declares an explicit initializer. Using
the CI-produced import graph, the project dependency closure across the three
configured executables shrinks from 1656 modules to 1147. Complete source and
kernel-replay discovery still independently includes all 249 test modules.
No Review file or trust gate changes. This measures dependency reduction;
focused compilation, runtime qualification and timing confirmation remain pending.

The successful bootstrap cache upload in run 41832547126 delayed compiler
verification by 8m14s. The workflow now saves its one Lean snapshot after
verification and diagnostic upload. A source attempt includes bootstrap progress;
if no source stage ran, CI saves the partial or completed bootstrap instead.
Workflow lint and all 64 stage-outcome combinations pass. The new cache ordering
still requires final-revision CI validation.

Run [41830870517](https://github.com/matter-labs/zksync-airbender/actions/runs/41830870517)
passed Linux capacity qualification, but its first native command was rejected
by the guard's old CLI maxima before execution. The guard now requires an
explicit native-artifact profile for 8,192 / 12,288 MiB, with another capacity
check under the worker lock. Unflagged calls retain the original caps, and native
calls cannot request the extended review timeout. The profile boundary controls
pass; original native reconstruction subsequently passed in run 41832547126.

Warm run [41803197805](https://github.com/matter-labs/zksync-airbender/actions/runs/41803197805)
failed in source validation on reserved `start` binders in
`Proofs/UnifiedReduced/WorkerExecution.lean`. The binders and their uses are now
escaped without changing their Lean names or theorem statements. This source
repair still needs CI validation; no duplicate local build is running.

The tag `fv-archive-uncached` records the branch before scope removal.

The uncached captures and captured-program compatibility modules are removed.
Old arithmetic, functional and frame shard projections are removed.
All 58 focused source builds for this deletion pass.
The cached native acceptance theorems remain in the production gate.
Three [native corollaries](Airbender/Review/Compiler/Theorems.lean) compose them
with the full unsigned, reduced and unified target proofs.
Their focused source builds pass.
Item 3 has stopped. No more fact families will be converted.
FV CI is configured for weekly full assurance and manual iteration runs on the large runner.
The weekly schedule starts when the workflow reaches the default branch.
One freshness step checks all 52 generator routes.
It also requires tracked Airbender imports to resolve to tracked sources.
The cold source queue includes the top-level `Airbender.lean` module.
Its focused source build passes after the stale imports are removed.
The tracked-import check covers 12,078 imports in 4,212 Lean files.
The earlier log is in [VERIFICATION_HISTORY.md](VERIFICATION_HISTORY.md).
The final axiom inventory and baseline refresh remain pending.
[PR #585](https://github.com/matter-labs/zksync-airbender/pull/585) is open and mergeable.
One full assurance run, including independent kernel replay, remains required before merge.
The history rewrite signed all 768 commits. Later commits are signed.
GitHub verifies the signed head.
The signing rewrite leaves the source tree unchanged.

## Plan

1. The three deletion commits are complete. Their focused source builds pass.
2. Iterate with a warm manual run on the large runner. It retains normal Lake
   freshness, the complete frontend and runtime checks, generator freshness,
   and the environment/axiom audit. The cold benchmark and independent replay
   are not in this iteration gate.
3. After iteration, run full assurance once with transitive kernel replay and
   the false-proof controls. Use a 2,048 MiB stack and refresh the axiom
   baseline. Weekly default-branch runs also include this assurance. Request
   a cold source benchmark separately when new performance data is needed.
4. Fix proof and validation failures within the formal model and CI. Record
   production defects in FINDINGS.md and expose the required property as a
   temporary interface assumption. Do not repair production behavior here.

## Runtime

The user moved final validation to the large CI runner.
[Run 41451555538](https://github.com/matter-labs/zksync-airbender/actions/runs/41451555538)
stopped at signed commit `6031819e9f8e76f4acc351a0b1af8c8bf7ee5dd3`.
All 12 native generators, all 16 setup exports, the complete setup inventory,
and the compiler-capture freshness checks pass. The cold pass built 2,756 modules.
The next module rejected the reserved `parts` binder in `ShiftAssembly.lean`.
The fix quotes that binder and the same reserved syntax in two adjacent consumers.
The Lean names and theorems stay unchanged.
All three focused source builds and all 52 generator checks pass.
CI now saves cold build progress after failure.
[Run 41546838677](https://github.com/matter-labs/zksync-airbender/actions/runs/41546838677)
then stopped after 756 modules when Linux rejected a `pidfd_open` request.
The guard now retries this error briefly and rechecks process identity and exit.
It still stops if it cannot pin a live process. Resource caps stay unchanged.
The focused Linux guard controls pass. A corrected full run is required.
The earlier run rejected three omitted split Keccak exports. The CI list is fixed.
The repaired run reuses saved native build caches.
The registered Rust CI workflow provides the manual entry.
It calls the same FV workflow. Other Rust jobs skip this manual run.
FV stays off PR runs. Nightly runs retain their normal baseline comparison.
This manual run requests a cold build and a baseline refresh.
It restores no project Lean objects. Each cold module gets a time and memory receipt.
The job exports the refreshed baseline only after a passing environment audit.
The transitive replay uses a 2,048 MiB stack and checks all safe dependencies.

The duplicate local Mac frontend and Docker cold run stopped at the user's request.
Their caches and partial reports remain. Neither is a full validation result.
The separate Lean 4.35 experiment has completed its focused source checks.
That experiment does not change this PR's Lean 4.31 toolchain.

Focused builds pass for the cached native acceptance path, all three native
corollaries and the changed compiler/protocol aggregate imports.
All 52 generator routes pass. These focused results do not replace the full gate.
`Source.ChiCharacters` uses the measured 1,800-second source allowance.
Other source leaves retain 900 seconds. Memory caps and kernel checks stay unchanged.

## Final validation

| Phase | State | Time (s) | Peak footprint (MiB) |
| --- | --- | ---: | ---: |
| CI cold source partial, 2,756 of 4,202 modules | Stopped at parse failure | 33,462.48 | 2,198.55 |
| CI `ShiftAssembly` parse failure | Fixed; focused source passes | 4.62 | 353.58 |
| CI cold source partial, 756 of 4,202 modules | Stopped at guard error; fixed | 11,130.39 | 2,278.52 |
| CI full frontend and runtime gates | Queued | Pending | Pending |
| CI environment audit and baseline refresh | Queued | Pending | Pending |
| CI full transitive replay, 2,048 MiB stack | Queued | Pending | Pending |
| Local Linux cold partial, 857 modules | Stopped; moved to CI | 8,383.54 | 2,202.59 |
| Local Mac frontend partial | Stopped; moved to CI | 5,108.33 | 2,100.26 |
| Local Linux `Source.ChiCharacters` cold leaf | Passed | 1,133.67 | 540.31 |

The CI and Linux partial times sum module guard times. The Mac time is wall time.
The failed CI artifact retains `cold-build/modules.jsonl` and all failure logs.
The complete cold pass will also export `cold-build/modules.md`.
These times include Lake startup and dependency freshness checks.
CI uploads commands, resource receipts and failure logs from each stage.
Local partial evidence remains in `/tmp/airbender-review-round/method-reset-2026-11-02/`.
No duplicate local full audit or replay is scheduled.
The PR monitor follows the CI run and reports failed verification steps even
while cache-saving cleanup is still running.

## PR checks

Earlier passing PR checks apply to their recorded revisions, not this cleanup.
The branch-only initialization-window test is removed; upstream #548 already
pins deployment top bits and rejects differing preimage values. The GPU workflow,
including its original RAM setting, is restored to the base.

Production crate additions are limited to the artifact export examples, the setup
artifact module and tests, its module declaration, and required serialization
derives. Cache-mode setup selection lives only inside the export example.
The final PR description lists every file outside `formal_verification/` and
its artifact or CI purpose. Current ordinary checks, native receipt
requalification and the separate full FV gate must pass before merge.
