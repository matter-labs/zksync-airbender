# Findings: assumptions and circuit bindings

<!-- Source-only labels below are modules/namespaces, hash pins, tool tokens,
local binders, or removed/private historical identifiers. Current public
declarations remain required by the compiled reference audit. -->
<!-- source-names:
Airbender Airbender.Proofs.GKRProtocol.ROMNative.WordMemoryRows AirbenderUnifiedNative
BigintMemory DelegationTimestamps DynamicCopyLoopNative ExecutionPublicInputsWith
ImportedBootInputsWith KECCAK_CHI5_CSR_REGISTER KECCAK_COLUMN_PARITY_CSR_REGISTER
KECCAK_SPECIAL5_CSR_REGISTER KECCAK_THETA_RHO_CSR_REGISTER PathGLoopNativeBase
Proofs.GKRProtocol.ColumnSlices SUPPORTED_CSRS SubwordBoundary SubwordRows Tests.ArtifactImport
Tests.BigintMemory Tests.DelegationTimestamps Tests.DynamicCopyLoopNative
Tests.NativeSetupSemantics Tests.PathGLoopCPU.Equations Tests.PathGLoopNativeQueries
Tests.UnifiedModularExecution Tests.UnifiedShift.queryValues Tests.UpstreamPlatformCompatibility
Trace.NativeDecoder __TEMPLATE_INITS_TEARDOWNS_TOP_BITS_ _soundness a23f1aa01 a99f6c4ce
ba55c93d53f3a689abccf6b628331f9df07ea8c779e3595f0efce04db914df71 de9c7c77b diagnose_modules
e0e5d1815 e89dfdb32 e94380e9f ec752d357458d70d21b5f68b8575bba70d303d8d0d2771032bb4017f18e85565
fd7c0fee5 feacc685b generic_lookup_padding keccak_f1600.rs keccak_special5
keccak_special5_layout_no_caches_gkr.json notStore parts prepared_round_masks_soundness
requalify_setups setup_artifact split_ifs start stop transcript_init workerFamilies
-->

Current native target: upstream `av_gkr_compiler` at
`c1a662222cafcd96db4383dce737edb79fa62b09`. Current totals and completed validation
are maintained in [Verification status](VERIFICATION_STATUS.md), separately from
this evidence register. The [current eight-file native inspection](artifacts/setup/native-evidence.json)
records the source observations and exact drift guards. The new base includes
the branch witness, recursion output and cap repairs from upstream #531.
Focused qualification of the new artifacts passed. The compiler group passed
497 checks in both cache modes. The full validation remains pending.

The original review below was dated 13 October 2026 at snapshot
`59a493173a85441da542155cb825488f43904b1e`; its inventory counts and dated
integration checkpoints are historical. Conditional closure within a public
profile is distinct from native enforcement and from general control-flow coverage.
The older full-CSR theorem retains straight-line preparation. The general
actual-path and complete-span theorems now pass focused kernel checks, including
an accepted two-COPY branch/jump/loop application. The accepted native
[G-loop application](Tests/PathGLoop.lean) also passes focused kernel checks:
`Tests.PathGLoop.full_execution` retains all three variants' real effects,
`baseline_grouped` and `scratch_grouped` compose the complete 56-call G protocol,
and `actual_nonzero_position` binds the last worker to index 55/controller 183 after
55 repeated loop calls. `protected_negative` proves the actual protected-message
SW7 changes message0 from 0 to 7 and refutes both endpoint
[`Airbender.Blake2G.WorkVector.WordMapping`](Airbender/Review/Trace/Workers/Blake2G/WorkVector.lean) and
[`PathSpanAlgorithmAt`](Airbender/Review/Trace/UnifiedReduced/Paths/SpanProjection.lean); its whole execution still holds. These applications must also pass separate declaration-origin auditing,
transitive controls and full independent kernel replay over the complete source inventory. Tracked data RAM
remains at or above the ROM limit; standard boot-ROM-data copying is not claimed.

This document records places where a checked theorem can remain true while a
broader circuit or execution claim fails. The pass examined the input/interface
declarations across `Review/Circuits`, `Review/Helpers` and `Review/Trace`, then
followed the significant conditions into their stronger claims and regressions.
It screened 224 Review modules and inspected 105 named input/interface declarations
in 83 files, plus acceptance, profile and conclusion definitions.

The audit-only pass at the snapshot above changed no Lean, Rust, artifact or
dependency files. The counterexamples below
already exist in the development; this pass did not discover a new counterexample.
An **accepted counterexample** establishes a gap at the exact relation tested.
An **unresolved binding** identifies a condition not yet connected to general
acceptance. A **profile difference** is intentional semantic scope. These labels
are not interchangeable with a full verifier or cryptographic exploit.

## Production scope and temporary interface assumptions — 4 November 2026

PR #585 retains production behavior from base
`c1a662222cafcd96db4383dce737edb79fa62b09`. Outside the formal model and CI,
only additive artifact exporters, their private setup helpers, export tests and
required serialization derives remain. Existing table, setup, proving, GPU
scheduling and EVM verifier functions are restored to the base. The normal setup
and proving path does not call the export code.

A production defect discovered by the model is documented here and represented
by an explicit temporary interface assumption. Record the required property,
affected source path, named Lean premise and evidence needed to discharge it.
The assumption leaves the production defect open; it must not be described as
native enforcement or introduced as a new Lean axiom. Keep it until a production
repair is validated and the affected artifacts are regenerated. Production
behavior must not be repaired in this PR to make a formal check pass.

The redundant branch-only EVM initialization-window repair and its tests have
been removed entirely. Upstream #548 already fixes the supported EVM path by
pinning window top bits to deployment constants; no replacement PR is being opened. The lazy lookup maps, setup-memory rewrites
and GPU lookup-domain change are also removed. Earlier tests of those branch
revisions do not validate the current checkout. Native source receipts and
fresh-export equality must be rechecked after the restorations; retained
artifact bytes and older validation results alone are not current freshness
receipts. Any resulting mismatch belongs in this register, not in a production
code repair.

Static comparison after cleanup initially reported ten changed source receipts:
`circuit_defs/setups/src/lib.rs`,
`cs/src/gkr_circuits/decoder_trait.rs`, `cs/src/tables/mod.rs`, the three
`execution_prover/src/setup/{common,mod,unrolled}.rs` files, and
`prover/src/gkr/prover/{setup,setup_artifact,setup_tests}.rs`, plus
`execution_prover/examples/export_setup_json.rs`.
This was a freshness failure after scope cleanup, with no new circuit defect
established. These source receipts were subsequently requalified through actual
native execution, as recorded below; payloads were unchanged.

Warm run [41815044934](https://github.com/matter-labs/zksync-airbender/actions/runs/41815044934)
passed the repaired preflight, then rejected the first stale source receipt before
native reconstruction. The explicit `requalify_setups` CI input now snapshots
candidate source receipts outside the checkout. All twelve generators, sixteen
complete setup comparisons and scoped native dep-info checks must pass before
the job promotes source receipts. Candidate snapshots are unqualified; they do
not update this finding or establish current native fidelity. Changed payloads
still fail and must be recorded here without changing production behavior.
The decoder smoke-test command follows its export-only `setup_artifact` module.

Run [41818079338](https://github.com/matter-labs/zksync-airbender/actions/runs/41818079338)
passed the first five circuit regenerations, then the original subword generator
exceeded the 2,560 MiB footprint bound (2,577.18 MiB observed after 9.86 seconds).
This is a resource failure, with no Rust constraint or setup mismatch diagnosed.
Production table construction remains unchanged.

Run [41823630219](https://github.com/matter-labs/zksync-airbender/actions/runs/41823630219)
rejected the attempted chunked export adapter: its data rows matched smaller-domain
native tests, but it cleared the content index map that the original table-size
method uses. The resulting ROM size was zero and the full circuit comparison
failed. The adapter and its example are withdrawn completely. Restored exporters
use the original native constructors, complete table objects and exact generator
tests. No source receipt was promoted by either failed run.

Native artifact generation, compiler capture and mixed native/Lean decoder-data
checks now have an explicit 8,192 MiB footprint / 12,288 MiB resident budget,
retaining the 900-second time cap and one global worker. This is a deliberate
resource-policy change, not a native fidelity or proof result. Before each such
job, Linux host and visible cgroup capacity/availability must provide the resident
budget plus 2 GiB headroom; reclaimable inactive file cache is accounted for.
Capacity measurements and actual guarded peaks are retained as receipts. Lean
source verification, environment/axiom audits and independent kernel replay keep
the original 2,560 / 5,120 MiB limits. Native reconstruction runs before restoring
the Lean cache so complete circuit/setup checks happen before Lean preparation.
Future mismatches record the first differing JSON field and retain the fresh
circuit for inspection. Actual setup reconstruction under this budget has now
passed in run 41832547126 below; Lean validation remains pending.

Run [41830870517](https://github.com/matter-labs/zksync-airbender/actions/runs/41830870517)
qualified the runner at 111,377 MiB effective capacity and over 110,000 MiB
available memory. It then rejected the larger CLI arguments before running a
native command: the guard parser still enforced the default caps. The correction
adds an explicit native-artifact profile, rejects its use with extended review
time, and independently qualifies capacity after acquiring the worker lock.
Default-profile callers still reject limits above 2,560 / 5,120 MiB. Controls now
exercise profile acceptance, rejection of unflagged/high/extended requests, and
budget decisions for native-sized process samples. No native result is
claimed from the argument-validation failure.

Run [41832547126](https://github.com/matter-labs/zksync-airbender/actions/runs/41832547126)
on `6c53a9a1201b579bebd341f29866d87da6d528c4` passed all twelve exact native
generator tests, sixteen complete setup comparisons and scoped dep-info checks.
The downloaded `qualified-receipt.json` reports 28 native execution jobs and
sixteen complete comparisons. Its SHA-256 is
`ec752d357458d70d21b5f68b8575bba70d303d8d0d2771032bb4017f18e85565`;
the exact qualified setup manifest's SHA-256 is
`20f680f0a08551ad3f1a3674686988f7fcac53ebec4117c8bdaea75bb53cad3e`.
All 28 receipt hashes, the exact current-source candidate and all sixteen
downloaded payloads were checked against the retained data. This resolves the
ten stale setup source receipts without changing a production function or a
retained setup payload. This qualification alone does not validate the Lean proofs.

Setup receipt promotion also invalidates the compiler's pin of the setup
manifest. Requalification now refreshes compiler input receipts only after all
33 compiler payload files reproduce byte for byte and the freshly exported
sidecars, certificates, circuit identities and input pins pass their checks.
Run 41832547126 also passed compiler requalification: all 33 payload files
reproduced byte for byte, the fresh provenance checks passed, and all eleven
retained cached native identities passed. The exact downloaded compiler manifest
has SHA-256
`ba55c93d53f3a689abccf6b628331f9df07ea8c779e3595f0efce04db914df71`;
its qualified receipt has SHA-256
`2f8f2293fb470f84ea52bef5b37f2a3686d3f030983d624114c3cfbb2848a084`.
Only compiler input receipts changed. Both manifests are the exact verified
downloads and pass their strict checkers locally. Lean validation and final full
assurance remain separate pending gates.

The same run subsequently failed while rebuilding
`Proofs/UnifiedReduced/WindowProjection.lean`. Lean rejected unquoted local
`parts` at line 88 and `start` at line 109. The guarded build exited with code 1
after 4.96 seconds, with 411.79 MiB charged footprint and no remaining owned
processes. The repair quotes those identifiers and corresponding local binding
patterns in the remaining private proofs. Quote-normalized source is identical
to the previous revision; no Review statement, production code or artifact
manifest is changed. Current Lean validation and final full assurance remain
pending.

Run [41846991839](https://github.com/matter-labs/zksync-airbender/actions/runs/41846991839)
on `5141cfccce167f536bea4b99f385a2783f295ce5` passed native and compiler checks,
then failed at `Proofs/UnifiedReduced/SupportedUsePrefix.lean:18`: its ordinary
`start` parameter was outside the earlier local-binding scan. The missing
`state_prefix_matching` error later in that file follows the rejected declaration.
The guarded build exited with code 1 after 5.76 seconds at 441.29 MiB charged
footprint, with no owned processes left. The follow-up repair quotes all remaining
bare `start` and `parts` code identifiers in private proofs opening the affected
Sail namespaces, including ordinary parameters and references. All seventeen
changed files are identical after removing identifier quotes. Review statements,
production behavior and qualified manifests are unchanged. CI must validate the
repair; no completed full assurance result is claimed.

Run [41853518121](https://github.com/matter-labs/zksync-airbender/actions/runs/41853518121)
on `c4eb40e6687939103089f8d78e7febfb7fe1f7e5` passed native setup and compiler
checks, then failed in `Tests/BigintMemory.lean:63`. The concrete fixture started
its nineteen timestamp triples at column 217, one column after the native layout:
previous low/high are `216 + 3*i` / `217 + 3*i`, and borrow is `218 + 3*i`.
It consequently put borrow bits into the next port's previous-low column and left
the real borrows zero. Lean correctly rejected negative low differences and an
upper difference equal to the excluded 524,288 boundary. The guarded leaf build
failed in 31.44 seconds at 608.83 MiB charged footprint, after 116 minutes of
serial source work. This is a constructed-fixture error, with no production defect
identified. The fixture ranges and predecessor-clock columns are corrected in
`BigintMemory`, `DelegationTimestamps` and `DynamicCopyLoopNative`. CI now checks
these three actual Lean fixtures and their dependencies before the complete
source traversal, using the existing guarded frontend and unchanged limits.
Review statements, production functions and qualified artifacts are unchanged.
The corrected fixtures still require Lean CI validation.

Run [41877076050](https://github.com/matter-labs/zksync-airbender/actions/runs/41877076050)
on `0400e0f36` verified `Tests.BigintMemory` (31.77 seconds) and
`Tests.DelegationTimestamps` (17.44 seconds). Its early fixture phase then rejected
`Tests.DynamicCopyLoopNative`: six CPU rows failed imported equations, followed
by pooled-lookup and timestamp failures. The handwritten auxiliary witness used
obsolete column roles: the multiplication intermediate belongs at 78, branch
selection at 79, ROM residue at 80, pooled slots at 82–121, PC carry at 122 and
timestamp borrows at 123–125. Both the COPY and Path-G fixtures now use those
native roles and the exact current pooled definitions. No constraint or lookup
was removed. A lightweight audit parses the corrected COPY assignment clauses
and checks all sixteen candidate rows against every native equation, every
native range/timestamp expression and all eighty complete pooled queries against
the retained setup JSON. This is supplementary evidence; Lean CI remains required.
The failing leaf took 40.09 seconds at 732.07 MiB charged footprint; the early
phase exposed it after 161.65 seconds. CI also frontloads the Path-G native
acceptance module to exercise the other affected fixture. Review statements,
production functions, source artifacts and resource/trust limits are unchanged.

Run [41882490544](https://github.com/matter-labs/zksync-airbender/actions/runs/41882490544)
on `e94380e9f` verified the corrected `Tests.DynamicCopyLoopNative` module. The
early phase then failed in `Tests.PathGLoopNativeBase.lean:262:49` on an unquoted
`start` parameter. Its failed leaf exited in 28.93 seconds at 544.04 MiB charged
footprint, with no owned processes left; the early phase took 140.71 seconds.
The repair quotes remaining `start`/`parts` identifiers throughout the test
sources, while preserving the five actual macro-keyword uses in three tests.
All identifier-only edits are identical after quote normalization.

Static inspection also found Path-G CPU certificates still indexing 129
polynomials, while the retained native JSON and existing `Airbender.UnifiedReduced.constraint_count`
theorem give 120. The private certificate bounds and final chunks now cover
exactly 0–119: seven sixteen-equation chunks and an eight-equation final chunk.
The obsolete 128-only chunks are removed. A static coverage check confirms all
41 finite certificate groups cover every native equation without an extra index.
The final claims still quantify over the complete actual imported constraint
list. Review statements, production behavior and artifact data are unchanged;
the revised certificates still require Lean CI validation.

Run [41887174299](https://github.com/matter-labs/zksync-airbender/actions/runs/41887174299)
on `1daf1d67e` passed the repaired `PathGLoopNativeBase` module, then rejected
the separate imported keyword `stop` in `PathGLoopCPU/Shared.lean:44:34`.
The guarded leaf exited in 5.63 seconds at 400.25 MiB charged footprint with no
owned processes left; the early phase took 90.1 seconds. The remaining 93 `stop`
identifiers in fifteen Path-G certificate files are quoted, while the actual
`column_blocks_part ... stop ...` macro keyword remains unchanged. Every source
edit normalizes byte-identically after removing identifier quotes. The native
120-equation coverage, Review statements, production and trust/resource policy
are unchanged. CI must validate the remaining certificate modules.

Run [41891337613](https://github.com/matter-labs/zksync-airbender/actions/runs/41891337613)
on `fd7c0fee5` compiled `Tests.PathGLoopCPU.Equations`, verifying all 120 native
CPU equations for all 228 rows and three variants. The early phase then failed
in `Tests.PathGLoopNativeQueries`: its helper vector still named range columns
78/79/81/86 instead of native 74/75/64/80, its pooled stencil and support lists
still used the old 88–127 region instead of 82–121, and its abstract clock helper
still expected borrow columns 131–133 instead of 123–125. The first diagnostic
is `PathGLoopNativeQueries.lean:195:4`, a bound for column 78 where native query0
requires column 74. The failed leaf took 85.61 seconds at 823.25 MiB charged
footprint, with no owned processes left; the early phase took 458.4 seconds.
These CPU-only helper coordinates now match the corrected candidate witnesses.
An independent structural check derives all thirteen range coordinates and all
five complete pooled-expression support lists from the retained native JSON.
The worker section is byte-identical. No native query or constraint is removed;
Review statements, production, artifacts and all trust/resource limits remain.
The query helpers and complete native acceptance still require Lean CI.

Run [41898007151](https://github.com/matter-labs/zksync-airbender/actions/runs/41898007151)
on `a99f6c4ce` eliminated the query proof errors. Its only diagnostic was the
unused `notStore` simp argument at `PathGLoopNativeQueries.lean:305:77`.
The failed leaf took 86.13 seconds at 822.34 MiB charged footprint, with no owned
processes left. The obsolete argument and unused local proof are removed;
the simp proof and every query remain checked. The full native prelude and
large cache upload made this small correction expensive to iterate. An
explicitly partial `diagnose_modules` CI mode now checks selected modules using
the existing guarded frontend without those native stages or cache uploads.
This is diagnosis evidence only; ordinary warm validation, the environment
audit and final full assurance remain required. No production defect is
identified by this linter failure.

### Connected native CPU test witnesses

Inspection of the other consumers found the same stale auxiliary coordinates
in delegation, comparison and control-preparation fixtures. Eleven test files
now place clock borrows at 123–125, multiplication scratch at 78, pooled slots
at 82–121, and comparison/control witnesses at the current native coordinates.
The wrapped-PC comparison explicitly sets native low-limb carry 122; it does
not reuse an old pooled-result column as a carry. Actual test theorems and all
their imported native constraints and queries remain unchanged.

A separate source parser reconstructed 84 representative witness rows directly
from the edited definitions and checked all 120 native structured equations,
thirteen range queries, eight timestamp queries, six port clock bounds and five
complete ten-field pooled rows per row against the retained native JSON. The
checks cover arithmetic, CSR, custom operations, binary/comparison/control,
PC wrap, normalization and the control-preparation chains. The memory-forgery
counterexample still satisfies native row constraints; its unchanged history
theorem states rejection. These supplementary checks are not Lean theorem validation;
the affected modules must still pass CI. This identifies stale constructed
test witnesses, with no production defect established.

The same inspection found fifteen more affected files covering arithmetic,
RAM/ROM, branch/JAL/JALR, bitwise, shifts, modular arithmetic and mixed/native
execution. Their witness definitions now use the current native coordinates,
including the inline initialization/teardown fields at 126–133. Every theorem
statement and proof body is byte-identical; no native constraint or lookup is
removed. The wrapping core-only example sets actual PC carry 122, while its
native clock extensions use borrows 123–125.

The supplementary source parser checks sixty more rows, for 144 total, against
the native equations and applicable range, timestamp and clock checks. It
compares complete fixed lookup rows with the retained native setup JSON;
dynamic ROM queries in three examples are checked against their explicit
public words instead. Three intentionally core-only rows retain that scope.
Bitwise and shift helper results are independently evaluated with the declared
bit-vector operations before checking the actual source-parsed assignments.
These are diagnostic checks, not Lean validation. The affected modules still
require CI; production code, Review statements and retained artifacts remain
unchanged.

Diagnosis [41905482598](https://github.com/matter-labs/zksync-airbender/actions/runs/41905482598)
on `a23f1aa01` then found a stale public theorem alias at
`ControlPreparationBase.lean:291:26`: `prepared_round_masks_soundness` is no
longer declared. The existing implementation theorem
`Airbender.UnifiedReduced.Caller.Proofs.prepared_round_masks` has the same field-capacity, inverse,
acceptance, prepared-input and alignment premises and the same mask conclusion.
The test now calls it directly. The failed leaf exited 1 in 37.01 seconds at
917.14 MiB charged footprint, with no owned children left. This repair changes
one proof reference and no premise, Review statement or production code.

Checking the connected tests' `_soundness` references against current
declarations found three more removed alias names. Eight hash-preparation
applications now pass their already-proved `Airbender.UnifiedReduced.Caller.HashControlPreparation` source
certificates to public `hash_control_preparation_soundness`. Two caller-cycle
applications use the existing implementation theorem `Airbender.UnifiedReduced.Caller.Proofs.caller_cycles`
with unchanged arguments. This composes the current theorems without adding
aliases to Review or changing any test statement or premise. Lean CI must
validate the new applications.

A static certificate audit found another stale interface: the four
`AirbenderUnifiedNative` rows and the consumed-message derivative still bounded
their finite CPU certificates by 129. The native inventory has 120 equations.
Their final chunks now cover 112–119; obsolete index-128 certificates are
removed, while the conclusions still quantify over the complete original
imported constraint list. The consumed-message CPU store also moves its word
address from old scratch 78 to native 74, retaining the multiplication value
from its already-correct parent witness. No worker coordinate is remapped.

Four new lightweight preflight controls compare explicit bounds and complete
chunk coverage against the native JSON and reject missing, overlapping and
outside-domain intervals. They run before compiler/native work. The import-only
fixture gate includes the consumed-message derivative. These source checks
pass; Lean still must validate the repaired certificates and derivative.

Diagnosis [41909111177](https://github.com/matter-labs/zksync-airbender/actions/runs/41909111177)
on `6dba399d9` compiled the corrected `AirbenderUnifiedNative` certificates,
Path-G query/acceptance modules and consumed-message data. It then failed at
`PathGConsumedMessage/Core.lean:64:12`: `split_ifs` had no remaining conditional
after simplification. Five transport goals also exposed stale CPU pooled-tag
coordinates 88/92/101/110/119 instead of native 82/86/95/104/113. Both helper
contracts and their five applications now cover the actual native tags; the
tactic tolerates branches already simplified away. The no-ROM transport claim
and complete native-acceptance conclusions are retained.

A new lightweight preflight control derives the five coordinates from the
native generic-lookup AST and checks those contracts/applications. The failed
leaf exited 1 in 32.62 seconds at 575.23 MiB charged footprint, with no owned
children left. This was a stale test-proof interface, with no production
defect identified. Lean CI still must validate the derivative and full set.

Focused diagnosis [41914965398](https://github.com/matter-labs/zksync-airbender/actions/runs/41914965398)
on `01734ad19` passed consumed-message Core and Inputs, then rejected
`Native.lean:207:79`: its permutation stencil put word address 24 at old column
78, while the validated data assignment uses native 74. The stencil is aligned
with the actual row. Its unchanged extensional-equality theorem and complete
native-acceptance conclusions remain required; no worker column is changed.
A preflight control checks both definitions against the native range-column
AST. The failed leaf exited 1 in 61.12 seconds at 889.54 MiB charged footprint,
with no owned children left. This is another stale constructed test helper,
with no production defect identified.

Standard warm [41919500084](https://github.com/matter-labs/zksync-airbender/actions/runs/41919500084)
on `2092e29db` passed native/setup reconstruction, compiler captures/provenance
and the early Lean fixtures. The complete source scan then found
`Tests/GKRNativeROM.lean:3:5` opening `Airbender` without any import; the expected
`Airbender.Compiler.ROMNative.WordMemory.nativeSetup` was consequently unknown. An explicit import
of the existing `Airbender.Proofs.GKRProtocol.ROMNative.WordMemoryRows` module
restores the test's intended dependency. Every test statement and proof body is
unchanged. The leaf exited 1 in 1.10 seconds at 131.93 MiB charged footprint,
with no owned children left. This was a missing test dependency, with no
production defect identified. The focused consumed-message diagnosis had
already passed in run 41917429432; complete FV and final assurance remain pending.

A scan found four additional zero-import entry points: windowed initialization,
subword native setup, unified full native setup and unified ROM. Their explicit
dependencies are restored together. Subword's removed `SubwordRows` and
`SubwordBoundary` helper names are replaced by direct checks on the existing
materialized native setup. The same concrete halfword/byte/decoder tag facts
are retained, and all nine generic coordinates of the padding row are proved
zero. This is the coordinate form of the original zero-vector property; it
does not weaken coverage. No Review or production code changes. A lightweight
test-import boundary control catches the missing-import pattern before builds.

Focused diagnosis [41926270665](https://github.com/matter-labs/zksync-airbender/actions/runs/41926270665)
on `6c6ab2f79` passed native ROM, then rejected subword's `Airbender.Compiler.MaterializedLookupSetup.generic_cell_value`
field notation: the theorem is declared in `Proofs.GKRProtocol.ColumnSlices`,
which the old helper namespace had imported transitively. That explicit import
is restored beside the materialized model import. Every assertion and proof
body is unchanged. The leaf exited 1 in 3.90 seconds at 314.51 MiB charged
footprint, with no owned children left; focused source work took 75.77 seconds.

All five GKR smoke tests passed in run 41927650659. Standard warm
[41929058872](https://github.com/matter-labs/zksync-airbender/actions/runs/41929058872)
on `7c222110c` then found `Tests.NativeSetupSemantics` relying on removed
decoder helpers and absent decoder/ROM imports. Its first error was unknown
`Trace.NativeDecoder` at line 5. Explicit dependencies restore the actual
packed decoder and imported ROM. The first decoder row is checked against an
explicit NOP entry and the original pinned Sail decoder. The unsupported-PC
test retains its full-domain rejection: the real and committed-padding PC
column contains only 0, 4, 12 or the unsupported sentinel. The proof follows
the actual imported dense/affine blocks rather than enumerating sixteen
million rows or using a removed semantic shortcut. No test premise, Review
statement, production code or kernel policy is weakened. The failed leaf
exited 1 in 4.03 seconds at 322.81 MiB charged footprint with no owned children;
complete-source work reached 1105.42 seconds after a 29.55-second fixture phase.

Focused run [41935450679](https://github.com/matter-labs/zksync-airbender/actions/runs/41935450679)
on `447c6c720` resolved the imports and positive membership checks, then
rejected definitional projection steps in the full-domain negative proof.
Directly reducing the padding vector also reached the existing recursion
limit. The repair projects normalization and mapped vectors through explicit
lemmas before reading the first imported column. It preserves the full
16,777,216-row rejection and existing limits. The failed leaf exited 1 in
6.04 seconds at 406.13 MiB with no owned children; focused sources took
57.91 seconds. No production or Review change is involved.

Run [41937231684](https://github.com/matter-labs/zksync-airbender/actions/runs/41937231684)
on `feacc685b` accepted the query projection but found an unspecified index
bound and missing zero-offset rewrites in the private PC proof. The bound now
names its vector/index, and explicit imported metadata equalities allow
`Nat.zero_add` before column comparison. The failed leaf exited 1 in 4.80
seconds at 399.63 MiB, with no owned children; sources took 57.39 seconds.

Run [41938404494](https://github.com/matter-labs/zksync-airbender/actions/runs/41938404494)
on `8c4ecfe2a` accepted those bounds and offsets, then rejected the finite
prefix's kernel-decision calls with local proof variables. Padding reduction
also ran before selecting the row branch. The repair splits that condition
first, proves the exact imported PC block streams by reflexivity and simplifies
the four prefix entries. Full-domain rejection and all resource limits remain
unchanged. The failed leaf took 5.07 seconds at 406.68 MiB, with no owned
children; sources took 56.55 seconds.

Run [41939704941](https://github.com/matter-labs/zksync-airbender/actions/runs/41939704941)
on `e0e5d1815` accepted the finite-prefix and branch-selection repairs. Only
padding-tail reduction still reached the existing recursion limit. The proof
now abstracts the bounded padding index before simplifying the constant
column, preserving its complete extent and keeping subtraction by 1,048,576
outside that reduction. The failed leaf took 5.52 seconds at 416.78 MiB, with
no owned children; sources took 58.10 seconds. Resource limits are unchanged.

The decoder/ROM test subsequently passed in focused run 41940857292 on
`e89dfdb32`, including complete-domain unsupported-PC rejection and final
freshness/object checks. Selected sources took 62.07 seconds; the module took
4.93 seconds at 347.57 MiB charged footprint with no owned children.

Complete warm [41942022978](https://github.com/matter-labs/zksync-airbender/actions/runs/41942022978)
on that head passed native/compiler checks, early fixtures and 114 guarded
source stages, then rejected `Tests.UnifiedModularExecution`'s forged-FMA
overlay: its old 78/80 auxiliary writes corrupt the native product and ROM
residue columns. The existing honest row already uses the native 74/78
coordinates; the forged overlay now does too. Its changed old destination,
recomputed result, local validity and global shared-history rejection remain
intact. Four failed native equations and one range check exposed this fixture
error; no production or Review statement changes are needed. The failed leaf
took 120.26 seconds at 702.84 MiB charged footprint with no owned children;
complete sources took 2805.36 seconds after 29.47 seconds of early fixtures.

Focused run 41950041857 on [the FMA repair commit](https://github.com/matter-labs/zksync-airbender/commit/d8abd3d9d30c1406191b02f39b371c1656783370) subsequently passed the complete modular
trace and forged-FMA controls, including shared-history and wrong-selector
rejection. Selected sources took 240.00 seconds; the module took 124.31 seconds
at 830.74 MiB charged footprint with no owned children. Final freshness/object
checks passed.

Complete warm [41951803857](https://github.com/matter-labs/zksync-airbender/actions/runs/41951803857)
on that head then found `Tests.UnifiedShift.queryValues` using legacy pooled
coordinates 88/92 despite its row assignment already using the native 82/86
layout. Wrong projected values caused fixed-table index bounds to fail and
later membership searches to reach the existing heartbeat limit. The private
helper now projects the actual exported native query coordinates. A lightweight
guard derives every pooled coordinate from the native JSON before compiler
work. The row assignments, theorem statements and proofs, production, Review
and resource limits are unchanged. The failed leaf took 777.00 seconds at
708.08 MiB charged footprint with no owned children; sources took 1045.20 seconds.
The repair passes nineteen focused controls and source-derived checks of all
seven CPU rows and 35 projected queries against complete native table rows.
Logical fixed-table indices remain below 524545; their layout is distinct from
the native physical region order, as the existing setup characterization proves.

Focused shift diagnosis 41956480731 subsequently passed, including final
freshness/object checks: selected sources took 283.31 seconds, and the module
took 168.87 seconds at 1039.26 MiB charged footprint with no owned children.

Complete warm [41957810422](https://github.com/matter-labs/zksync-airbender/actions/runs/41957810422)
on [the shift proof revision](https://github.com/matter-labs/zksync-airbender/commit/2484ebebfdd8481aa46484be195aebb33f2aa982)
then rejected `Tests.UpstreamPlatformCompatibility`'s undefined
`ImportedBootInputsWith`, `ExecutionPublicInputsWith` and imported-execution
wrappers. The actual public interface has `Airbender.UnifiedReduced.BootInputsWith` and one flat
`Airbender.UnifiedReduced.ExecutionInputsWith` record. The test adapters now assemble that record from
the same boot data and six public profile fields, translating only the ordinary
address condition under arbitrary original handlers. The profile-only adapter
accepts boot data, already supplied by its full-input callers. No Review
statement/premise, production behavior, axiom or resource policy changes.
The failed leaf took 6.17 seconds at 424.84 MiB charged footprint with no owned
children; complete sources took 311.51 seconds.

While complete warm run 41963487081 was still active, a static audit of
`Tests.ArtifactImport` identified two runtime checks that would reject current
native artifacts: unified expected 129 equations instead of 120, and bigint
expected 136 instead of 135. The assertions and diagnostic labels now follow
the actual retained producer JSON. A native-derived preflight checks 23 scalar
and query-count expectations across nine artifacts; it rejected both stale
counts before the correction. No assertion was removed and no production,
Review statement, theorem premise, axiom or resource policy changed. Actual
runtime CI qualification remains pending.

## Kernel fixed-setup provenance

All three split Keccak source certificates are proved.
The kernel connects each retained JSON source to its original canonical rows.
`parity_original_source_rows` proves the complete parity source relation.
`theta_original_source_rows` proves the complete theta/rho source relation.
`chi_original_source_rows` proves chi5 membership under native tags 65 and 66.
These tags exclude physical zero padding from chi5 queries.
Parity and theta/rho certificates include their physical padding.

The proofs retain the original source bytes, parser validation, columns and
physical lengths. They use exact source parsing and RLE decoder certificates.
They do not replace the retained sources with mathematical recipes.
The full unsigned target uses these certificates with native execution,
public program binding and initialization.
Exact lookup, request and RAM premises remain explicit.

The source certificates are in
[ParitySourceBinding](Airbender/Proofs/FullUnsigned/ParitySourceBinding.lean),
[ThetaSourceBinding](Airbender/Proofs/FullUnsigned/ThetaSourceBinding.lean) and
[ChiSourceBinding](Airbender/Proofs/FullUnsigned/ChiSourceBinding.lean).

## Finding status versus conditional proof coverage

**An assumption can close a conditional proof obligation while the finding stays
open.** Temporary assumptions that exclude an accepted bad case are recorded as
such; they do not establish that the circuit/verifier rejects it. An acknowledged
implementation bug needs a fix and validation, or evidence that the relevant
acceptance path already enforces the missing property. An open PR is neither.

Intended external interfaces (such as canonical statement words and contribution
masking), supported public profiles, and properties already derived in stronger
claims are separate categories. They are not automatically bugs. Conversely, a
missing validation check must not be relabeled an intended interface merely
because Lean can take it as a premise. No full malicious-proof exploit is needed
to retain a demonstrated source defect or accepted-relation discrepancy.

### Linear and open-PR review — 15 October 2026

The five exported Linear issues and **all live comments** were read. Initial source
assessment used `3f4c7d67d`. Current production scope and interface assumptions
are updated below for the 4 November 2026 cleanup.
PR patches are proposals at their
inspected heads, not assumed fixes. This is the disposition of the reviewed cases,
not a claim that every open PR or every backend has been audited.

| Case | Classification and evidence | What remains open |
| --- | --- | --- |
| [AIH-334](https://linear.app/matterlabs/issue/AIH-334) — duplicate initialization windows | **Fixed upstream by [#548](https://github.com/matter-labs/zksync-airbender/pull/548), already present in the base.** The EVM template pins inits/teardowns top bits to deployment constants, rejects preimage values that differ, and uses those constants in the generated gates. The redundant #585 repair and tests are removed. | The [initialization selection interface](Airbender/Review/Helpers/Context/ExternalBoundary/Initialization.lean) retains the formal range/distinctness and layout-correspondence obligation for the selected deployment constants. This is not an outstanding production validation defect in the supported deployment. |
| [AIH-336](https://linear.app/matterlabs/issue/AIH-336) — queryable decoder filler | **Upstream #492 is present in the base.** Untagged decoder padding uses field-minus-one, while tagged tables retain their discriminator and generic zero entry. PR #585 adds no CPU or GPU setup correction. | The temporary [decoder binding](Airbender/Review/Helpers/Context/ExternalBoundary/Decoder.lean) retains full-row extraction, setup authentication, typed queries and committed/preprocessed/backend agreement. Requalification against the restored production functions remains pending. |
| [AIH-339](https://linear.app/matterlabs/issue/AIH-339) — zero-clock workers | **Fixed and verified for the current native BabyBear target.** The adopted #490 timestamp query rejects active zero clocks in all four imported BabyBear families and all 14 cached/no-cache Rust profiles. The historical raw witness is retained and now proved rejected; valid issued execution passes. The original comments' caller-to-worker argument alone did not establish the converse. | [Native occurrence accounting](Airbender/Proofs/ExternalBoundary/NativeRequests.lean) derives the full ledger from accepted constraints and initialized caller binding. The full mixed execution proof uses that derivation. Rust/artifact correspondence and cryptographic enforcement remain external. |
| [AIH-113](https://linear.app/matterlabs/issue/AIH-113) — dropped scaled pointer range check | **Historical compiler bug with repair present in the inspected source.** [Delegation compilation](../../cs/src/gkr_compiler/delegation_circuit.rs) now passes the retained range vector into [memory lowering](../../cs/src/gkr_compiler/delegation_mem_accesses.rs), which pushes the scaled check into it. No live comments. | Do not assume every generated/cached artifact includes that repair. Compiled/artifact correspondence remains an external fidelity obligation; no new pointer-alignment assumption or newly discovered current-source bug is asserted. |
| [AIH-315](https://linear.app/matterlabs/issue/AIH-315) — WHIR randomness reuse | **Upstream correction included in the verified rebase.** The corrected `av_gkr_compiler` target includes the coordinated [#526 correction](https://github.com/matter-labs/zksync-airbender/pull/526) and #527 protocol change. The Linear comment accepting the original freshness defect is unchanged. | The recorded CPU/EVM proof-replay paths pass on this branch. Backend-specific regeneration/compatibility and formal protocol soundness remain separate obligations. The old-pin assessment below is historical; source inclusion and scoped replay are not a general protocol-soundness proof or evidence of a forged proof. |
| F02 — bigint controls | **Excluded by the supported delegation-use contract.** Controls 0 and 65537 remain accepted native/reference discrepancies; [AIH-355](https://linear.app/matterlabs/issue/AIH-355) was canceled on 8 October without comment. | Public supported-use execution requires valid reference-prefix arguments. The lower-level [control binding](Airbender/Review/Helpers/Context/ExternalBoundary/BigintABI.lean) remains available for conditional worker results. Arbitrary native acceptance is not a valid-control check. |
| F04 — worker ROM | **Excluded by the supported delegation-use contract.** COPY with ROM pointers can read zero shadows instead of public bytes; the developers classify these invocations as UB ([AIH-364](https://linear.app/matterlabs/issue/AIH-364)). | Valid use requires RAM pointers. The physical tracked-RAM execution profile and lower-level [RAM-port binding](Airbender/Review/Helpers/Context/ExternalBoundary/WorkerRAM.lean) keep their exact scopes; no general native rejection of ROM pointers is claimed. |
| [PR #531](https://github.com/matter-labs/zksync-airbender/pull/531) — recursive output and branch scratch | **Merged upstream as `06c15f275`. It is in the current base.** The unified branch witness now reads the scratch as a field value. It applies the branch guard before Boolean conversion. The [base entrypoint](../../tools/gkr_verifier/src/common_fsv_unified_base_sec_100.rs) returns the verified registers. The transition prover selects the matching cap computation for stored and recomputed codewords. | Source inspection confirms these changes. New-base artifact regeneration and focused checks remain in progress. Full recursive proof and EVM runtime validation remain pending. |
| [PR #316](https://github.com/matter-labs/zksync-airbender/pull/316) — reduced-load alignment / recursive word 7 | **Reported implementation bugs in another circuit/verifier path.** The patch adds alignment constraints and rejects recursive output words omitted from hashing. | Check the affected v2 path and tests before claiming a repair; the current richer v3 FV relation and its existing alignment proof do not certify that path. |
| [Private PR #8](https://github.com/matter-labs/zksync-airbender-private/pull/8) — FRI degree slack | **Reported protocol bug with a proposed protocol change.** Producer/verifier patches and comments were reviewed; reported CPU tests do not establish protocol soundness or reproducible recursive artifacts. | Cryptographic analysis, producer/verifier agreement and artifact reproducibility remain open for that target. No degree-bound assumption is treated as a fix. |

**Hash witness contracts.** [F11](#f11--hash-witness-contracts-remain-unenforced)
records the four private-witness assumptions used after removal of the G,
extended-round and Keccak circuit patches. Their conditional proof use does not
establish circuit enforcement. Bundle entry and the blessed callers' zero-low-limb rule are recorded separately there.

### Supported delegation use — 27 October 2026

The developers canceled the following reports on 8 October. The agreed proof
domain is programs that use the provided wrapper sequences with valid entry
and runtime arguments, expressed by the public-data
[ValidDelegationUse](Airbender/Review/Trace/UnifiedReduced/DelegationUse.lean) predicate.
This is a program-safety precondition; it does not assert that the verifier
checks the condition. Exact logical matching, public initialization, the modeled
registry and setup/reference fidelity remain separate assumptions. The unified
supported registry contains bigint, G and extended round. The proved full unsigned
target also covers the blessed split Keccak path (F12); special5 retains separate
conditional results and is excluded from the three machine targets.

| Report | Case | 8 October disposition |
| --- | --- | --- |
| [AIH-350](https://linear.app/matterlabs/issue/AIH-350) | Invalid delegation sequence / interior entry | UB; developers provide blessed assembly sequences. |
| [AIH-355](https://linear.app/matterlabs/issue/AIH-355) | Bigint controls 0/65537 (F02) | Canceled without comment; no individual technical explanation is inferred. |
| [AIH-357](https://linear.app/matterlabs/issue/AIH-357) | Extended-round controls | Canceled. Upstream #491 fixes the final-XOR selector. That fix is in the current base. It does not add the absent one-hot rule. |
| [AIH-358](https://linear.app/matterlabs/issue/AIH-358) | Invalid special5 control | UB. |
| [AIH-360](https://linear.app/matterlabs/issue/AIH-360) | G counter outside its schedule | Invalid invocation sequences are UB. |
| [AIH-362](https://linear.app/matterlabs/issue/AIH-362) | Equal G state/message pointers | Developers expect the full memory argument to become unprovable. The complete accepted G-span memory proof now derives separation; the public supported-use domain still retains it. |
| [AIH-364](https://linear.app/matterlabs/issue/AIH-364) | Pointers below RAM (F04) | Properly compiled/linked programs avoid these; otherwise UB. |
| [AIH-367](https://linear.app/matterlabs/issue/AIH-367) | Interior batch entry | Described as divergence between prover CSR calls and simulation. |

These dispositions supersede the earlier requirement to repair delegation
circuits before claiming supported-use soundness. Accepted-relation regressions
remain evidence of behavior outside that domain. The contract includes G's
constant initializer, complete 56/80- and 7/10-call code shapes, single bigint
calls, no interior entry and valid reference-prefix pointers and controls.
Extended-round masks include the blessed callers' zero low limb. G separation
remains a program obligation in the supported-use domain. Separately,
[complete accepted G spans](Airbender/Proofs/Blake2G/BlockFrame.lean) derive it
from initialized memory matching. No circuit, generator or production layout is changed here.

F01's typed verifier-PC interface and F05's contribution-mask interface have
inspected implementation mechanisms, with Rust/argument refinement still external;
their conditional logical results remain checked. F06 is an explicit project/Sail
profile difference. F07/F08's complete-protocol profiles are scope conditions, with
the historical zero-clock exception analyzed under F03; current native
BabyBear constraints exclude active instances. F09's general extraction/fidelity
obligation is distinct from its concrete AIH-336 bug. F10's conditional integration
is now checked in [full mixed execution](Airbender/Review/Trace/UnifiedReduced/FullExecution.lean);
unrestricted acceptance remains wider than the supported-use domain of F02/F04. Historical
progress snapshots below retain their original narrower claims; the F10 section
records the completed connection.

**Assessment of the Linear comments.** All five comments across these five issues
were read; AIH-113 has none, and no comment pages remained.

- **AIH-334, Aleksandr Vlasov, 1 October:** agree that the issue is valid in
  general. Hardcoding production windows is a possible fix only if the actual
  verifier pins valid, disjoint windows for its geometry. Assuming distinctness
  in Lean while accepting duplicate prover-selected indices is not that fix.
- **AIH-336, Aleksandr Vlasov, 1 October:** agree with replacing reachable zero
  filler by a value outside the active query domain. The proposed field-minus-one
  sentinel additionally needs the guarded limb's range and agreement of all setup
  consumers; changing just one representation is insufficient.
- **AIH-339, Aleksandr Vlasov, both 1 October comments:** the initial clarification
  request and subsequent caller/worker explanation were both considered. The
  explanation correctly establishes a worker for each issued call and unique
  issued clocks. **I disagree with treating that argument as sufficient to dismiss
  the finding:** a zero-clock worker's read/write virtual tokens coincide without
  any call. Initialized physical matching excludes two such workers, but the
  pre-fix single-worker state change was valid. The adopted #490 timestamp
  constraint now rejects that worker; it supplies the missing converse used by
  native occurrence accounting. This is a limitation of the original argument's
  scope, not a contradiction of its caller-to-worker implication.
- **AIH-315, Yoav Eshel, 8 October:** agree that the reported digest reuse should
  be treated as a bug needing fresh-digest validation. His comment explicitly
  notes the absence of a known soundness proof and cites WHIR construction 5.1.
  This assessment does not independently prove the paper comparison, a protocol
  attack, or that any proposed transcript patch resolves all producer/verifier
  schedules. No disagreement with the comment's stated caution.

**21 October recheck.** All five Linear issues and their complete comment pages
were rechecked; no new comments change the assessments above. The reviewed FV
source pin for that review was `805909325`; the subsequent rebase target is
`av_gkr_compiler` at `451884662`. The
[validation inventory](VERIFICATION_STATUS.md#current-checkpoint) states the
completed and pending gates; source inclusion is not a full-assurance pass. AIH-315 has a merged upstream correction in
[PR #526](https://github.com/matter-labs/zksync-airbender/pull/526), detailed below;
the former description as simply awaiting a source fix was stale.
[PR #527](https://github.com/matter-labs/zksync-airbender/pull/527) merged on
17 October at head `0603c0f095ed4c5a5b407239907e201ebfbfccc2`: it inherits
#526 and adds a separate seeded-commit protocol change. Both are included in
the rebase. The recorded CPU/EVM proof paths pass; backend-specific
producer/verifier and artifact compatibility remains explicit. [PR #316](https://github.com/matter-labs/zksync-airbender/pull/316)
and [private #8](https://github.com/matter-labs/zksync-airbender-private/pull/8)
remain open at their previously reviewed heads; their proposals and reported
validation are not implementation or protocol-soundness closure for this target.
No new circuit defect was demonstrated by this documentation/source recheck.

Other reviewed PRs do not certify this target: [#209](https://github.com/matter-labs/zksync-airbender/pull/209)
hardens arithmetic in the older Mersenne31 path; [#161](https://github.com/matter-labs/zksync-airbender/pull/161)
changes CLI proof selection. [#426](https://github.com/matter-labs/zksync-airbender/pull/426)
contains historical review examples, which are leads rather than evidence of a
current defect or repair. The PDF in [#301](https://github.com/matter-labs/zksync-airbender/pull/301)
and the full merge in [private #17](https://github.com/matter-labs/zksync-airbender-private/pull/17)
were not audited. No Linear state or PR was changed.

### AIH-334 — fixed upstream by #548

[Upstream #548](https://github.com/matter-labs/zksync-airbender/pull/548), merged
as `f8ed88f68a99bdba3f769bf6cef1472f82b962cc`, is already in the PR base.
The [template](../../verifier_evm/src/templates/gkr.sol) declares one
`__TEMPLATE_INITS_TEARDOWNS_TOP_BITS_` deployment constant per RAM set.
`transcript_init` decodes each full u32 preimage word and reverts unless it equals
the corresponding constant. The
[gate generator](../../verifier_evm/src/generator/circuit_yul.rs) uses those same
constants when computing each set's window, and
[verifier assembly](../../verifier_evm/src/generator/assemble.rs) checks the
configured count and uint8 range. The committed supported verifier pins distinct
windows. Arbitrary prover-selected windows therefore cannot replace them.

**The production item is fixed upstream by #548.** The redundant `de9c7c77b`
repair, its helper module, template/generated changes and tests are removed from
#585. No replacement PR is being opened.

[Initialization.Selection](Airbender/Review/Helpers/Context/ExternalBoundary/Initialization.lean)
still expresses the logical range and distinctness needed by the memory model.
Binding that record and its geometry to the selected deployment constants remains
a formal correspondence obligation, rather than a claim that production lacks
the checks supplied by #548. New deployments must select valid, disjoint windows;
the generic generator's configurable constants are not a proof of every possible
deployment configuration.

### AIH-336 — base sentinel behavior and temporary decoder interface

The current base already uses `generic_lookup_padding` in
[CPU setup construction](../../prover/src/gkr/prover/setup.rs) to fill the
committed tail, and the decoder materializer retains the upstream sentinel
behavior. Those files are restored exactly to the base. The former branch-only
CPU memory optimizations, GPU lookup-domain expansion and associated production
regressions are removed; their old passing results do not qualify this checkout.

The Lean model keeps the **temporary decoder interface assumption** in
[Decoder.Binding](Airbender/Review/Helpers/Context/ExternalBoundary/Decoder.lean).
Its `contents` premise binds complete rows to the public program or an excluded
sentinel, `lookups` binds the actual query to the family table, and `typed`
binds the guarded limb to its native range. Extraction, setup authentication,
and agreement among committed columns, cached preprocessing and scalar/vector/GPU
paths remain external obligations. The restored GPU scheduler retains its base
lookup-length and padding mechanisms; no new runtime agreement or discrepancy
is claimed without validation.

Fresh exports and source receipts must be requalified against the restored
functions. If this exposes a mismatch, record its exact inputs and required
interface property here. Do not change production to satisfy the model. Remove
an assumption only after the relevant production behavior and artifact binding
are validated.

### AIH-315 upstream correction and branch applicability

[PR #526](https://github.com/matter-labs/zksync-airbender/pull/526) merged on
14 October 2026 as `129f827003b34acd64a3315a5863eac75bc09fe6`. Source inspection
at its merged descendant `0603c0f095ed4c5a5b407239907e201ebfbfccc2` confirms that
both affected CPU WHIR call sites use the fresh field-draw helper, which advances
the Blake2s seed before drawing. Both matching verifier-generator call sites use
the helper that advances the transcript before constructing the field element.
The raw-draw API itself intentionally keeps its previous behavior. The initial
review checkout lacked the correction; the rebased `av_gkr_compiler` target at
`451884662` includes both #526 and #527. The recorded CPU/EVM valid-proof replay
passes on that target. Accelerated/backend-specific regeneration and formal
protocol soundness remain outside that local validation.

The PR reports corresponding GPU scheduling changes, unchanged Keccak behavior,
and regenerated BabyBear verifiers/proofs/binaries. Its recorded CI is green,
including tests, GPU checks, verifier regeneration and CLI smoke verification.
Those are upstream validation results, not new local runtime or GPU executions
in this review. The change is explicitly protocol breaking for BabyBear WHIR;
producer/verifier code and generated artifacts must move together. PR #527 adds
a further seeded-commit change and should not be confused with #526's freshness
correction. No formal cryptographic soundness proof or forged-proof reproduction
is claimed. This updates source-fix status without crediting the fix to the
older FV source pin or silently replacing its artifacts.

### Native setup table import — checked

The user authorized exporting and importing complete selected-program lookup
setup, including ROM and decoder rows. The [native exporter](../../prover/src/gkr/prover/setup_artifact.rs)
serializes actual materialized columns and the actual circuit object, with
lossless compression and per-column source checks. [Shared range definitions](Airbender/Review/Helpers/Tables/Range.lean)
now import native 13-/16-/19-bit rows. [Bigint fixed tables](Airbender/Review/Circuits/Bigint/Tables/Setup.lean)
also import all six actual regions: [kernel proofs](Airbender/Proofs/Bigint/ImportedSetup.lean)
recover the exact 1,390,592 rows and native field membership, and the existing carry
and low-byte consumers use those data. No table-equivalence premise or new field
restriction is added. [G controller outputs](Airbender/Review/Circuits/Blake2G/Tables/Controller.lean)
also project imported data; [kernel proofs](Airbender/Proofs/Blake2G/ImportedController.lean)
check every one of the 512 native rows against the existing controller reference
and concrete lookup rows, including key and discriminator. Arbitrary-controller
interfaces, all inactive/invalid controls and existing witnesses are preserved.
[Keccak controller outputs](Airbender/Review/Circuits/Keccak/Tables/Controller.lean)
likewise project the actual native region: [kernel proofs](Airbender/Proofs/Keccak/ImportedController.lean)
check all 4,096 rows, including the key, six outputs, discriminator and complete
inactive/fallback domain. Existing control, physical-slot and worker consumers
use those data with their previous field scopes, interfaces and witnesses.
The five [G XOR regions](Airbender/Data/Setup/Blake2G/XorData.lean) and
[round XOR regions](Airbender/Data/Setup/Blake2Round/XorData.lean) now also
use their own imported rows. [G proofs](Airbender/Proofs/Blake2G/ImportedXor.lean)
and [round proofs](Airbender/Proofs/Blake2Round/ImportedXor.lean) recover all 344,384
fixed rows per artifact, with keys, XOR outputs, padding/tags and native field casts.
Actual lookup/mixing consumers retain their generic fields and arbitrary controller
interfaces. Index hints use exported IDs/offsets.
[Keccak's five fixed regions](Airbender/Data/Setup/Keccak/FixedData.lean)
also import all 1,245,185 real rows. [Kernel proofs](Airbender/Proofs/Keccak/ImportedFixed.lean)
recover XOR/Iota/Chi, both rotation pieces, every key, padding/tag and native cast;
the actual lookup consumers use those rows with their original fields, inverses
and arbitrary controllers. No table-equivalence premise or witness change is used.
Standard fixed and complete selected-program ROM/decoder contents also now import
actual rows. Their relation bridges and native execution adapters pass the full
checks: library, both executables, all 133 concrete test modules, importer
regressions and axiom/review checks. The audit covers 3,624 roots (149 axiom-free);
every previous 3,011 report is exactly preserved, including all 92 axiom-free reports. This work does not close F02/F03/F04 implementation
findings, F09's general query/authentication/Rust-refinement boundary or AIH-336's
pending accelerated/full-proof validation. [Reproduction and scope](artifacts/setup/README.md).

Historical integration and rebased validation checkpoints are retained in the
[findings history](FINDINGS_HISTORY.md).

## Review priorities

| ID | Finding | Evidence/status | Condition or weaker claim that limits coverage |
| --- | --- | --- | --- |
| F01 | Jump terminal PC can be noncanonical locally | Resolved in the logical model under explicit total-verifier boundary binding; original counterexample retained | Canonical u32 contribution closure, cryptographic enforcement and Rust/artifact correspondence remain external |
| F02 | Invalid bigint controls | Excluded by supported delegation use; native counterexamples for 0/65537 remain | Lower-level command contracts stay explicit; arbitrary native rejection is not claimed |
| F03 | Historical active worker without a caller | Native timestamp exclusion, occurrence accounting and rejection/valid-issued regressions are retained; assurance status is recorded separately | Native BabyBear exclusion and initialized caller accounting derive the former external ledger |
| F04 | Worker ROM shadows can disagree with public bytes | ROM-pointer invocations are excluded by supported delegation use; the native COPY counterexample remains | Physical tracked-RAM and lower-level ROM transport retain their separate scopes |
| F05 | Raw inactive rows need not stutter | Conditionally resolved by the external contribution-mask boundary; no demonstrated implementation bug | Exact whole-layout masked closure derives active acceptance/execution; Rust/GKR/cryptographic enforcement remains external |
| F06 | Discarded LW differs from original Sail | Accepted native NOP with no original Sail execution | `NoDiscardedLoads`, or the named Airbender NOP profile |
| F07 | Worker and lower-level integrated claims retain control/participation conditions | Unresolved general binding; discharged in specified stronger scopes | [`OperationInputs.rounds`](Airbender/Review/Helpers/Delegation/Operations.lean), [`Blake2Round.Memory.RoundMask`](Airbender/Review/Circuits/Blake2Round/Memory.lean), [`OperationInputs.keccakActive`](Airbender/Review/Helpers/Delegation/Operations.lean) |
| F08 | Complete hash claims retain protocol shape and first-span restrictions | Public-program binding derives selected span/controller shape and masks; full round-worker coverage remains explicit pending a checked redundancy proof | Mode/duration/preparation, public code profile, controller extents/full coverage and legacy prefix conditions |
| F09 | Setup/decoder queries retain implementation-fidelity boundaries | Actual table contents and semantic connections are imported and checked | Rust/parser fidelity, public-program binding, native query binding and commitment authentication remain external |
| F10 | Caller-cycle effects are weaker than full custom instruction execution | Complete mixed CSR reference execution uses F02 and public protocol/RAM profiles; native participation is derived | General acceptance still admits invalid bigint commands and ROM-shadow behavior; conditional integration does not fix F02/F04 |
| F11 | Hash witness contracts remain unenforced | Four explicit private-witness contracts exclude known accepted cases; circuit patches were removed | Lower-level control/mask premises stay explicit; the supported-use theorem derives G/round contracts under the blessed wrapper domain |
| F12 | Blessed split Keccak | Proved in the full unsigned target; a Review theorem exposes all 361 native calls computing the original permutation | Direct worker constraints/source setup certificates, exact matching and public use remain premises; no split compiler capture and final assurance is pending |
| F13 | Initialization and submitted instance scope | Current targets cover one initialization/teardown instance and a restricted submitted pool roster | Multi-instance aggregation/global window uniqueness and a derivation excluding omitted submitted worker pools remain pending |

Review F01's external correspondence and F02–F04 first. F05 and F06 establish why current
participation/profile restrictions matter. F07–F10 identify assumptions or narrower
conclusions that must not silently become claims of unrestricted acceptance.
Review [F11](#f11--hash-witness-contracts-remain-unenforced) alongside them before
transferring conditional native-path results to arbitrary accepted hash witnesses.

## F01 — Terminal PC resolved under the explicit total-verifier boundary

**Status.** Resolved in the logical model under the explicit total-verifier boundary
binding. The local circuit counterexample remains valid, but is excluded by the
verifier's canonical u32-to-two-limb terminal contribution. Cryptographic
enforcement and Rust/artifact correspondence remain external.

**Evidence.** [JumpSailHistory](Tests/JumpSailHistory.lean)
proves `noncanonical_native_accepted` and `noncanonical_terminal_mismatch`.
The row satisfies imported equations and timestamp queries, original public JAL
decoding, state/memory matching, clock boundaries and actual public initialization.
Its terminal high PC limb is the field encoding of `-1`, outside the 16-bit range;
the interpreted terminal word disagrees with Sail's sign-extended JAL target.
Register-word bounds still hold: this is specifically an endpoint failure.

**Where the bad case is excluded.**
[JumpBranchSlt.TraceInputs](Airbender/Review/Circuits/JumpBranchSlt/Model.lean),
[Standalone jump inputs](Airbender/Review/Helpers/Context/Registries/JumpBranchSltInputs.lean)
and both
[pooled physical/native-boot inputs](Airbender/Review/Helpers/Context/PooledBoundary.lean)
now consume verifier-boundary closure in place of their former direct
terminal-PC and terminal-canonical range fields. The
[public contract](Airbender/Review/Helpers/Context/VerifierBoundary/Model.lean)
keeps typed statement PCs/timestamps and the logical permutation over the actual
imported row starts/ends explicit. Boot inputs fix initial PC/clock to 0/4;
general canonical initial endpoints describe conditional trace/segment scopes.

**Checked connection.** The encoding reuses
[`PCState.boundary`](Airbender/Review/Helpers/Context/PCState/Model.lean) and preserves the
full 32-bit PC in bounded low/high field limbs. Comparing accepted state matching
against the canonical closure and canceling their identical start-list proves
equality of the entire original terminal tuple with the typed contribution.
[`terminal_state_soundness` and `terminal_bound_soundness`](Airbender/Review/Helpers/Context/VerifierBoundary/Theorems.lean)
derive the raw endpoint and its bounds, without truncating/repacking a malformed
pair or supplying its range. Existing intermediate-PC range proofs consume this
derived bound. Purely local calculation lemmas remain conditional.

The [original witness](Tests/JumpSailHistory.lean) still satisfies its original
acceptance relation; `noncanonical_verifier_boundary_rejected` proves that no new
canonical closure can admit it. The [valid JALR fixture](Tests/JalrTrace.lean)
proves `canonical_verifier_boundary` and instantiates the public standalone and
per-circuit soundness claims. Existing branch/comparison and pooled fixtures also
inhabit their replacement contracts.

**Inspected implementation and remaining trust.** The current source inspection
at `9683fe67d16aabadd31140a062082e79c7bccf43` and the earlier inspection at
`0dc0a631349462700825f326516d36200be30edc` are distinguished in the
[source inventory](Airbender/Review/Helpers/Context/VerifierBoundary/README.md#inspected-source-and-external-obligations).
It records unrolled/unified statements, u32 mask/shift encoding, separate PC-space
coefficients/tuples and initial 0/4 constants with exact blobs. The supplied
historical revision `1f4a8455e9f893a1ffb3d23ad79918f243b28aca` is locally
retrievable; retrieval alone is not an audit of that historical execution path.
Logical PC-space matching and Rust/artifact correspondence remain external;
sampled product equality is not deterministic multiset equality.

**Scope distinction.** The separate unified artifact's
[execution_soundness](Airbender/Review/Trace/UnifiedReduced/Theorems.lean)
does not assume terminal-PC normalization. Do not generalize the standalone/pooled
jump counterexample to that theorem. The earlier user-reported circuit bug is
historical context; this investigation establishes conditional logical exclusion,
not a circuit fix, a proved Rust correspondence or an unconditional verifier proof.

## F02 — Valid bigint operation observations do not establish valid calls

**Current disposition.** Excluded by the supported delegation-use domain above,
with valid controls stated on independent reference prefixes. This is a domain
restriction supported by the developers' UB policy, not a pending circuit repair
or a claim of native rejection. The historical counterexamples remain checked.

**Evidence.** [UnifiedDelegation](Tests/UnifiedDelegation.lean)
proves `issued_bigint_without_opcode`, `issued_bigint_high_control` and their
execution/current-fetch consequences. Both cases are live, original-decoded calls
in initialized, exactly matched joint histories. x12 = 0 selects no opcode;
x12 = 65537 selects ADD while retaining a nonzero high control limb.
`issued_bigint_abi_gap_caller_cycles` shows that even current caller-cycle
observations admit both cases. `issued_bigint_pointer_abi` establishes canonical,
aligned, distinct RAM pointers for these same witnesses: fixing the pointer ABI
does not fix control validity. [BigintAbi](Tests/BigintAbi.lean)
also checks the smaller local witnesses.

**Reference discrepancy.** The checkout's
[bigint_impl](../../riscv_transpiler/src/vm/delegations/bigint.rs) asserts an eight-bit
control word and exactly one opcode after removing the carry bit. It rejects
both controls. These Rust assertions are source evidence, not a proved equivalence
between the VM and Lean.

**Why current theorems still pass.**
[Native.operation_execution](Airbender/Review/Trace/Workers/Bigint/Theorems.lean)
proves the existing selected arithmetic effects. It deliberately does not assume a
valid opcode to erase the gap. An implication for each selected operation can hold
when none is selected; current caller cycles likewise do not run the full custom CSR.

**Conditional integration checked.** [Complete bigint calls](Airbender/Review/Trace/UnifiedReduced/BigintCalls.lean)
now derive the successful independent reference transition under the lower-level
valid-command contract. Pointers, actual operands and the complete write/frame
follow from accepted initialized matching; original Sail PC advance retires the
caller. COPY→LW/SW uses these full reference states in the same ordinary history.
The full reference explicitly rejects both controls 0/65537, while their original
native acceptance and observational regressions remain unchanged. This closes
the bigint reference-connection proof task; it does not reject arbitrary invalid
native controls, which are outside the supported-use domain.

**Scope to preserve.** General native acceptance still admits the invalid
controls. Supported-use soundness must derive the actual worker binding from the
public program contract and exact prefix matching; renaming the witness premise
does not supply that derivation. Unrestricted invalid-call behavior is not claimed.
The [supported-use theorem](Airbender/Review/Trace/UnifiedReduced/SupportedUseExecution.lean)
now derives that binding by induction over exact native prefixes; the original
conditional bigint entrypoint remains available.

Lower-level integrated execution also retains the [round-mask witness boundary](#f07--round-selection-and-worker-participation-remain-inputs-in-weaker-scopes); it is not a public input or native acceptance guarantee.

## F03 — Historical zero-clock worker; native exclusion adopted

**Current source and proof.** The rebased `av_gkr_compiler` target includes #490's
active-invocation timestamp query. All 14 native cached/no-cache Rust profiles
reject execute-one/zero-invocation rows and retain valid issued/padding cases.
[Native exclusion](Airbender/Proofs/Delegation/NativeInvocation.lean) proves this
for all four imported BabyBear worker families. The actual query would require
503316480 to lie in the 19-bit range. No positive-clock premise is supplied.
[Native occurrence accounting](Airbender/Proofs/ExternalBoundary/NativeRequests.lean)
then derives the full occurrence ledger from these accepted constraints and
initialized caller binding. The full mixed execution proof and current rejection/valid-issued regressions
pass using this derivation instead of the temporary ledger premise. The full
137-test/library/executable/importer/audit/review validation passes on this pin.

**Historical evidence.** The exact prior accepted witness and its composed
x12 = 0→1 prefix effects remain available in the
[immutable pre-rebase source](https://github.com/matter-labs/zksync-airbender/blob/010c3cbb3c237b6e125277162dd1011c2f212333/formal_verification/lean/Tests/DelegationZeroInvocation.lean).
Its zero-clock issued/empty virtual tokens coincide, so request cancellation
alone never supplied worker-to-caller coverage. Initialized physical matching
bounded this surplus to one; caller-to-worker uniqueness did not exclude it.
The upstream fix adds the missing native constraint.

**Current regression.** [DelegationZeroInvocation](Tests/DelegationZeroInvocation.lean)
retains the same raw row, instruction/core arithmetic, zero G result, token
permutation, virtual cancellation and padding retention. It replaces obsolete
accepted-execution assertions with `active_zero_invocation_rejected` and
`unissued_worker_rejected`. Valid issued G execution and hash coverage remain.
The generic ledger interface and lower-level zero-clock classifications remain
available for profiles that do not select these native BabyBear constraints.
Rust/artifact correspondence and cryptographic enforcement stay external.

## F04 — A valid COPY mode does not bind native worker ROM to public bytes

**Current disposition.** ROM-pointer invocations are excluded by supported
delegation use ([AIH-364](https://linear.app/matterlabs/issue/AIH-364)). The current
physical execution theorem additionally retains its public tracked-RAM domain.
This is not a planned circuit fix or evidence that arbitrary native acceptance
rejects the retained ROM-shadow witness.

**Evidence.** [DelegationROMBoundary](Tests/DelegationROMBoundary.lean)
proves `native_caller_worker_matching`, `public_request_binding`,
`supported_copy_mode`, `worker_accesses_rom` and `public_rom_word_nonzero`.
The decoded caller and COPY worker match with native zero-ROM shadows while the
actual public ROM word is nonzero. `machine_only_rom_lift_breaks_matching` proves
that lifting seed/terminal tokens to public bytes while retaining worker values
breaks the architecture's exact matching.

**Where current claims stop.**
[MixedMemoryInputs.initialization](Airbender/Review/Helpers/UnifiedReduced/MixedMemory.lean)
uses a physical Sail seed image; it does not automatically transport a native
zero-shadow worker pool. The actual VM
[bigint_call](../../riscv_transpiler/src/vm/delegations/bigint.rs) rejects ROM pointers.
The [pointer ABI](Airbender/Review/Circuits/Bigint/PointerABI.lean)
is derived in shared-history claims under a tracked-RAM domain. Its RAM condition
is not established for arbitrary native acceptance, and valid controls alone do
not exclude the COPY fixture.

**Conditional transport scope.** The native worker ports must remain bound to
the RAM-only call ABI. Conditional
[whole mixed-memory transport](Airbender/Review/Trace/UnifiedReduced/NativeMixedROM.lean)
is now checked under the explicit RAM-port contract: public boot inputs derive the
physical initialization, ordinary native ROM slots are interpreted using public
bytes, worker transfers stay unchanged, and accepted shared matching yields one
Sail history with actual worker operations and terminal public cells. Caller
queries/requests, worker assignments and raw PC/clock endpoints are preserved.
The RAM contract is derived in the existing physical tracked-RAM scope; arbitrary
native acceptance does not establish it. This completes conditional composition
without fixing the accepted ROM-shadow discrepancy or validating full custom CSR
retirement. The original counterexample is retained.

Lower-level integrated execution also retains the [round-mask witness boundary](#f07--round-selection-and-worker-participation-remain-inputs-in-weaker-scopes); it is not a public input or native acceptance guarantee.

## F05 — Padding erasure resolved under an explicit contribution-mask boundary

**Local evidence retained.** [InactiveRow](Tests/InactiveRow.lean) checks execute
zero, initial PC zero, final PC four and destination low limb 123 under the retained
local ADD/SUB constraints. This disproves raw stuttering; it does not demonstrate
an implementation bug. The Rust compiler already masks global contributions.

**Checked logical connection.** The user authorized the
[external contribution-mask boundary](Airbender/Review/Helpers/Context/PaddingBoundary/README.md)
on 15 October 2026, analogous to the verifier-PC boundary. Boolean native execute
flags interpret an inactive row's aggregate as identity and retain an active row's
full tuples. Exact masked PC, architectural memory and virtual CSR permutations
keep the whole raw layout and unmasked public endpoints. Erasing identity factors
derives the existing active-trace acceptance contracts and
[whole execution entries](Airbender/Review/Trace/Padding.lean). All raw imported
constraints and retained auxiliary/range/timestamp queries remain checked; active
decoder membership retains its original logical table scope.

**Regression.** [PaddingBoundary](Tests/PaddingBoundary.lean) supplies complete
native clock lookups for the PC 0→4/result-123 inactive case. Two such occurrences
are inserted into the actual initialized [dependent ADD trace](Tests/TraceExecution.lean),
which reaches the same Sail terminal PC/cells. A padding-only forged terminal
transition and a non-Boolean selector are rejected. Active zero-valued tuples stay
present. A colliding scalar encoding does not imply tuple matching. The existing
zero-clock G worker survives projection and both invalid bigint controls inhabit
the new boundary; padding selection is independent of invocation/control validity.

**External trust retained.** The contract is a named theorem premise, not a project
axiom or a proof of Rust verification. It assumes exact symbolic tuple closure
and the binding of compiled masks to actual native execute columns. Product
equality at sampled challenges is insufficient by itself. Address-space
projection, import/compiled correspondence and GKR/cryptographic soundness remain
external. F05 is conditionally resolved at this logical boundary; no inactive
row's desired output or architectural inertness was assumed.

## F06 — The discarded-LW restriction protects a real semantic difference

**Evidence.** [DiscardedLoad](Tests/DiscardedLoad.lean)
proves [`Tests.DiscardedLoad.native_accepts_discarded_load`](Tests/DiscardedLoad.lean),
[`Tests.DiscardedLoad.original_discarded_load_error`](Tests/DiscardedLoad.lean),
[`Tests.DiscardedLoad.no_native_terminal_execution`](Tests/DiscardedLoad.lean) and
[`Tests.DiscardedLoad.profile_terminal_execution`](Tests/DiscardedLoad.lean). An accepted native
NOP has no original Sail execution because the discarded load still performs a
failing memory access. The explicit Airbender profile admits the PC-only NOP.

**Where it is excluded or reinterpreted.**
[NoDiscardedLoads and profileClause](Airbender/Review/Helpers/Decoder/Instruction.lean)
state this distinction. The unchanged-Sail
[ADD/SUB trace theorem](Airbender/Review/Trace/Families/AddSub/Theorems.lean)
requires the restriction; pooled and unified standard execution inputs retain it.

**Closure needed.** Decide which ISA profile is the intended claim and preserve
that choice through fetch and retirement. This is a documented project-profile
difference, not evidence that the declared Airbender-profile theorem is wrong.
Removing the restriction from an original-Sail claim would require new semantics
or proof inputs.

## F07 — Round selection and worker participation remain inputs in weaker scopes

**Condition.** [OperationInputs](Airbender/Review/Helpers/Delegation/Operations.lean)
requires an exclusive
[`Blake2Round.Memory.RoundMask`](Airbender/Review/Circuits/Blake2Round/Memory.lean)
for every extended-BLAKE row and execute = 1
for every Keccak row. The extended-round
[local interfaces](Airbender/Review/Circuits/Blake2Round/Row.lean)
and [Memory interface](Airbender/Review/Circuits/Blake2Round/Memory.lean)
retain the round-mask premise too. Individual boolean bit checks are not the
exclusive-mask ABI specified in [Control.RoundMask](Airbender/Review/Circuits/Blake2Round/Control.lean).

The exclusive mask is also a witness premise in lower-level integrated
[mixed memory](Airbender/Review/Helpers/UnifiedReduced/MixedMemory.lean),
[delegation memory](Airbender/Review/Helpers/Delegation/MixedMemory.lean) and their
native-ROM/shared-operation interfaces. It is not restricted to standalone
workers and is not a public input. Stronger protocol interfaces derive it only
under their stated preparation and coverage conditions.

**What is already discharged.** The initialized full
[compression/boundary/window claims](Airbender/Review/Trace/Workers/Blake2Round/Theorems.lean)
derive masks from their public control/protocol inputs. Prepared unified round
claims derive them from the actual LUI preparation token and matching. The regional
entry derives masks separately inside each caller window before Sail transport;
earlier workers remain in the prefix and every extended-round worker must be
covered by a prepared controller region. Public decoded round CSR coverage now
derives region membership and masks for every issued round worker without
whole-pool coverage. Raw regional mask derivation uses the public memory context
and the derived local scope. Unissued extended-round mask behavior remains outside
this issued result. A separate initialization binding now derives each unissued
worker read and proves that its actual initial x12 high limb equals
`flags + 8 * 2^round` exactly when its native bits form that exclusive mask.
Zero and multibit controls remain unsupported by that ABI. A publicly zero seed
implies no exclusive mask, without asserting an accepted unissued-round witness
or excluding such a worker.
[Blake2RoundCall](Tests/Blake2RoundCall.lean)
checks rejection of a wrong round bit and changed flags under the corresponding
control word. Request checks separately provide participating worker activity.

**Closure needed.** Trace every use of the weaker interfaces to one of those
derived facts or to an explicit supported protocol. General arbitrary-control
and inactive-worker behavior remain outside these stronger scopes. No new
malformed-round counterexample is claimed here.

## F08 — Hash interfaces include restrictions on the witness and its schedule

Full round-worker coverage remains an explicit premise. The former active
zero-clock justification is obsolete for the native BabyBear target (F03).
Deriving coverage from public caller coverage and live-invocation matching is a
separate proof obligation; the existing premise is retained until Lean checks it.

**Condition.** [HashSpan.Protocol](Airbender/Review/Helpers/Delegation/SpanABI.lean)
assumes a homogeneous worker family, initial control/mode and exact call count.
Worker windows add [G prefix completeness](Airbender/Review/Trace/Workers/Blake2G/Windows.lean),
[extended-BLAKE empty prefix and ten-row cap](Airbender/Review/Trace/Workers/Blake2Round/Windows.lean),
or [Keccak empty prefix](Airbender/Review/Trace/Workers/Keccak/Windows.lean).
Prepared mixed scopes add a uniform/straight literal or sequential ordinary/custom program profile,
a worker-free final preparation cycle, selected-span family/count restrictions and
duration equalities. Regional extended-BLAKE composition also requires explicit
controller coverage and a ten-position bound inside each region.
G/Keccak now constrain the family only inside their selected window; other
bigint/G/Keccak workers stay in joint history outside it. Extended-round workers
remain outside that mask-free scope. This adds no bigint opcode-validity condition.
Different literals/registers may appear along the straight path: native PC/clock
matching derives the instruction at each cut. This removes the one-literal registry
restriction without admitting branches or arbitrary final preparations. The
arithmetic extension admits ADD/SUB/ADDI/LUI/AUIPC with arbitrary operands before
the final specified literal. The sequential extension also admits LW/SW, bitwise/
shifts, REV8 and supported TRIADD/XORROT. Its accepted aliased TRIADD→ADDI reset
derives 65537→196611→0 with the same retained clocks and rejects a fabricated read.
Jumps, branches and wraparound comparisons remain outside the linear PC/clock
profile. A separate aligned comparison profile now derives modular RV32 addresses
from the same accepted constraints/matching, with modeled setup and minimum
modulus 4194304 explicit. It derives actual SLTIU→ADDI states 65537→1→0 through
PC `0xfffffffc`→zero, retains clocks six/ten and rejects fabricated reads and
wrong literals. Selected caller/controller regions now support the modular
registry and global public round-CSR occurrence coverage too. Jumps, branches
and nonliteral final preparation remain outside this older preparation profile.
The newer native-path theorem supports branches, jumps and loops under explicit
F11 hash witness contracts. These older results are preparation/memory effects,
not full-prefix retirement. Public
decoded forms and accepted PC constraints derive the preparation address; native selector bits or output values are not
supplied. The accepted aliased ADD→ADDI reset derives actual 65537→131074→0
through one continuous history with clocks six/ten and rejects a fabricated read. Two preparation
cuts also share one intervening native history with both controls derived. Two
complete prepared G/Keccak references now use one continuous chain, with the actual
first finish initializing the gap and second span; their intermediate states,
native tokens, clocks and reference results are derived. This still uses the public
literal registry, ordered aligned cuts and explicit span mode/count/duration.
Arbitrary nonempty ordered lists now share the same continuous execution within
this public prepared G/Keccak scope. The broader prepared protocol entry now
adds extended-BLAKE restarts: raw matching derives masks within each LUI-prepared
caller region with a local ten-position cap. Explicit coverage of all extended-round
workers permits complete lists of all three references in the same continuous
execution. It no longer requires a global empty prefix, homogeneous pool or ten-row
pool bound. Coverage, local family/count/duration and public preparations still
constrain witness shape. Broader preparation/protocol binding remains profile-specific; newer
[actual-path execution](Airbender/Review/Trace/UnifiedReduced/NativePathExecution.lean)
composes caller retirement through branches, jumps and loops under F11. G/Keccak
allow earlier workers; the original first-span extended-BLAKE entry retains an empty
worker prefix while the newer regional entry uses explicit controller coverage; see
[ControlPreparation](Airbender/Review/Helpers/UnifiedReduced/ControlPreparation.lean),
[PreparedHashWindowInputs](Airbender/Review/Trace/UnifiedReduced/PreparedHashWindows.lean)
and [PreparedRoundInputs](Airbender/Review/Trace/UnifiedReduced/PreparedRoundWindows.lean).

These conditions are not all just public initial data: lengths, family membership,
prefix emptiness and duration constrain the accepted worker/machine collections.
Intermediate values, actual cut states and schedules *within that scope* are proved.
The theorem does not derive that every generally accepted execution has that shape.

**Evidence for the limit.** The checked
[`Tests.Blake2RoundCall.completion_does_not_restart`](Tests/Blake2RoundCall.lean)
and [`Tests.KeccakSchedule.completion_does_not_restart`](Tests/KeccakSchedule.lean)
results cover extended-BLAKE and Keccak completion, respectively. Treating
first-span theorems as automatically repeating would be incorrect.

**New public-program connection.**
[ProgramCallerRegion](Airbender/Review/Helpers/UnifiedReduced/WindowSchedule.lean)
constrains public code addresses and CSR families. Sequential public decoding and
accepted native PC/clock matching derive that each selected instruction is a
caller; exact request matching then derives worker family, multiplicity and slots.
[ProgramProtocolWindowInputs](Airbender/Review/Trace/UnifiedReduced/PreparedRoundWindows.lean)
uses public reference duration to derive complete counts. Its sequence entry reaches
all three references at the same actual segment states, without selected worker
family/count premises. `ProgramPreparedProtocolInputs` now also derives local
extended-round shape from public LUI preparation, CSR regions and at most forty
ticks between aligned ordered cuts. Family, the ten-position bound and exact worker
duration follow from native matching; raw matching then derives masks before
transport. `ProgramRoundCallerCoverage` now derives region membership exactly for
live round workers; public preparation and raw matching derive all issued masks
without actual worker coverage or supplied masks. In the weaker interface, full
coverage is equivalent to absence of zero-clock extended-round workers. Current
native BabyBear timestamps exclude active instances; that historical equivalence
is not a reason to retain the premise in the stronger native API. Its checked
coverage implication remains a separate obligation for whole-pool transport. No new unissued
extended-round counterexample is established. The public sequential/code/preparation/
cut profile remains explicit. This does not establish every accepted execution has that
shape, or validate bigint controls or unissued-worker behavior.

The modular selected-region entry now derives the same window and local controller
shape through aligned sequential/comparison code, modeled setup and minimum
modulus 4194304. `WrappedProgramPreparedProtocolInputs` and
`WrappedProgramProtocolWindowInputs` connect those derived scopes to the existing
complete-reference sequence. Public policies quantify addresses at every clock
in each interval, including repeated RV32 addresses; native schedules and worker
counts are conclusions. Global round-worker coverage remains a witness-shape
boundary, and the public global round-CSR coverage/mask result remains linear.
The unissued-round question and whole caller retirement remain explicit boundaries.
Source-aware final preparation is checked; branch/jump preparation extensions
remain outside this older registry. The newer native-path theorem is independent
of that registry and retains the explicit F11 hash witness contracts.

[Issued hash segmentation](Airbender/Review/Trace/UnifiedReduced/Segmentation.lean)
closes coverage for the existing unified public prepared-protocol profile.
`ProgramHashCallerCoverage` quantifies every occurrence of public hash CSR code,
including repeated RV32 addresses; bigint callers may remain in gaps.
`IssuedHashSegmentation` derives unique window assignment, exact worker/request
multiset partitions and the sum of complete-reference call counts through
`Caller.hash_segmentation_soundness`. No selected worker coverage or desired state
is supplied. `Caller.segmented_hash_sequence_soundness`
combines this partition with the existing complete G, extended-BLAKE and Keccak
references at the same continuous-history states. Mode, public cuts/duration,
code coverage, modeled tables, logical matching and the existing global round-mask
scope remain explicit. This does not infer protocol shape from general acceptance.
The weaker unissued-worker interface characterizes uncovered hash workers as
zero-clock residuals; its G fixture changes x12 from zero to one. Current native
active-worker exclusion is separate and rejects active zero clocks (F03). An issued G worker is covered at its
actual clock-five invocation, while its one-call interval cannot satisfy the
56-call reference scope. Missing windows, wrong families, repeated-address omissions
and overlap are rejected. All four COPY/carry/invalid-bigint preparation fixtures
remain admitted outside the hash partition. Whole custom-CSR retirement and
unrestricted invalid-call/ROM behavior remain separate.

**Remaining boundary.** Public code coverage and complete protocol shape remain
explicit. The native coverage implication must be checked before removing a
premise; the old active zero-clock justification is obsolete. Invalid calls are
excluded by the supported-use domain. Whole custom-CSR retirement retains F10's
profile, and further preparation variants are outside this round.

## F09 — Modeled tables and decoder membership can hide implementation mismatches

**Content-model gap closed.** The [complete setup import](artifacts/setup/README.md)
now supplies actual fixed, controller, byte, selected-program ROM and decoder
rows to the circuit consumers. Kernel proofs connect those imported contents,
native IDs/offsets and metadata projections to the existing semantic relations.
The former handwritten-table-content boundary is closed in this published scope;
it is not remaining proof work.

**Retained interfaces.** [PooledHistoryInputs](Airbender/Review/Helpers/Context/Interfaces.lean)
and [OperationInputs.tables](Airbender/Review/Helpers/Delegation/Operations.lean)
still bind the selected setup and public image. Arbitrary public programs are
preserved through explicit program/setup profiles; the retained program corpus
does not replace those scopes. [PooledProgram](Airbender/Review/Helpers/Decoder/PooledProgram.lean)
and request checks retain exact logical decoder-query membership.

**External closure needed.** Formal Rust setup/preprocessing and parser/emitter
fidelity, compiled query placement and cryptographic setup authentication remain
unproved; see [the trust boundary](TRUST_AND_REVIEW.md#modeled-tables-and-logical-arguments).
Importing and checking actual row contents does not prove those connections.
AIH-336's upstream sentinel behavior is in the base; PR #585 adds no production
correction. Requalification of source receipts, fresh exports and backend
agreement after restoring the base remains pending. Decoder interpretation stays
an explicit temporary interface assumption; no new discrepancy is asserted here.

## F10 — Shared cycle composition does not validate the full custom CSR reference

**Checked connection.** [MixedCycleEffects](Airbender/Review/Trace/UnifiedReduced/MixedCycles.lean)
now combines original ordinary/custom retirement, current public fetch,
[caller observations](Airbender/Review/Trace/UnifiedReduced/CallerCycles.lean),
all workers and the complete native PC/clock path over one initialized history.
`Caller.mixed_cycle_soundness` derives reads, operands, decoding and scheduling
under the existing public configuration, tracked-RAM and unchanged-Sail load
profile. The actual final memory agrees with terminal cells in the retired-PC
view of the native path's terminal endpoint. No successful full custom-CSR
reference sequence is claimed by this observational certificate.

**Retained counterexamples.** F02's invalid bigint calls with controls 0 and
65537 instantiate the combined certificate itself. The same assembly also covers
actual COPY→LW/SW retirement. The pinned bigint reference rejects both
invalid controls. Historical accepted zero-clock execution is now rejected by
the imported native timestamp constraints (F03).
Adding ordinary retirement and terminal observations therefore does not supply
full-call control/pointer/invalid-call semantics. The original standard/custom
[Mixed.execution_soundness](Airbender/Review/Trace/UnifiedReduced/Theorems.lean)
continues to exclude delegation callers from its successful-instruction registry.

**Conditional integration.** [Bigint caller retirement](Airbender/Review/Trace/UnifiedReduced/BigintCalls.lean)
now establishes the complete successful reference state transition and PC advance
under the explicit lower-level valid-command contract. Hash-call reference transitions and
whole mixed sequencing are now connected in
[full_execution_soundness](Airbender/Review/Trace/UnifiedReduced/FullExecution.lean)
with participation derived from native constraints and initialized caller accounting. Every ordinary/TRIADD/XORROT and complete
bigint/G/extended-round/special5 Keccak caller step fetches its actual public instruction,
executes in the same full Sail states and retires to the next native PC. The
chain starts at the original public state and reaches actual terminal cells/PC;
it is a [`Trace.Realizes`](Airbender/Review/Trace/Execution.lean) result,
rather than the older observational certificate.
Public initial PC, readonly code/configuration, tracked-RAM domain, modeled tables,
logical matching and the existing complete prepared-protocol profile remain
explicit. Per-row reads, ABI controls, lane bounds, pointer conditions and
intermediate states are derived. The internally derived occurrence ledger
gives total coverage; no positive-invocation premise is added.
The [G](Airbender/Review/Trace/Workers/Blake2G/ReferenceCalls.lean) and
[extended-round](Airbender/Review/Trace/Workers/Blake2Round/ReferenceCalls.lean) and
[Keccak](Airbender/Review/Trace/Workers/Keccak/ReferenceCalls.lean)
worker reference sequences now fix every full Sail micro-call state/frame under the existing complete-span
profiles; they add no per-row control/pointer/result assumption. These bridges
now also supply mixed caller PC retirement. The COPY→LW/SW regression starts
with public PC zero and nextPC 123 and realizes the complete mixed trace.

**Scope closure.** F10's conditional integration retains its stated premises.
F02/F04 are excluded invalid invocations under supported delegation use. Their
lower-level contracts imply neither circuit repair nor unrestricted acceptance. Initialization/teardown now has its separately
checked imported-GKR boundary connection, described below.

**External closure needed.** Bind accepted caller validity to the complete
pinned reference, including invalid calls, or make an explicit reference/scope
decision. Current constraints and matching cannot imply command validity in
the face of F02. Worker ROM binding (F04) needs its stated additional inputs. Inactive
padding (F05) now has the separately authorized conditional logical closure.
Supported-use exclusions and lower-level witness contracts are distinct from
unrestricted native acceptance. The integrated round mask remains explicit.
Generated/import/cryptographic and exceptional-path milestones retain their
separate scope in the [plan](FORMAL_VERIFICATION_PLAN.md).

Lower-level integrated execution also retains the [round-mask witness boundary](#f07--round-selection-and-worker-participation-remain-inputs-in-weaker-scopes); it is not a public input or native acceptance guarantee.

## F11 — Hash witness contracts remain unenforced

**Status.** Supported-use domain boundary; arbitrary native enforcement is not
claimed. The G, extended-round and
Keccak circuit patches were removed; proofs retain the restored native relation.
[HashCommands](Airbender/Review/Helpers/UnifiedReduced/NativeMemory.lean) supplies
four explicitly assumed predicates from
[HashABI](Airbender/Review/Helpers/Context/ExternalBoundary/HashABI.lean).
These restrict private worker-witness reads, including controls and pointers.
They are not public inputs that a verifier can validate independently of a
binding to the witness. They supply no output, intermediate state, reference
execution, occurrence schedule, call count or complete bundle result.

| Contract field | Exact condition and known excluded behavior |
| --- | --- |
| gControl | Every G x12 read is one of the 80 full-mode or 56 reduced-mode controls. The restored circuit retains the fallback for control 80; membership in the successful-call reference is not enforced by that fallback. |
| gBases | Actual G state and message base pointers differ. Equal bases violate the successful-call reference but the restored native relation does not enforce their separation. |
| roundControl | Actual round x12 equals three flags plus exactly one supported round bit, below seven or ten according to mode, with a zero low limb. Individual native Boolean bit checks permit zero/multiple round bits; they are weaker than this exclusive mask. The blessed callers' masks have a zero low limb; the public supported-use contract includes that rule. |
| keccakControl | Actual x10 is one of the existing 649 protocol micro-call controls, including final round-24 Iota. The local native controller permits positions outside that schedule, including the round-31 Chi rollover. |

**Evidence and scope.** [NativeProtocolGap](Tests/NativeProtocolGap.lean) proves
that the assumptions exclude G control 80 and equal bases; its conclusions are
contract rejection, not native rejection.
[KeccakControlUpdate](Tests/KeccakControlUpdate.lean) proves round-31 Chi rollover
satisfies all 187 imported equations and lookups under its explicit permissive
setup. This is a local accepted-relation witness, not acceptance under every native
setup or a complete forged proof. The exclusive-mask difference is visible in the
[round control interface](Airbender/Review/Circuits/Blake2Round/Control.lean) and
[F07](#f07--round-selection-and-worker-participation-remain-inputs-in-weaker-scopes).
The restored fallback controls, aliasing and unsupported masks must not be
reported as rejected merely because the contracts exclude them.

**Bundle entry differs from per-call validity.** G control membership admits a run
beginning at counter 24 and round membership admits an entry at round 3. The
[VM G bundle](../../riscv_transpiler/src/vm/delegations/blake2_g_function.rs) requires
counter zero on entry; the
[VM round bundle](../../riscv_transpiler/src/vm/delegations/blake2_round_function.rs)
requires permutation index zero. Neither entry requirement follows from the four
contracts. The plan-free native-path theorem establishes local successful calls,
not this stricter bundle-entry condition. The
[complete span interface](Airbender/Review/Trace/UnifiedReduced/Paths/Spans.lean)
fixes entry through its per-trace protocol plan. The public supported-use contract
instead prohibits initial/intermediate entry into wrapper interiors and validates
the independent reference-prefix control schedule. These are program obligations
under the developers' contract, not circuit repairs awaiting implementation.

**Required disposition.** Preserve the lower-level conditional worker APIs and
their exact witness premises. The supported-use entrypoint must derive those
premises from public reference-prefix validity and accepted exact matching.
Retain G separation as a public program obligation until the complete-bundle
memory claim is proved. Special5 remains outside the blessed execution scope (F12).

**Native bridge.** The
[supported-use execution theorem](Airbender/Review/Trace/UnifiedReduced/SupportedUseExecution.lean)
takes no bigint/hash witness contract. Its
[prefix construction](Airbender/Proofs/UnifiedReduced/SupportedUsePrefix.lean)
uses accepted state/request/memory matching without a round mask. Induction on
the next instruction's clock proves every earlier worker valid, applies the old
conditional execution theorem only to that strict prefix, and obtains an
independent reachable reference state. Exact frontier tokens identify the next
worker's canonical inputs; public reference-prefix validity then establishes
its controls and G separation. This avoids assuming a full valid memory/execution
history to derive the same validity conditions. Initialization, the physical
tracked-RAM profile and exact logical matching retain their existing scope.

The helper/trace dependency check now passes: HashABI imports circuit-level
protocol definitions directly. The round and special5 schedule definitions moved
verbatim, preserving their public names and bodies. The public supported-use
contract remains in the execution layer. Focused consumer checking does not
establish full review/environment/replay assurance; see the current
[validation status](VERIFICATION_STATUS.md#current-checkpoint).

## F12 — Blessed split Keccak coverage and validation boundary

The full unsigned target is proved with the blessed 361-call split path. Its
[proof](Airbender/Proofs/FullUnsigned/Target.lean) composes the three direct native
worker layouts, fixed-source certificates, exact shared RAM/request matching,
public supported use and one initialization/teardown instance. Parity, theta/rho
and chi5 preserve their grouped timestamp and native port semantics.

The [Review split permutation statement](Airbender/Review/Trace/Workers/Keccak/SplitPermutation.lean)
exposes the existing [native chain proof](Airbender/Proofs/Keccak/SplitNativePermutation.lean):
all 361 actual calls compute Clean's original `Specs.Keccak256.keccakPermutation`, including the
final delayed iota. Initialized histories, exact event matching, public call
arguments, active constraints and physical snapshots remain explicit.

This does not compose split compiler captures: none exist. The three machine
native corollaries certify CPU rows only, while standard worker equations remain
no-cache flat-constraint premises. Unified/reduced have no represented split
pools and assume those submitted instances absent. Special5's separate 649-call
claims remain and the three machine targets exclude its calls.

Final source/frontend validation, environment auditing and full independent
replay remain pending. Earlier gap descriptions are historical; see
[the findings history](FINDINGS_HISTORY.md). They do not describe the proved
full unsigned target's current split coverage.

## F13 — Target initialization and submitted instance scope

**Model scope limitation.** `Airbender.Compiler.MachineTargets.InitializationBoundary` takes one native witness
and one window assignment. The three target proofs support several windows
inside that instance, but not a list of initialization/teardown instances.
The [unrolled verifier](../../full_statement_verifier/src/unrolled_proof_statement.rs)
accepts several standalone instances. The
[unified verifier](../../full_statement_verifier/src/unified_circuit_statement.rs)
accepts several trailing initialization-carrying instances. Both check bounded,
strictly increasing window indices across all contributing instances. Honest
large-memory proofs therefore extend beyond the currently stated Lean scope.

Generalization must aggregate each instance's actual RAM tokens, native gates
and parameters and prove global window distinctness and the combined boot seed.
Until that is implemented, target docstrings, verification status and the trust
guide explicitly retain the one-instance limitation. This is a missing model
composition, not a request to change production or assume its desired result.

**Submitted instance premise.** `workerFamilies` restricts the entire represented
submitted standard-worker pool. Full unsigned has bigint/G/extended round plus
its dedicated split pool; reduced has only extended round. Unified uses the
four-family standard pool. Pools omitted from a target, including split pools
in unified/reduced, are assumed absent. Their absence has not been derived solely
from public no-call conditions, matching and native clock checks. Native
corollaries supply CPU row certificates only; their worker assumptions remain
visible. A broader submitted-instance theorem requires that missing derivation.

## Public decoder model

The production decoder comparison found a model gap at text word 38 of the
pinned OS release. The word encodes MUL. Rust emitted a MUL/DIV row at PC 152.
The earlier Lean model emitted the unsupported sentinel because the original
Sail decoder queries misa. That model admitted only pure decoder trees.

The [public decoder](Airbender/Review/Helpers/Decoder/ProgramRows.lean) now runs
the original Sail decoder in the public initial state. The
[frame proof](Airbender/Proofs/GKRProtocol/StatefulDecode.lean) proves that each
successful decode preserves that state. It adds no expected-instruction or
state-preservation premise. The original Sail clauses, native circuits and
imported values stay the same.

All 14 production decoder comparisons passed in both cache modes. A new small
program checks MUL, MULHU, DIVU and REMU. Its two MUL/DIV comparisons passed.
The [fixture manifest](artifacts/programs/zksync-os.json) pins the public release
assets. This differential result does not establish execution of the OS: its
special5 calls remain outside the machine targets.

## Remaining boundary register

Review these assumptions for applicability. Several are supported public profiles
or logical abstraction boundaries; F11 records the supported-use domain and the
lower-level witness-conditional APIs:

| Boundary | Exact premise or missing connection | Review consequence |
| --- | --- | --- |
| Initialization/teardown | [Imported standalone and inline GKR soundness](Airbender/Review/Circuits/Initialization/Theorems.lean) proves exact products of computed native RAM tokens. [Execution adapters](Airbender/Review/Trace/Initialization.lean) derive the old native seed correspondence, aligned/distinct cells and register coverage from the actual layout and public distinct windows; actual raw teardown columns supply terminal RAM tokens. | Local circuit-to-token correspondence is checked. Public Sail profile, initial PC/clock, configuration/program/setup binding, distinct windows and separate register teardown remain legitimate inputs. Exact logical matching, Rust/parser fidelity and cryptographic enforcement remain external; sampled product equality is not a permutation proof. No new implementation bug is claimed. |
| Memory/fetch configuration | [FlatMemoryConfiguration and PlatformWordAddress](Airbender/Review/Helpers/Memory/Platform.lean) select Machine mode, direct memory, PMP disabled and permissive PMA, with device windows determined by the explicit platform configuration; code bounds/alignment and landing-pad restrictions remain explicit. | These are supported public-profile conditions. Full faults, interrupts, MMIO, other privilege/protection configurations and the full fetch driver are not covered. |
| Independent external input | [ExternalStream.Ports](Airbender/Review/Helpers/Core/ExternalStream.lean) binds responses to an independently supplied stream. | Exact consumption and execution do not authenticate an oracle or establish a particular externally intended stream. |
| Logical matching | [Accepted](Airbender/Review/Helpers/Context/Model.lean), worker matching and request matching are exact permutations of full tokens. | This is the intended premise for the noncryptographic memory-history result. Product/compression equality must not be silently substituted for it; actual global participation and token construction still need their implementation binding. |
| Artifact/reference fidelity | [Import/generation boundary](TRUST_AND_REVIEW.md#import-and-generation-fidelity): richer no-cache import, original Sail generation and project-reference applicability. Base-field arithmetic preservation is proved for 11 cached compilations. Physical-row APIs derive lookup/helper validity from exact emitted-tuple matching; natural multiplicities are not tied to physical counters. CPU native corollaries keep exact public decoder-table binding explicit; worker equations remain no-cache flat constraints and split workers have no compiler capture. [Validation evidence](VERIFICATION_STATUS.md#current-checkpoint) records source/runtime checks and the independent pending assurance gates. | Captured-instance results do not prove universal Rust compiler correctness or cryptographic argument soundness; use the [compiler premise table](Airbender/Review/Compiler/README.md#execution-premises). |
| Delegation-use domain | [F11](#f11--hash-witness-contracts-remain-unenforced) records the lower-level HashCommands fields. The public supported-use contract instead states wrapper shapes, entry safety and valid reference-prefix controls/pointers, including the blessed round masks' zero low limb. | Exact prefix matching derives the bigint/hash conditions for the new supported-use entrypoint. G separation remains explicit; arbitrary native enforcement and blessed split Keccak coverage are not claimed. |
| Keccak wrapper coverage | [Earlier gap](#f12--blessed-split-keccak-coverage-and-validation-boundary). The full unsigned target now covers the blessed 361-call split protocol. | Full frontend validation and transitive replay remain pending. Special5 stays excluded from the targets. |
| Worker clock ranges | [MemoryInputs](Airbender/Review/Helpers/Delegation/Memory.lean) retains clockRoom and invocationHigh: offset-two writes fit in the low limb and the invocation high limb is bounded. | Worker-only memory proofs have these range premises. Integrated caller/accounting claims derive them; no actual read value or pointer bound is supplied. |
| Fields and coefficients | The public claims retain prime-field minima and serialized inverse equalities; bigint's integrated operation proof is BabyBear-specific. | These are arithmetic compatibility conditions, not proof defects. A generic field theorem does not establish the actual Proth120 artifact import. |

## Assumptions that stronger claims already derive

The audit did not find a desired read, final arithmetic result or full memory
history supplied as an independent premise in the six ordinary-family integrated
models. [ADD/SUB's model](Airbender/Review/Circuits/AddSub/Model.lean)
is representative: its mapping identifies native observables and the selected
row's actual prefix state, while initialization and modeled tables are separate.
F01 is the important additional endpoint exception in the jump/pooled scope.

- [Complete memory paths](Airbender/Proofs/Trace/MemoryPaths.lean),
  [latest reads](Airbender/Proofs/Trace/LatestReads.lean)
  and [Clean-consistent history](Airbender/Proofs/Trace/MemoryHistory.lean)
  are conclusions of initialized full-token matching and proved clock laws.
- Actual reads, ordinary operand/immediate bounds, decoder preprocessing and row
  order are derived in the connected ordinary scopes.
- Shared worker histories derive pointer/operand bounds and actual transfers;
  the RAM-only public domain in F04 must still stay visible.
- Issued-worker identity, unique invocation clocks and cycle placement are
  derived. Current native BabyBear constraints additionally exclude active
  zero-clock workers and derive the full occurrence ledger (F03).
- Local G bounds, selected-lane/frame facts and exclusive extended-round masks
  have stronger history/protocol connections. Their presence in a weaker local
  calculation interface is not alone evidence of a circuit bug.

For each remaining premise, ask: **is this genuinely public input/profile data,
a logical global-argument condition, a fact proved by a stronger claim, or a
witness/output restriction still awaiting a binding?** F01 shows why the last
category must never be described simply as public context.

## Validation and next review

[Verification status](VERIFICATION_STATUS.md#current-checkpoint) records completed
and pending gates with their source snapshots. The whole-environment audit,
transitive replay and Linux/CI qualification remain separate from compilation.

Review the public supported-use domain and exact-prefix transport for bigint,
G and extended round, preserving lower-level contracts and native counterexamples.
The integrated witness mask, complete-protocol coverage, source/decoder/setup
fidelity and blessed split-Keccak gap retain their stated scopes. A proof
assumption documents a condition; it does not repair a production defect.
