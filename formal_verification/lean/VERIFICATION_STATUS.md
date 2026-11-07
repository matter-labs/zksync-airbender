# Verification status

<!-- Source-only labels below are modules/namespaces, hash pins, tool tokens,
local binders, or removed/private historical identifiers. Current public
declarations remain required by the compiled reference audit. -->
<!-- source-names:
Airbender.Compiler.ROMNative.WordMemory Airbender.lean AirbenderUnifiedNative BigintMemory
Blake2Round.NativeColumnRows3Part1 ColumnSlices DelegationTimestamps DynamicCopyLoopNative
GKRNativeROM PathGConsumedMessage.Core PathGLoopNativeBase ShiftAssembly ShiftAssembly.lean
Source.ChiCharacters Tests.ArtifactImport Tests.Keccak Tests.KeccakFixture
Tests.NativeCPUFixtures Tests.NativeSetupSemantics Tests.PathGLoopCPU.Equations Tests.Timestamps
Tests.TraceHistory Tests.TraceImport Tests.UnifiedModularExecution
Tests.UnifiedShift.queryValues Tests.UpstreamPlatformCompatibility WordMemoryRows a23f1aa01
a99f6c4ce ba55c93d53f3a689abccf6b628331f9df07ea8c779e3595f0efce04db914df71 c4eb40e66
diagnose_modules e0e5d1815 e89dfdb32 e94380e9f fd7c0fee5 feacc685b notStore parts pidfd_open
prepared_round_masks_soundness start stop workerFamilies
-->

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

Full run [42350890242](https://github.com/matter-labs/zksync-airbender/actions/runs/42350890242)
on signed head 9bdfb988e0dd2ab83bf629d1e5c47f032f69030e failed independent
kernel replay at 22:31:43 UTC on 7 November. The ChiSourceController module
exceeded the unchanged 2,560 MiB charged-memory cap: exit 125 after 13.10
seconds, 2,571.87 MiB charged, 2,048 MiB replay stack, no owned processes left.
The log contains no kernel rejection. There are 7,386 successful replay guards
before this leaf in the 8,381-module compiled DAG. The repaired split slot
cache now passes actual project replay in 13.80 seconds at 844.55 MiB charged;
ChiCharacters passes in 942.69 seconds at 920.25 MiB charged. Complete replay
has not passed, and direct/transitive false-proof controls were skipped.

The repair divides the private 121-row, eleven-column controller calculation
into eleven closed 121-row proofs and an exhaustive column assembly. The
original whole-controller theorem statement, preceding definitions and proofs,
and complete public theorem tail are byte-identical. Review statements and
premises, production behavior, replay/checker policy, resource limits and the
retained axiom baseline remain unchanged. All 923 captured native fingerprint
inputs are byte-identical.

A bounded isolated CORE fixture imports only the pinned Lean 4.31 toolchain.
It copies 807 actual source data definitions and the finite predicate and repair,
retains the certified suffix indices, and compares all 1,331 source controller
values with the corresponding region sliced from the retained native JSON.
All cases compile in 19.95 seconds at 1,033.46 MiB charged, with only propext
and Quot.sound reported. The unchanged replay adapter checks the fixture's
1,013 safe declarations in 6.49 seconds at 1,091.55 MiB charged; two compiler
implementation declarations are skipped, and the fixture declares no axioms.
Changing the final row's final column is rejected by the eleventh column proof
(exit 1, 20.86 seconds, 1,028.69 MiB charged). These Darwin controls use
1,536/3,072 MiB memory limits, a 60-second deadline, the existing process-stack
policy and a 2,048 MiB replay thread stack. Nineteen focused Python controls
and 1,302 guide links/anchors pass. This is isolated evidence, not complete
project validation or Linux replay under the 2,048 MiB process stack.

The failed run's exact diagnostic receipt is inspected: schema 1, commit
9bdfb988e0dd2ab83bf629d1e5c47f032f69030e, run/attempt 42350890242/1, native
fingerprint 93bf55f548def02ee3d55793f6c679d601a089d3028ffb82a90e19016d9ce519,
all 12/16/33/11 checks. Both native stages actually ran. Complete source,
importer runtime, Review, generated freshness, all 126 exact decoder comparisons
across eleven inputs, and the retained-baseline environment audit passed. The
audit retains 5,164 protected roots and covers 229,364 dependencies, with no
missing roots, changed reports, forbidden axioms, unsafe dependencies or
undispositioned changes. These are pre-repair results. A new exact-head full
assurance run with baseline refresh disabled remains required; no final
assurance is claimed.

### Prior split slot cache repair

Full run [42265036454](https://github.com/matter-labs/zksync-airbender/actions/runs/42265036454)
on signed head 964db88d323d7f04a258f38bce28eca1c6d31652 failed independent
kernel replay at 07:06:10 UTC on 7 November. The split slot-reduction module
exceeded the unchanged 2,560 MiB charged-memory cap: exit 125 after 10.50
seconds, 2,560.42 MiB charged, 2,048 MiB replay stack, no owned processes left.
Its log contains no kernel rejection. There are 6,526 successful replay guards
before this leaf in the 8,381-module DAG. The earlier ChiCharacters replay now
passes in 940.05 seconds at 920.14 MiB charged. Complete replay has not passed;
direct/transitive false-proof controls were skipped.

The repair decomposes the private whole-cache calculation into twenty-four
fifteen-entry proofs and one final-entry proof, then proves the original
361-entry theorem from all twenty-five blocks. The literal slot cache, original
whole-cache theorem statement and complete public theorem/normalization tail
are byte-identical. Review statements and premises, production behavior,
replay/checker policy, resource limits and the retained axiom baseline remain
unchanged. All 923 captured native fingerprint inputs are byte-identical.

A bounded isolated CORE fixture with the pinned Lean 4.31 toolchain checks the
exact finite slot definitions, cache and repaired proof in 7.09 seconds at
427.10 MiB charged, with only propext and Quot.sound reported. The unchanged
replay adapter checks that compiled fixture's 520 safe declarations in 5.42
seconds at 821.05 MiB charged, with no owned processes left. These local Darwin
controls use 1,024/2,048 MiB memory limits and a 60-second deadline; the replay
thread stack is 2,048 MiB and the process stack follows the existing Darwin
policy. A changed final cache row is rejected in the final one-entry block
(exit 1, 7.05 seconds). Nineteen replay, axiom-report and proof-boundary Python
controls pass. This is isolated evidence, not a full project replay; Linux
replay under the unchanged 2,048 MiB process stack remains required in CI.

The failed run's exact diagnostic receipt is inspected: schema 1, commit
964db88d323d7f04a258f38bce28eca1c6d31652, run/attempt 42265036454/1, native
fingerprint 93bf55f548def02ee3d55793f6c679d601a089d3028ffb82a90e19016d9ce519,
all 12/16/33/11 checks. Native generation and compiler capture actually ran.
Complete source/runtime/Review, generated freshness, all 126 exact decoder
comparisons across eleven inputs and the retained-baseline environment audit
passed. The audit retains 5,164 protected roots and covers 229,263 dependencies,
with no missing roots, changed reports, forbidden axioms, unsafe dependencies
or undispositioned changes. These are pre-repair results; a new exact-head full
assurance run with baseline refresh disabled is required. No final assurance
is claimed.

### Prior replay repair and retained baseline

Final full run [42194460969](https://github.com/matter-labs/zksync-airbender/actions/runs/42194460969)
on signed head b29277dd895499574e317a994fd89243a72f06cb passed fresh native
qualification, complete source/runtime/Review, generated freshness, decoder
differentials and the fixed-baseline compiled environment audit. The actual audit
retains all 5,164 protected roots and 229,263 dependency declarations, with no
forbidden axioms, unsafe proof dependencies, missing roots or changed reports.
Its child exited 0 in 248.11 seconds at 1,324.83 MiB charged footprint.

Independent replay then failed at 17:35:29 UTC on 6 November. The exact
ChiCharacters source-binding leaf reached the shared helper's 900-second limit:
exit 125, 900.23 seconds, 920.22 MiB charged footprint, 2,048 MiB stack and no
owned processes left. Its log contains no kernel rejection. The retained artifact
contains 3,935 successful replay guards before that leaf in the 8,381-module
compiled dependency DAG. This is partial replay evidence; there is no completion
certificate, and direct/transitive false-proof controls were skipped.

The repair applies the existing named 1,800-second ChiCharacters allowance to
that exact replay leaf. Inventory jobs, neighboring modules and ordinary audit
calls retain 900 seconds. Memory caps remain 2,560/5,120 MiB and replay stack
remains 2,048 MiB. The named timing policy is included in ledger identity; safe
declaration coverage, import ordering and fresh project replay are unchanged.
No Lean statement, proof, premise, baseline, production function, native input,
workflow or axiom policy changes. All 923 captured native inputs are byte-identical.

Six replay controls pass, including execution of the driver over a simulated
compiled DAG: only the exact replay leaf gets the allowance, not its inventory,
suffix/nested names or dependencies. Actual guard argument parsing retains both
memory caps and stack; an unsuccessful fake child still fails. Six axiom controls
also pass. The existing guard suite passes 30 controls with four Linux runtime
controls skipped locally. These are lightweight controls, not a successful Lean
replay. A new complete full assurance run with baseline refresh disabled remains
required; no final assurance is claimed.

Run [42183091911](https://github.com/matter-labs/zksync-airbender/actions/runs/42183091911)
on signed head e9f9354f8854e1dcf5ff10900d566c457b0adcd0 passed every warm
verification gate. Fresh native qualification completed at 08:05:15 UTC on
6 November; its exact receipt was inspected. The complete source/runtime/Review
frontend passed in 365.48 seconds, followed by generated-source freshness and
all 126 exact decoder-row and circuit-object comparisons across eleven inputs,
including the production OS program. The exporter prerequisite exited 0 through
the native guard; every decoder guard left no owned processes.

The separate compiled environment audit passed at 09:09:30 UTC: 5,164 roots and
229,263 dependency declarations, no forbidden axioms or project axiom declarations,
no unsafe proof dependencies, no missing protected roots and no undispositioned
report changes. Its Lean child exited 0 after 247.87 seconds at 1,329.04 MiB
charged footprint, with no owned processes left. The direct smoke reports cover
173 requests; Review validates all 4,205 source targets and 170 public theorems.
Ordinary checks also completed without failures on this exact head.

The [retained baseline](scripts/axiom_baseline.json) is the exact refreshed JSON
from that successful audit, SHA-256
f84e619abb15374a4e6bbcc6ea246c0f7c257fe4c8658866bb1f6b110e38520e.
All 5,164 current roots are protected; every previously protected root remains
present, and reports for shared roots are unchanged. This baseline/status revision
requires final full assurance with baseline refresh disabled. Independent complete
dependency kernel replay and direct/transitive false-proof controls were disabled
in the warm run and remain pending; no final assurance is claimed.

Warm CI now separates native qualification from Lean proof validation. An exact
input fingerprint and completed native receipt can omit repeated Rust generation
and compiler captures after proof-only edits. Strict retained-source/payload
checks still run; missing or changed evidence requires fresh native work. The
first run must populate the small receipt cache. Full assurance, cold builds and
setup requalification always retain fresh native generation. Run
[42008848844](https://github.com/matter-labs/zksync-airbender/actions/runs/42008848844)
on `5a255e6103bc49f5f321601b8c72829e166cbc90` passed fresh native generation,
compiler capture, immutable-input revalidation and receipt publication. The saved
receipt was inspected in its diagnostic artifact. Run `42151721613` later reused
the exact completed native receipt from `42037931876` after strict current-input
validation; its retained receipt and reuse decision were inspected. This is reuse
of qualified evidence, not fresh native generation on the later head.
The older `41987147083` was cancelled with user authorization.

Run `42008848844` then hit the 10,800-second preliminary fixture-stage deadline,
while normally compiling `Blake2Round.NativeColumnRows3Part1`. The last guard
reported SIGTERM at 340.77 MiB charged footprint and no owned processes left;
no proof-error result is claimed. The retained records contain 682 source-build
and 682 query-pool entries; the full-project frontend had not started. GitHub
successfully saved a 3,222,126,071-byte Lean snapshot after this failure.

The retry moves the same four fixture closures to the front of the existing
complete source pass and removes the duplicate preliminary pass. All 4,205
modules in the actual CI import graph remain present exactly once and every
import precedes its user. Thirty-six focused controls, the real-graph ordering
check and workflow lint pass. No Lean source or Review statement changes.
The full pass retains its 54,000-second stage deadline, per-child time/memory
guards, final freshness/hash checks and all runtime/audit/replay obligations.
This scheduling repair requires CI validation; final full assurance is pending.

Run [42037931876](https://github.com/matter-labs/zksync-airbender/actions/runs/42037931876)
on `18f8c733f9bce1ebb3d81d5da452b5cc64d82aa0` passed all four prioritized
fixture modules and fresh native qualification. The complete source pass then
failed after 45,033.32 seconds in `Tests.ArtifactImport`: the runtime import
cleanup had removed the indirect provider of `Airbender.MulDiv.importedConstraints` and
its source bytes. The failed leaf exited normally with code 1 after 4.74 seconds,
at 350.62 MiB charged footprint, with no owned processes left. This was a missing
import, not a resource deadline. A direct import of the existing MulDiv artifact
restores those declarations without changing any assertion or proof statement.
A regression control checks all eleven referenced artifact providers through the
runtime import closure and rejects the original missing MulDiv import. All 37
focused controls pass locally. Actual repaired Lean source/runtime validation,
the environment/axiom audit and final full assurance remain pending.

Run [42151721613](https://github.com/matter-labs/zksync-airbender/actions/runs/42151721613)
on `06d7f3ff30dcae43e2af8fc362be2633b19c35b4` completed normal Lake source
freshness for all 4,205 project modules, native freshness for the 2,132-module
runtime closure, and the library/executable builds. The direct Lean axiom command
exited normally after 5.38 seconds at 360.25 MiB charged footprint, with no owned
processes left, and reported only the three permitted axioms for all six requests.
The Python smoke comparison then incorrectly required all 4,379 roots from the
separate compiled-environment baseline in that six-root log. No runtime execution
or environment audit success is claimed. The repair compares the smoke inventory
against its exact source requests, including any requested baseline roots; the
separate full environment inventory/baseline audit is unchanged. Retained-log
replay and 42 focused controls pass, including missing/extra/duplicate/forbidden
smoke-report controls and rejection of a missing protected Review audit root.
Actual complete runtime/audit validation and final full assurance remain pending.

Run [42164820299](https://github.com/matter-labs/zksync-airbender/actions/runs/42164820299)
on `3251f7357cd40f7f256118045121397d1e257a95` passed fresh native qualification,
recorded an inspected exact receipt, and passed the repaired six-root axiom smoke
check. The complete frontend then failed after 149.52 seconds in importer runtime.
The runtime child exited 1 after 12.67 seconds at 485.96 MiB charged footprint,
with no owned processes left. The AddSub embedded-circuit round trip emitted
`aux_layout_data.relative_timestamp_groups: null`, while Rust omits this vector
when empty. A bounded Lean core replay of the original serializer against the
actual AddSub artifact isolates exactly that one extra JSON field. The repair
omits absent and empty groups, retains nonempty groups and every other value,
and preserves the full circuit-equality assertions. Twenty checks using the exact
schema/serializer bodies and runtime assertions pass against the actual AddSub
and Bigint artifacts in an isolated core fixture (2.57 seconds, 364.29 MiB charged),
along with all 42 focused Python controls. No project build was run locally.
The new runtime branch controls cover absent, present-empty and nonempty groups,
other auxiliary values, absent/present padding, and other explicit null fields.
Complete project runtime, generated/decoder, environment/axiom audit and final
full assurance still require CI success on the repaired revision.

Run [42168019177](https://github.com/matter-labs/zksync-airbender/actions/runs/42168019177)
on `47cee2b649eec33d2570c015a74176e53291bf4e` passed the complete importer runtime,
including both retained circuit round trips and the new timestamp-group controls.
The runtime child exited 0 after 44.34 seconds at 486.59 MiB charged footprint,
with no owned processes left. The frontend then failed after 380.37 seconds in
the independent Review snapshot checker: it discovered 4,204 modules while the
complete checked snapshot contains 4,205. The sole difference is the configured
program-row oracle executable, outside the library/test/Sail directories. The
repair independently reads executable roots and source directories from the
current Lake configuration, retaining exact source/object/import inventory
equality and all freshness, frozen-input, hash and receipt checks. All three
inventories now match all 4,205 modules in the retained CI snapshot. All 46 focused
controls pass, including configured source-directory handling, missing/conflicting
runtime roots, and dropped/invented source/object/import inventory rejection.
No Lean source, runtime assertion, Review statement/premise or resource gate
changes. The complete Review/environment audit and final assurance remain pending.

Run [42170297273](https://github.com/matter-labs/zksync-airbender/actions/runs/42170297273)
on `8ac91061986fd4358fb009af006eccb130c9a284` passed fresh native qualification,
complete source/native freshness and importer runtime. The runtime child exited
0 after 45.71 seconds at 495.45 MiB charged footprint, with no owned processes
left. Review then validated all 4,205 snapshot modules and nine actual snapshot
mutation controls, confirming the executable-inventory repair. Its next compiled
inventory failed because the generated Sail guide linked a removed compiler
compatibility module. The Review child exited 1 after 47 seconds at 197.67 MiB
charged footprint, with no owned processes left; no resource or proof error is
claimed. The guide now links the current platform-polymorphic compiler target
corollaries and an existing native platform application. Three stale historical
anchors also point to their current sections. All current guide links,
anchors pass (1,301 links), and all 453 compiled Review inventory imports occur
in the checked CI module inventories. All 46 focused controls pass locally.
No Lean source, statement, premise, checker or resource gate changes. Complete
Review/environment audit and final full assurance remain pending.

Run [42173778146](https://github.com/matter-labs/zksync-airbender/actions/runs/42173778146)
on `171fc137fd2516aaafebb68abdd8b5620864e97e` reused the inspected exact native
qualification receipt from the preceding run. Source/native freshness, importer
runtime (43.55 seconds, 486.43 MiB charged, no owned children left), snapshot
identity and all nine snapshot mutation controls passed. The compiled Review
inventory loaded successfully, confirming the removed-module link repair. The
frontend failed after 351.74 seconds because guide reference validation reported
125 missing/ambiguous references. The Review child exited 1 after 93.16 seconds
at 507.09 MiB charged footprint, with no owned processes left. The diagnostics
include module/namespace labels, hash pins, tool tokens, local binders and removed
or private historical names. The existing per-guide source-name metadata now
explicitly classifies those 101 source-only reference occurrences. Current public
declarations use fully qualified names, including the three ambiguous short-name
diagnostics; all 16 resulting declaration names remain required by the checker.
The historical local start binder is separately classified as source-only.
Retained-diagnostic classification, all 1,301 guide/history links, 453 current
inventory imports and all 46 focused controls pass locally. Only documentation
changes; the compiled reference checker, theorem coverage, proof interfaces and
all resource/trust gates remain unchanged. Actual compiled reference validation,
complete Review/environment audit and final full assurance remain pending.

Run [42176369285](https://github.com/matter-labs/zksync-airbender/actions/runs/42176369285)
on `980baaa5511adccec9540b81e53bf7678171a197` passed fresh native qualification
and the compiled guide-reference check, confirming the documentation repair.
Complete importer runtime passed (44.24 seconds, 491.62 MiB charged, no owned
children left), along with source/native freshness, all 4,205 snapshot identities
and nine mutation controls. Review then found 167 source-declared public theorems
missing from the explicit axiom-report requests. Its child exited 1 after 96.26
seconds at 508.39 MiB charged footprint, with no owned processes left; the frontend
failed after 358.04 seconds, without a resource or proof error.
The lookup-binding generator had retained only the six target requests. It and
the generated audit now retain those six unchanged and add the 167 missing
explicit reports, for 173 unique requests. All 357 current Review modules were
already imported, so the import closure does not grow. Only reporting commands
are added; no theorem statement, proof, premise or axiom is introduced or changed.
The regression uses the real split-permutation statement's source range and
rejects an omitted or duplicate audit request. All 47 focused controls pass,
including generator freshness. Expanded-inventory parser controls reject missing,
extra, duplicate and forbidden synthetic reports; these are not actual theorem
axiom results. Actual expanded Lean reports, complete Review/environment auditing
and final full assurance remain pending.

Run [42180089232](https://github.com/matter-labs/zksync-airbender/actions/runs/42180089232)
on `895796d5866a6bd8f48398ffc4140d86d0256b64` passed the complete source/runtime
and Review gate in 417.25 seconds. All 173 explicit reports contain only the three
permitted axioms; Review covers 170 public theorems and 210 contextual guide
declarations. Runtime exited 0 after 43.37 seconds at 515 MiB charged footprint;
Review exited 0 after 94.93 seconds at 505.81 MiB. Both left no owned processes.
Generated source freshness also passed. The decoder differential then failed
before a guarded comparison: native qualification reuse skipped the Rust cache
and builds, while the stage required the setup exporter executable. The retained
filesystem footprint confirms the setup and compiler target directories absent.
No decoder row mismatch or resource failure is claimed.
The decoder stage now builds the existing setup-exporter example through the
native aggregate guard before requiring its executable. Cargo is scoped, locked
and serial, with CI and the Rust stack override unset; it also revalidates any
restored binary. Existing native memory/time/capacity/lock limits and all decoder
comparisons remain unchanged. Fixtures execute the actual workflow prerequisite
with isolated fake Cargo for absent/restored binaries and reject build failure
or a missing executable output. All 55 focused controls, shell syntax and YAML
parsing pass; actionlint adds no findings beyond its two unchanged runner/action
baseline findings. No local Cargo or Lean build was run. This workflow change
changes the conservative native fingerprint, requiring fresh qualification again.
Actual repaired decoder execution, environment auditing and final full assurance
remain pending.

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
existing `Airbender.UnifiedReduced.Caller.Proofs.prepared_round_masks` directly, with the same arguments,
premises and conclusion. The leaf exited 1 in 37.01 seconds at 917.14 MiB, with
no owned processes left. No resource or trust gate was involved. The repair
requires another Lean diagnosis; full verification and assurance are pending.

A declaration audit also found three obsolete public alias names used by
connected tests. Eight preparation proofs now compose their existing
`Airbender.UnifiedReduced.Caller.HashControlPreparation` source certificates with the current public
`Airbender.UnifiedReduced.Caller.hash_control_preparation_soundness` theorem. Two caller-cycle tests call the
existing `Airbender.UnifiedReduced.Caller.Proofs.caller_cycles` theorem with their original arguments.
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
the existing `ColumnSlices` projection theorem import for `Airbender.Compiler.MaterializedLookupSetup.generic_cell_value`.
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
Its test adapters now target actual `Airbender.UnifiedReduced.BootInputsWith` and `Airbender.UnifiedReduced.ExecutionInputsWith`.
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

The runtime executable also needs only the permissive setup value from
`Tests.Keccak`. That definition now lives in `Tests.KeccakFixture`, imported by
both consumers under its unchanged name. Its definition, both consumer bodies
and all runtime assertions are byte-identical. The same CI import graph predicts
that extracting this fixture removes another 517 existing project dependencies
and adds one fixture module, reducing the executable closure from 1147 to 631
modules and removing all generated Sail modules from that closure. Complete
source, compiled environment audit and final kernel replay still include every
proof and all 250 test modules. This predicts less native compilation work;
CI compilation, actual runtime execution and timing remain unqualified.

`Tests.TraceImport` also imported `Tests.Timestamps` and `Tests.TraceHistory`
without referencing their declarations. Removing those two imports preserves
its entire body, including its focused `#eval run`, and removes another 406
project modules from the executable closure: 631 becomes 225. Neither removed
test declares an explicit initializer, instance, syntax extension or attribute.
Both tests remain independently included in complete source validation, compiled
environment audit and final kernel replay. Native compilation and elapsed-time
confirmation still require CI; the active older warm run predates these changes.

The guarded frontend now prints each stage start, concrete leaf target, elapsed
time every 30 seconds and child exit code into the live Actions log. Query pools
also report their target count and first/last target. Detailed logs and resource
receipts remain in diagnostics. A real lightweight child control checks that
progress polling preserves complete output and a nonzero exit; an interruption
control checks that exceptions still reach the existing child cleanup. Existing
resource limits, guard receipts, freshness checks and assurance gates are unchanged.

Cancellation diagnostics from
[41963487081](https://github.com/matter-labs/zksync-airbender/actions/runs/41963487081)
show source-object freshness and compiled hashes completed before native work.
The retained records include six source builds (43.96 guarded seconds), 1980
native object builds (2569.91 guarded seconds) and 3943 recursive freshness-query
steps (4349.12 guarded seconds). These guarded durations exclude orchestration
overhead and do not sum to elapsed wall time. The interrupted source/runtime stage
had reached 12202.88 seconds; no runtime or environment audit pass is claimed.

The frontend now uses explicit native-object misses in normal Lake diagnostics
as build candidates. Each candidate still gets the same ordinary guarded leaf
build, followed by a normal query of the entire failed chunk and the existing
final freshness query. Missing or incomplete diagnostic hints retain the original
bisection fallback. Hints never attest freshness, change guard limits or skip
the compiled-object hashes. Controls cover complete and incomplete hints and
reject candidates outside the requested native-object targets. CI qualification
and elapsed-time measurement of this optimization remain pending.

A static runtime audit also found two stale importer expectations: unified CPU
equations were 129 rather than the native 120, and bigint equations were 136
rather than the native 135. The checks and labels now use the actual producer
counts. A new preflight derives 23 metadata/query-count checks across nine
native JSON artifacts; its negative control rejected both old expectations.
All runtime assertions remain present. No production or Review change is needed;
the revised runtime executable still requires CI qualification.

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
3. Retain the exact refreshed baseline from the passing warm environment audit,
   then run full assurance with transitive kernel replay and the false-proof
   controls on the signed final revision. Use a 2,048 MiB stack and disable
   baseline refresh for this final check. Weekly default-branch runs also include
   assurance. Request a cold source benchmark separately when new performance
   data is needed.
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
| CI full frontend and runtime gates, run 42183091911 | Passed | 365.48 | 790.46 |
| CI environment audit and baseline refresh, run 42183091911 | Passed; exact baseline retained | 247.87 | 1,329.04 |
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
