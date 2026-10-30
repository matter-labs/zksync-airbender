# Findings: assumptions and circuit bindings

<!-- source-names: keccak_special5 keccak_f1600.rs keccak_special5_layout_no_caches_gkr.json KECCAK_COLUMN_PARITY_CSR_REGISTER KECCAK_THETA_RHO_CSR_REGISTER KECCAK_CHI5_CSR_REGISTER KECCAK_SPECIAL5_CSR_REGISTER SUPPORTED_CSRS -->

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

## Kernel fixed-setup provenance

The full unsigned target has an unresolved fixed-setup binding. `FixedSetup`
describes parsed JSON. `Setup.parse` calls `Lean.Json.parse`. Its `anyCore`
worker is opaque in the kernel. A focused probe confirms that even an empty
JSON object does not reduce through this parser in a kernel proof.

The imported table facts need a proved source-to-data bridge. A runtime parse
check cannot close this kernel obligation. Keep the target premise and axiom
policy unchanged. This binding gap does not establish a circuit failure.

Kernel checks now cover full native execution and public supported-use
induction. The target wrapper exposes one source-interpretation function.
This function must connect parsed fixed JSON to the canonical tables.

The setup transport proof now covers all three workers in both cache modes.
Three `FixedSetupRows` certificates suffice for the original target. Each
certificate must map every parsed physical row, including padding, into its
complete canonical table. Parity, theta/rho and chi5 certificates remain open.
No new assumption closes them.

A total JSON decoder prototype stays outside the branch. Small kernel tests
and differential checks of all 18 retained setup-directory JSON files pass.
Direct kernel evaluation of the complete theta/rho source exceeds the fixed
memory cap. A compact source certificate is still required. The retained
artifacts, setup parser and imported values stay unchanged.

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
assessment used `3f4c7d67d`; the AIH-334 fix below builds on `73c632e89`.
PR patches are proposals at their
inspected heads, not assumed fixes. This is the disposition of the reviewed cases,
not a claim that every open PR or every backend has been audited.

| Case | Classification and evidence | What remains open |
| --- | --- | --- |
| [AIH-334](https://linear.app/matterlabs/issue/AIH-334) — duplicate initialization windows | **Fixed in the current EVM generator and both tracked GKR sources; validation below.** The Linear comment correctly accepts the original defect as “Valid in general.” [Generated validation](../../verifier_evm/src/generator/initialization.rs) now rejects duplicate/out-of-range windows before transcript processing. The [Rust unified statement](../../full_statement_verifier/src/unified_circuit_statement.rs) separately checks range and increasing order. | The [distinct-selection contract](Airbender/Review/Helpers/Context/ExternalBoundary/Initialization.lean) remains explicit: its formal correspondence to EVM execution is unproved. Valid sparse windows 254/255 and reversed distinct pairs are retained for the 2^22-word/four-byte geometry. Existing deployments are not changed by this source fix. |
| [AIH-336](https://linear.app/matterlabs/issue/AIH-336) — queryable decoder filler | **Upstream #492 supplies the fix.** It sets each untagged decoder padding column to field-minus-one. This fix is in the current base. Tagged tables keep their discriminator and generic zero entry. The native forward code computes the padding fill from the circuit metadata. | The branch removes its redundant full-domain CPU lookup cache. The focused regression compares the forward relation with every row in the native test fixtures. New-base accelerated runtime tests and a complete proof run remain pending. The external [decoder contract](Airbender/Review/Helpers/Context/ExternalBoundary/Decoder.lean) still needs extraction, authentication and query binding. |
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
registry and setup/reference fidelity remain separate assumptions. The current
covered registry contains bigint, G and extended round. Blessed split Keccak is
uncovered (F12), while special5 has only its existing conditional results.

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
[validation inventory](VERIFICATION_STATUS.md#validation-evidence) states the
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

### AIH-334 implementation fix and validation

The [emitter](../../verifier_evm/src/generator/initialization.rs) derives window
size from the artifact's trace length and word bits, and set count from its
teardown layout. A 2^22-row/four-byte-word window occupies 2^24 bytes, so the
exclusive top-index bound in the u32 byte-address space is **256**, not 64.
The [live template](../../verifier_evm/src/templates/gkr.sol) invokes validation
before transcript copying or hashing. It checks that all index bytes exist,
decodes each complete little-endian u32, checks range and rejects every duplicate
pair. It does not truncate indices, assume contiguity or require ordering.

Both tracked [merged source](../../verifier_evm/generated_contracts/merged/src/GkrWhirVerifier.sol)
and [replay fixture](../../verifier_evm/generated_contracts/merged/test/fixtures/GkrWhirVerifierFixture.sol)
carry the same emitted guard and invocation; a regression compares their decoder,
validation and transcript-init functions to fresh generation. Other generated
circuits, contracts and proof/cache artifacts are unchanged.

The [Rust/EVM regression](../../verifier_evm/tests/initialization_windows.rs)
compares both committed entrypoints' guards and transcript initialization to fresh
generation, and compiles the fresh verifier and committed replay fixture with Solidity 0.8.36.
It executes the actual generated guard in the
[EVM suite](../../verifier_evm/tests/contracts/InitializationWindows.t.sol): valid
sparse/reversed windows, duplicates, both out-of-range positions, high-byte/LE
decoding, truncated input, adjacent-byte independence and two 256-run fuzz tests.
The existing valid merged proof is replayed through the fresh verifier and committed
fixture. On the rebased `451884662` target, both Rust tests and all eight Solidity
cases pass, including the two 256-run fuzz tests. The main production contract has
a different terminal PC; its guard is compared, with no production-proof replay claimed.
The local macOS run disabled Rust debug information for the
[prover](../../prover/Cargo.toml) and
[keccak_special5](../../circuit_defs/keccak_special5/Cargo.toml) crates to avoid
the pinned nightly compiler's debug-info crash.
Full FV validation of the rebased branch remains in progress.

This fixes the source-level AIH-334 validation defect for the current single-proof
EVM target. It does not prove EVM/Rust/Lean refinement, cryptographic soundness or
correctness of other verifier paths, and does not upgrade deployed contracts.
The Lean selection premise stays visible for that unproved formal connection;
the other implementation findings remain open. The Linear assessment above is
unchanged: explicit validation implements the required property without pinning
production indices to constants.

Reproduce the scoped EVM regression with Foundry and Solidity 0.8.36 installed:

```sh
cargo check --locked -p verifier_evm --lib
SOLC_PATH=/path/to/solc-0.8.36 cargo test --locked -p verifier_evm --lib --test initialization_windows --test flatten_roundtrip -- --include-ignored
```

On this host the pinned Rust compiler crashed while emitting debug information
for an existing dependency. The successful test run used environment-only
`CARGO_PROFILE_DEV_DEBUG=0`, `CARGO_PROFILE_TEST_DEBUG=0` and `CARGO_INCREMENTAL=0`;
no compiler pin, dependency or repository build configuration changed.

### AIH-336 source correction and validation

Rechecked the live issue and its complete comment page on 15 October 2026; the
assessment of Aleksandr Vlasov's comment is unchanged. Unsupported decoder slots
already used field-minus-one. The actual remaining problem was the zero-filled
setup-domain tail beyond the real decoder table, particularly when the compiler
omits a decoder table discriminator.

[Setup construction](../../prover/src/gkr/prover/setup.rs) now sets PC-low to
field-minus-one in that untagged tail, outside the existing active u16 PC-limb
domain. Real program rows, unsupported slots, discriminator-tagged tables and
the generic zero-entry row retain their existing meanings. Inactive witness
queries still use their original zero/default tuple; their execute predicate
remains zero. The correction does not assume that an active query selected a
valid instruction.

Changing only the committed columns would leave the optimized forward path
inconsistent. CPU preprocessing now compresses every committed setup row, rather
than truncating the cache and synthesizing a zero tail. The scalar and AVX-512
consumers already read that cache's actual length. [GPU setup scheduling](../../gpu/gkr/src/setup/mod.rs)
now materializes the same full domain; the existing kernel and stream/ownership
contract are unchanged. This increases retained cache size to one extension
value per trace row. No compiled layout, generated witness function, saved
setup cache or proof artifact is rewritten.

The [CPU regression](../../prover/src/gkr/prover/setup_tests.rs) uses both real
cached/no-cache add/sub decoder shapes with small test domains and the native
bytecode preprocessor. Its eight cases cover tagged/untagged tables and
supported/unsupported PC zero. It checks exact
real rows, out-of-range filler, legal PC-zero preservation, committed-column
compression versus the full cache, inactive tuples, and actual production forward
lookup numerators/denominators with cancelling valid multiplicities. It runs
with the [gkr_self_checks feature](../../prover/Cargo.toml). The same test fails
for the old zero tail and for a
committed-only correction with a truncated cache. The
[CUDA scheduling regression](../../gpu/gkr/src/setup/tests.rs) now includes a
nonzero tail and compares the complete domain with CPU arithmetic.

Scoped [prover](../../prover/Cargo.toml) library and
[gpu_gkr](../../gpu/gkr/Cargo.toml) library/test checks pass on this aarch64
Mac. The CPU regression passes; CUDA is unavailable and the AVX-512 path is not
executed here. The test automatically reaches that accelerated path on enabled
x86 hosts. Full regenerated proof replay, accelerated runtime agreement and
replacement of old decoder-only setup commitments remain explicit validation
work; the finding is not marked fully closed. F09's formal extraction, setup
commitment authentication and compiler/verifier correspondence remain external.
The existing external interpretation contract is unchanged and is not counted as the
implementation correction.

The nightly compiler crashed in LLVM debug-info emission for the large prover
test harness. The successful scoped build disables debug info only for the
[prover crate](../../prover/Cargo.toml)
through command-line profile overrides; no compiler pin or dependency changed:

```sh
cargo check --locked -p prover --lib
cargo check --locked -p gpu_gkr --tests
cargo test --locked --config 'profile.dev.package.prover.debug=0' --config 'profile.test.package.prover.debug=0' -p prover --lib --features gkr_self_checks decoder_padding_matches_committed_setup_in_forward_relations --no-run
cargo test --locked --config 'profile.dev.package.prover.debug=0' --config 'profile.test.package.prover.debug=0' -p prover --lib --features gkr_self_checks decoder_padding_matches_committed_setup_in_forward_relations
```

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
| F12 | Blessed split Keccak is uncovered | The provided 361-call split wrapper differs from the modeled 649-call special5 protocol | Split worker models, caller/CSR binding and the blessed-sequence proof are required for the full unsigned target |

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
AIH-336's separate source correction still awaits accelerated runtime agreement,
complete regenerated proof replay and replacement of old decoder-only setup
commitments. No new decoder/table discrepancy was demonstrated by this recheck.

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
[validation status](VERIFICATION_STATUS.md#validation-evidence).

## F12 — Blessed Keccak path is outside current proof coverage

**Status — 28 October 2026.** Required, open coverage gap for the unrolled full
unsigned target. The conditional `keccak_special5` results remain, but they do
not establish execution of the provided Keccak wrapper.

**Wrapper and modeled circuit differ.** The public
[`keccak_special5::keccak_f1600` wrapper](../../common_constants/src/delegation_types/keccak_special5.rs)
forwards to [`keccak_f1600.rs`](../../common_constants/src/delegation_types/keccak_f1600.rs).
That implementation issues 361 consecutive calls: in each of 24 rounds, five
column-parity calls, five theta/rho calls and five chi5 calls, followed by one
final column-parity call. Its three CSRs are
`KECCAK_COLUMN_PARITY_CSR_REGISTER`, `KECCAK_THETA_RHO_CSR_REGISTER` and
`KECCAK_CHI5_CSR_REGISTER`. It uses a 256-byte-aligned state pointer in x11.

In contrast, the [Lean artifact](Airbender/Review/Circuits/Keccak/Artifact.lean)
imports `keccak_special5_layout_no_caches_gkr.json`. The
[complete worker claims](Airbender/Review/Trace/Workers/Keccak/README.md)
cover that circuit's 649-call protocol and its seven local modes. The three
split compiled circuits now have cached and no-cache Lean imports of their equations, fixed
lookups and timestamp queries, including explicit grouped timestamp metadata.
They have no native worker soundness or composed machine execution proof.
The [pure split reference composition](Airbender/Proofs/Keccak/SplitPermutation.lean)
now proves the original Keccak permutation for all 361 reference calls.
It includes the final delayed iota. It does not prove native worker effects.
The retained chi5 lookup now derives nibble bounds and exact chi from its
actual input fields. Its native circuit retirement and memory proof remain open.
Shared state layout does not supply a refinement between the native protocols.
The [split schedule](Airbender/Review/Trace/Workers/Keccak/SplitSchedule.lean)
now states the exact public 361-call order and control transition;
[kernel proofs](Airbender/Proofs/Keccak/SplitSchedule.lean) check the counts and
progression. The new phase proofs also establish the pure reference result.
Native worker effects remain open.

**Unified setup differs.** The inspected
[`SUPPORTED_CSRS` list](../../circuit_defs/setups/src/unrolled_circuits/unifier_reduced_machine_circuit/mod.rs)
includes `KECCAK_SPECIAL5_CSR_REGISTER` and omits all three split Keccak CSRs.
Current unified verifier programs make no Keccak CSR calls, so the unified
target explicitly excludes special5 calls. The blessed split path belongs to
the unrolled full unsigned target, whose machine configuration supports the
three split CSRs. Its public decoder and exact caller/worker request bindings
now pass. Native worker functions, fixed-setup provenance and combined memory
execution remain open.

**Supported-use contract.** The developers classify unsupported delegation
invocations as UB ([AIH-350](https://linear.app/matterlabs/issue/AIH-350)); the
special5 invalid-control report was also canceled as UB
([AIH-358](https://linear.app/matterlabs/issue/AIH-358)). The agreed public-data
contract design, `ValidDelegationUse program initial`, admits the provided
wrapper shapes with valid entry and runtime arguments and excludes special5
calls. The implemented covered registry contains bigint, G and extended round;
the blessed split Keccak path is outside it. Thus the retained special5 theorems
do not contribute Keccak coverage under this contract. The predicate and native
prefix bridge compile, while the original conditional entrypoints retain their
explicit witness contracts for compatibility. Neither the new contract nor the
bridge supplies missing split-circuit or unified setup coverage.

**Required open work.** Prove native soundness for the three split circuits.
Connect their actual read/write effects to the checked 361-call reference.
Close fixed-setup provenance and combined memory execution. Derive supported
use from every actual native prefix. Preserve existing special5 claims
as conditional circuit/protocol results. Do not assume split/special5 equivalence,
or change circuit constraints, generators or production layouts to make the
current proof go through. A supported-use execution claim must explicitly leave
the blessed Keccak path outside its *proved* scope until these obligations are met.

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
| Artifact/reference fidelity | [Import/generation boundary](TRUST_AND_REVIEW.md#import-and-generation-fidelity): richer no-cache import, original Sail generation and project-reference applicability. Base-field arithmetic preservation is proved for 22 captured cached/uncached instances. Physical-row APIs derive lookup/helper validity from exact emitted-tuple matching; natural multiplicities are not tied to physical counters. Supplied-program wrappers require retained decoder-table compatibility. [Validation evidence](VERIFICATION_STATUS.md#validation-evidence) records source/runtime checks and the independent pending assurance gates. | Captured-instance results do not prove universal Rust compiler correctness or cryptographic argument soundness; use the [compiler premise table](Airbender/Review/Compiler/README.md#execution-premises). |
| Delegation-use domain | [F11](#f11--hash-witness-contracts-remain-unenforced) records the lower-level HashCommands fields. The public supported-use contract instead states wrapper shapes, entry safety and valid reference-prefix controls/pointers, including the blessed round masks' zero low limb. | Exact prefix matching derives the bigint/hash conditions for the new supported-use entrypoint. G separation remains explicit; arbitrary native enforcement and blessed split Keccak coverage are not claimed. |
| Keccak wrapper coverage | [F12](#f12--blessed-keccak-path-is-outside-current-proof-coverage): proofs cover 649-call special5; the provided wrapper uses the unmodeled 361-call split protocol, whose CSRs are absent from the inspected unified setup. | Retain conditional special5 results; blessed Keccak execution and its setup integration are deferred. |
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

[Verification status](VERIFICATION_STATUS.md#validation-evidence) records completed
and pending gates with their source snapshots. The whole-environment audit,
transitive replay and Linux/CI qualification remain separate from compilation.

Review the public supported-use domain and exact-prefix transport for bigint,
G and extended round, preserving lower-level contracts and native counterexamples.
The integrated witness mask, complete-protocol coverage, source/decoder/setup
fidelity and blessed split-Keccak gap retain their stated scopes. A proof
assumption documents a condition; it does not repair a production defect.
