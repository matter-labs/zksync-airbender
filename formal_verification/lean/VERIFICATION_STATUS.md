# Verification status

<!-- source-names: keccak_special5 -->

The model proves conditional soundness for the relations below. **No single
whole-execution theorem currently covers a committed production verifier
program.** A stream-aware unified relation now combines nondeterminism reads,
modular operations and delegation calls, but no native-to-reference soundness
theorem has been proved for that relation. The captured compiler execution bridge
also retains the four-entry decoder tables. Program-parametric source/trace
execution and logical lookup/RAM composition are established narrower results.

## Production machine targets

| Setup machine | Current target status |
| --- | --- |
| Unrolled full unsigned | Open. The `UnrolledFullUnsigned` target lists all premises. Prove native soundness for its combined relation. Bind the public program setup. Connect the caller, worker and initialization boundaries. Prove the split Keccak worker functions on the new base. The target excludes special5 calls. |
| Unrolled reduced | Open. The `UnrolledReduced` target lists all premises. Prove native soundness for its stream and caller relation. Bind the public program setup. Connect the extended-round worker and initialization boundaries. |
| Unified | Open. The `Unified` target lists all premises. Prove native soundness for the combined stream, modular and caller relation. Bind the public program setup. Connect the inline initialization boundary. The target excludes special5 calls. |

[The three target definitions](Airbender/Review/Compiler/MachineTargets.lean)
are Lean propositions. They are not proved theorems. Each target names its
native acceptance, program setup, decoder lookup and initialization premises.
Exact lookup matching and state/RAM permutations remain explicit.

Work now follows this order: Unified, UnrolledReduced, then
UnrolledFullUnsigned. The packed checker pilot stays at its current scope.

## Rebase checks

The branch now uses base `c1a662222cafcd96db4383dce737edb79fa62b09` from
`origin/av_gkr_compiler`. The remote tip matched this commit on 29 October 2026.
The local EVM initialization-window fix is present.

The three target definitions passed a focused source check. That check used
the retained dependency cache. It does not validate the changed native imports.
The native setup exporter passed its scoped Cargo check and build. All 16
setup exports and all 22 compiler captures regenerated. The setup artifact and
native evidence checks passed. The padding regression passed after removal of
the redundant full-domain CPU cache. The retained lock adds only the local
cs-to-prover edge required by the new base. It changes no package version.
Setup freshness passed. All 12 native generators ran. All 16 fresh setup JSONs
matched. Native dep-info covered 551 inputs. The refreshed manifest covers 731
source files.

The compiler and lookup provenance checks passed after regeneration. The
unified table and decoder setup scaffold checks also passed. The decoder
oracle rebuilt with the current sources on Lean 4.31.0.

The changed unified, bigint and initialization imports passed focused builds.
The four changed split imports passed in both cache modes. The split group
clock, derived-borrow, control-bound, physical-port and memory-order proofs
passed kernel elaboration on the new layouts. The split import test module
also built. All 22 production-program decoder comparisons passed in both cache
modes with the current oracle. All 68 small-program comparisons also passed.
These cover both cache modes for two ordinary programs, an extended-round
caller and the blessed split Keccak caller. The small matrix used an optimized
exporter build. It changed no Rust source or dependency version.
The compiler binding builds are pending.
Earlier build results apply to the old base.
Unified's current column-role inventory, dispatch bound and ordinary PC
increment passed focused kernel builds. Bigint's current column-role inventory,
control-bit proof and timestamp proof passed. Bigint's additive, equality and
multiplication writeback proofs passed on the derived EQ selector equations.
Bigint's memory rules, address soundness and memory value bounds passed
focused checks with the current timestamp columns.
Unified's control projection, control lookup resolution and jump arithmetic
passed focused checks on the new shared columns and affine write gates.
Unified's zero-register preservation and timestamp proofs passed focused
checks. The pooled ROM memory-port adapter also passed with the current
timestamp record. These close the native zero-write and clock obligations
used by the machine targets.
Unified's memory, ROM, binary, shift, TRIADD, XOR/rotate and modular proofs
passed focused checks. Its existing native caller-path proof also passed.
These restore the native instruction obligations on the new layout.
The combined stream target still needs its execution proof and initialization adapter.
All nine ordinary worker and CPU memory-port inventories passed focused
checks. Their timestamp records use an explicit absent borrow subtrahend.
The focused circuit and proof group passed all 288 module checks.
This group includes the timestamp tests, native path and span execution,
supported delegation use and the three target propositions.
An earlier batch hit its resident-memory cap
while it rebuilt an unchanged extended-round import. That was a resource stop.
The later batches used the documented 5,120 MiB resident cap.

The normal dependency build reached its 1,800-second limit while it rebuilt
unchanged shift certificates. The guard left no owned process running.
The focused checks now use a separate object directory. A declaration
dependency inspection found no use of the changed timestamp-group record or
bigint range input in the 64 retained shift certificates. The focused checks
reuse this mathematical cache. This is not a full frontend build or kernel
replay of all dependencies.

Lake now tracks all six split circuit JSONs and all three split setup JSONs.
These inputs serve the full unsigned target's three fixed-setup premises.
The provenance controls check that Lake requires each native JSON input.
All 20 controls passed. A focused build passed with the new dependencies.

The branch has not been force-pushed.

The full unsigned relation now combines the six CPU families, modular MOPs,
nondeterminism reads, bigint, BLAKE2 extended-round and the three split Keccak
calls in one stream execution. Its caller registries are functions of public
text, with a proved generic public-byte/source lemma and inclusion of the
existing ordinary/caller steps. The new split micro-call reference uses the
blessed control schedule, the inverse-Pi physical slot map and the existing
Keccak round constants. Kernel checks establish distinct touched slots for all
361 calls and the final round's identity slot map. Native worker-to-reference
soundness, complete 361-call functional composition and registry disjointness
remain open; these reference checks do not establish native circuit coverage.

The split-worker native interface now selects all six exact compiled
constraint/lookup/timestamp imports, invocation columns and memory ports by
worker kind and cache mode. It states participation and exact memory-token
matching as explicit logical acceptance premises. Setup provenance, grouped
memory effects, complete split caller composition and functional soundness remain
open. A separate split request interface retains full-width CSR addresses and
exact virtual-token matching for the three blessed worker families; focused
proofs derive one-to-one nonzero fulfillment and bounded invocation clocks
from machine constraints and the public initial clock. Exact decoder matching
and public Sail bytes also fix each matched worker's split kind. The imported
ADD/SUB constraints prove canonical caller PC retirement. Shared caller/worker
memory composition and functional worker soundness remain open. A focused split
memory proof now derives bounded timestamps for all physical reads and writes
from public seed clocks, caller-derived worker clocks and the explicit RAM
permutation. A generic grouped-clock lemma proves strict read-before-write order
from a positive compiled read distance. All four theta/rho and six chi5 groups
have exact clock equations and Boolean borrows extracted from both cache modes.
Both column-parity captures additionally derive every per-port Boolean borrow
and timestamp comparison bound directly from their imported equations and
lookup queries, then prove strict read-before-write order given the public
invocation and logically matched previous-clock bounds.
For theta/rho and chi5, an explicit public controller-table soundness premise
now yields one-hot iteration flags or a bounded row index. The complete
uncached split setup exports are retained and provenance-checked; cached and
uncached exports have identical fixed columns and table metadata. The imported
controller regions have kernel-checked row properties and genuine static-table
soundness theorems. Proving that every active tagged lookup in the full generic
setup belongs to these regions remains open. The complete theta/rho generic
table is now imported, and a kernel-checked structural proof isolates its
controller tag to the exact retained 121-row region. Row equality between the
generic view and the sliced view, and the corresponding chi5 result, remain
open. Native fixed-table lookups then
give positive, nonwrapping distances and strict order for all groups in both
cache modes. Complete memory effects remain open. All theta/rho and chi5 physical ports now
have kernel-checked group ownership in both cache modes. A common theorem proves
strict read-before-write order for all six capture families. Exact RAM matching,
public initial clock bounds and the explicit controller premise now yield the
complete split-pool logical RAM history facts: matching, preserved addresses
and strict per-port time order. Functional worker effects remain open.

Both cached and uncached native captures remain required. The checker migration
must qualify all 22 capture configurations.

A direct one-line `decide +kernel` pilot over the existing shift/AND Block
representation exceeded the bounded process memory limit after 12.79 seconds
without a proof error. Separate packed-byte imports for shift AND, OR and XOR,
plus the unified XOR8 setup output column, share a once-proved bitwise
`check_sound`; each has a one-line kernel `ok` and a mathematical byte-projection
claim for all 65,536 outputs. Each packed import retains definitionally equal
full source artifact bytes to its corresponding original source import. The
existing Block and setup-prefix shards remain; these are four pilot columns,
not a migration of the 22 configurations or a cold-build baseline.
The shared bitwise checker and all three shift-table capture checks now
elaborate with default heartbeats. The shared replication proof still requires
a raised recursion limit.

## Supporting proved results

| Area | Result and scope |
| --- | --- |
| [Ordinary circuits](Airbender/Review/Circuits/README.md) | Arithmetic, branches/jumps, comparisons, shifts/bitwise and word/subword memory have reference soundness proofs. Local public-image histories and native ROM-shadow histories are distinct interfaces. |
| [Whole execution](Airbender/Review/Trace/README.md) | Pooled and unified source/trace execution bind final PC and every tracked cell, including registers, for programs admitted by their selected registry. Branches and repeated-PC loops are supported. Discarded x0 writes missing from a registry remain outside it. |
| [Unified stream inclusion](Airbender/Proofs/UnifiedReduced/FullStreamInclusion.lean) | Every existing mixed ordinary/custom or complete delegated-call step lifts to the stream-aware unified relation without consuming a stream word. Finite runs lift, and existing no-read whole-execution results retain their terminal claims when the native read count is zero. Native soundness of the combined relation with external reads remains open. |
| [Delegated workers](Airbender/Review/Trace/Workers/README.md) | Bigint, BLAKE2 and special5 Keccak compose under explicit call contracts. Complete algorithms require protocol coverage and valid memory gaps. Extended-round masks remain witness premises in lower-level integrated APIs as well as worker APIs. |
| [Supported delegation use](Airbender/Review/Trace/UnifiedReduced/SupportedUseExecution.lean) | Public wrapper shapes, safe entry and reference-prefix validity derive bigint/G/extended-round worker contracts. G pointer separation remains in the public domain; accepted complete G spans also derive separation from memory matching. Public initialization, tracked RAM, configuration, setup and exact matching remain explicit. |
| [Provided Keccak wrapper](FINDINGS.md#f12--blessed-keccak-path-is-outside-current-proof-coverage) | Uncovered. The blessed 361-call split order and control progression are checked; the three public CSR caller forms now have a separate Sail decoder registry and complete code-shape interface. [A proved bridge](Airbender/Proofs/Keccak/SplitCallerBridge.lean) preserves public Sail source evidence and the full-width native lookup query when routing a split CSR to that registry, including membership in the modeled public decoder table; each word of a blessed group selects its scheduled worker and passes the full unsigned allowlist. All three compiled worker constraint/lookup cores are imported. Their complete setup, memory effects, all-stream supported-use condition and functional composition are still required for the full unsigned target. The modeled 649-call special5 protocol is separate. |
| [Initialization](Airbender/Review/Trace/Initialization.lean) | Native standalone/inline adapters derive seeds for ordinary pooled/unified execution. External-read, modular, TRIADD/XORROT and delegation extensions retain their own seed premises. |
| [Reduced public program](Airbender/Proofs/Trace/ReducedPublicProgram.lean) | The public reduced decoder filter is definitionally the stream-aware reduced filter. Every projected ordinary entry uses one of its four native CPU families, so the reduced-run inclusion no longer needs a separate family premise for text-derived programs. Every projected virtual caller is the BLAKE2 extended-round CSR; the special5 exclusion follows for reduced text. This does not establish native decoder setup binding or whole-machine soundness. |
| [Public program setup](Airbender/Review/Compiler/PublicProgramSetup.lean) | New unrolled and unified interfaces bind independently supplied decoder columns, the actual imported circuit masks, capacity, delegation group syntax and initial image to public text. [The imported mask constructors](Airbender/Proofs/GKRProtocol/ProgramMasks.lean) satisfy that binding. [Source and classification theorems](Airbender/Proofs/GKRProtocol/PublicProgramCases.lean) map a range-checked query in those columns to a Sail-sourced ordinary instruction or virtual caller in its corresponding public program. [Native row corollaries](Airbender/Proofs/GKRProtocol/PublicNativeRows.lean) use an explicit exact decoder lookup premise to classify actual trace rows; [accepted-row corollaries](Airbender/Proofs/GKRProtocol/PublicAcceptedRows.lean) derive the required PC range from constraints, state matching and the public initial PC. Matching each compiled circuit's lookup to the supplied columns, deriving native acceptance from all certificates, then proving compiler execution remain open. |
| [Compiler preservation](Airbender/Review/Compiler/README.md) | Base-field arithmetic preservation covers 22 captures. Fourteen row compositions derive helper bounds, authored lookup membership and source validity from physical native arithmetic/active rows and exact emitted-tuple matching. Separate public-text row models have generic active-PC membership for ordinary instructions and full-width delegation-CSR caller rows, with captured masks and ROM capacity. A range-checked active modeled decoder row, including its selected native column mask, now yields an ordinary or virtual caller entry sourced from public Sail bytes. Caller source includes the decoded CSR shape and configuration allowlist; an effectful decoder result is not silently accepted. A generic initial-ROM lemma places each present public text word into the modeled word-ROM table. The caller projection also requires a public well-formed call-group premise to match native preprocessing. The compiler wrappers still require retained four-entry tables; the differential checks do not yet replace that premise. |

Upstream #531 merged as `06c15f275` and is in the new base. The unified
base-layer entrypoint now returns the verified registers. It no longer returns
the fixed success vector. New-base runtime validation remains pending.
See [the source](../../tools/gkr_verifier/src/common_fsv_unified_base_sec_100.rs)
and the [trust boundaries](TRUST_AND_REVIEW.md).

Exact natural-multiplicity lookup matching, state/RAM permutations and public
boundaries remain assumptions. Sampled sum/product equality does not establish
those exact relations. Cryptographic argument soundness, universal Rust compiler
correctness, import/generation fidelity and completeness are outside these claims.
The [supported-use domain](Airbender/Review/Trace/UnifiedReduced/DelegationUse.lean)
excludes invalid bigint/hash invocations and special5 calls. Its round rule is the
blessed mask with zero low limb; arbitrary VM calls have a wider domain.

## Validation evidence

This table is the maintained evidence inventory. Historical counts and detailed
receipts belong in [verification checkpoints](VERIFICATION_HISTORY.md), rather
than repeated in the guides. Changes after a checkpoint require their own checks.

| Gate | Last completed evidence / outstanding work |
| --- | --- |
| Repair controls | Mac: 68 policy/provenance/generation tests pass; 26 guard tests pass and four Linux-only tests skip; 23 pool policy/process tests pass. All six affected generator roundtrips, 14 complete lookup bindings and the independent export-byte validator pass their focused checks. These are not a complete frontend or Linux-backend qualification. |
| Reference known answers | The XKCP all-zero permutation regression passes a normal Lean build (14.39 seconds, footprint 927.56 MiB, resident 3251.11 MiB). The NIST FIPS 202 SHA3-256 empty-message permutation vector passes a focused guarded build at the current source. RFC 7693 abc and all 14 lookup bindings elaborate against cached imports; they still require the complete dependency rebuild below. All guarded focused jobs leave no surviving workers. |
| Split Keccak import slice | The example exporter compiles with `cargo check --locked -p execution_prover --example export_setup_json`. All six split worker setups export to temporary files in cached/uncached modes, and their embedded circuit objects equal the checked-in compiled objects. All six Lean constraint imports, timestamp-group checks and focused parser negative controls build under the guard (16.47 seconds, peak footprint 638.87 MiB, resident 2985.12 MiB, no surviving worker). These temporary setups are not retained in the manifest; no split-worker soundness or full import regression is claimed. The broader artifact/setup import build was intentionally interrupted after 579.72 seconds with no reported Lean error and no surviving worker. |
| Setup provenance after exporter extension | The only exporter change adds three split-family match arms; the preexisting family branches and serialized setup paths are unchanged. Its source hash was refreshed in the retained manifest. `check_setup_artifacts.py` passes for all 13 existing artifacts, 713 native source hashes and the 12 production/one derived circuit identities. This is a static provenance check, not a fresh native reconstruction at this HEAD. |
| Public-text decoder row model | Focused guarded builds prove ordinary and caller-aware membership, table inclusion, 16-bit sentinel exclusion, public source of each range-checked active modeled row before and after the native mask, exact native caller-registry inclusion, and generic public text-word ROM membership. The caller source records the exact CSR instruction shape and allowlist. The native model keeps the complete virtual CSR in the lookup query, rejects over-capacity text, keeps one row per padded word and applies the imported family mask. The pure-decoder tightening still matches native add/sub rows for a seven-call BLAKE2 example in full/reduced and unified configurations, both cache modes. Direct axiom smoke for the new pooled/unified membership, masked active-row source and text-ROM theorems reports only `propext`, `Classical.choice` and `Quot.sound`; split caller metadata uses `propext` alone. The complete environment audit remains pending. This does not yet replace the fixed decoder premise in compiler theorems. |
| Packed checker pilot | Packed shift AND, OR and XOR output columns import one 2048-bit natural per 256 native rows after source-slice validation. Generic `checkRows_sound`, `extractDigit`, and bitwise byte-extraction lemmas feed one `PackedBitwise.check_sound` for all three. The focused AND, OR and XOR certificate builds passed under the 2560 MiB footprint guard in 6.43, 6.25 and 6.27 seconds respectively (peak footprint about 1550 MiB each). [The unified XOR8 setup output](Airbender/Proofs/Tables/UnifiedXorPackedPilotCertificate.lean) now passes the same checker in a focused kernel build; its peak memory and cold-build effect have not been measured. Direct axiom smoke for the unified `ok` and output theorem reports only `propext` and `Quot.sound`. The old Block and prefix shards remain in use; no cold-build or transitive replay improvement is claimed. |
| Decoder differential | A compiled Lean oracle and native exporter agreed on all padded rows for an earlier 40-case small-program comparison across full/reduced machines, all applicable families and both cache modes. Focused uncached checks at the current model match all four reduced CPU families of the committed 804,998-word unrolled base-layer verifier, including 17,360 BLAKE2 CSR words; the add/sub match used a saved native export. The unified decoder matches the committed BLAKE2 and special-opcode recursion verifiers in focused uncached runs. A synthetic blessed 361-call split Keccak text matches the full add/sub decoder in both cache modes. Native circuit objects agreed across two small programs and both machine configurations for the four shared circuits. A separate public call-group shape check passes for all five committed verifier texts and rejects malformed BLAKE2/split controls. CI now includes all committed verifier texts plus small ordinary, BLAKE2 and split Keccak cases in both cache modes; that new gate has not run. A compatible ZKsync OS image/text pair is missing: the tagged repository binary has single-call BLAKE2 groups, which the current native preprocessor rejects. |
| Reduced setup export tooling | The exporter accepts `--reduced` for the four shared unrolled CPU families. `cargo check --locked -p execution_prover --example export_setup_json` and the source-pinned manifest check pass. The executable build succeeded with `CARGO_PROFILE_DEV_DEBUG=0`, avoiding the local LLVM DWARF SIGBUS; focused native exports then completed. |
| Complete source/runtime/review frontend | Passed on Mac at f0b059fe6412: 4,862 modules, 219 concrete Tests, five retained Sail modules, 3,509 runtime native modules, library and both executables. Normal Lake freshness, artifact hashes, direct axiom comparison, importer runtime and review checks passed. The 23 guarded jobs took 260.14 seconds from a normally built cache; peak footprint 855.31 MiB and resident 4279.14 MiB; no surviving workers. This is historical evidence for the source before the Review reorganization. |
| Linux native setup freshness | Passed at ac90532c92b1: 12 generators, 13 complete exports, receipts and 546 dep-info inputs; 242.97 seconds, peak charged memory 1629.62 MiB, no surviving workers. |
| Native compiler capture reproduction | Passed at ac90532c92b1: all 67 root files reproduced byte for byte, with retained/fresh validators and provenance controls. Derived interpretation/lookup directories have separate validators. |
| Linux process controls | Passed at ac90532c92b1 on aarch64 Linux: 29 guard and 23 pool tests. The subsequent exit-race repair requires fresh runtime controls. |
| Complete Linux frontend / cold reproduction | The cold attempt stopped after 3,883 completed source-build steps when Docker became unavailable; launcher exit 255, interrupted leaf has no result. No complete Linux frontend or cold pass was issued. Preserve that partial cache as recovery data, not passing evidence. |
| Whole-environment axiom audit | Pending. The Mac attempt stopped after 125.97 seconds at resident 5125.94 MiB against the unchanged 5120 MiB cap (footprint 1193.53 MiB); no surviving workers and no successful audit result. The IotaMapping dependency discrepancy has a reviewed disposition, not a regenerated passing baseline. |
| Independent transitive replay / negative controls | Pending. Earlier selected-module replay did not replay imports transitively. The 32 MiB stack remains provisional until the deep modules and full dependency graph pass. |
| CI qualification | Advisory. Current cold/warm runtime, cache sizes and complete replay feasibility on the configured runner are not established. Its 22-hour shared work deadline and 24-hour job boundary do not establish feasibility. |

The allowed standard axioms are propext, Classical.choice and Quot.sound. All
12,409 established explicit audit roots remain required; additional definitions
may add roots. Baseline updates must come from a successful environment audit
with reviewed deltas. A direct report is a smoke check, not that audit.

## Remaining milestones

1. Validate the assurance repairs and conservative Review reorganization without
   dropping public declarations, audit roots, imported values or assumptions.
2. Finish whole-environment auditing, independent transitive replay and isolated
   false-proof controls; measure Linux cold/warm and CI feasibility.
3. Complete the three production machine targets: compose stream-aware instruction
   and caller relations with initialization; bind compiler setup to arbitrary
   public text; prove the blessed split Keccak path for full unsigned; and
   demonstrate committed verifier programs.
4. Convert measured per-capture fact families to once-proved Boolean checkers,
   then qualify build and replay cost. Cryptographic soundness, universal Rust
   compiler correctness and completeness remain in the
   [deferred milestone register](FORMAL_VERIFICATION_PLAN.md#deferred-milestones).

[Reproduction](README.md#reproduce) gives commands and resource limits.
[Findings](FINDINGS.md) distinguishes supported-use exclusions, conditional proof
coverage and implementation issues. Production circuits are not changed to make
proofs succeed; discrepancies require documentation and narrow explicit assumptions.
