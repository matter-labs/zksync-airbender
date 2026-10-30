# Verification status

<!-- source-names: keccak_special5 -->

The model proves the public Unified and UnrolledReduced machine targets.
Both proofs include the native combined stream relation, public program binding
and initialization. The full unsigned target remains open. Exact lookup,
request and RAM matching remain explicit. The final full validation is pending.

## Production machine targets

| Setup machine | Current target status |
| --- | --- |
| Unrolled full unsigned | Open. Native execution, public supported-use induction and initialization are kernel checked. Complete three `FixedSetupRows` certificates: parity, theta/rho and chi5. Each must cover every parsed physical row, including padding. The target excludes special5 calls. |
| Unrolled reduced | Proved by `MachineTargets.Proofs.unrolled_reduced_soundness`. The theorem has exactly the `UnrolledReduced` target type. It includes public program binding, native combined execution and initialization. Exact lookup, request and RAM matching remain explicit. |
| Unified | Proved by `MachineTargets.Proofs.unified_soundness`. The theorem has exactly the `Unified` target type. It includes public program binding, native combined execution and initialization. Exact lookup, request and RAM matching remain explicit. The target excludes special5 calls. |

[The three target definitions](Airbender/Review/Compiler/MachineTargets.lean)
are Lean propositions. Unified and UnrolledReduced now have proofs. The full
unsigned target remains open. Each target names its native acceptance, program
setup, decoder lookup and initialization premises.
Exact lookup matching and state/RAM permutations remain explicit.

Unified and UnrolledReduced are complete. Work now covers UnrolledFullUnsigned
and blessed split Keccak. The packed checker pilot stays at its current scope.

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
The compiler binding builds passed. The bigint and unified wiring
certificates passed in both cache modes with fresh native graph imports.
The wiring generator check passed for all 22 captures and 304 module targets.
The full arithmetic and windowed agreement generator checks also passed.
All four current arithmetic imports passed focused checks. The complete
compiler group passed 497 checks. It covers every bigint and unified compiler
case module, both cache modes, the shared logical and program execution
consumers, and the decoder dependencies that those consumers import.
The group reuses the unchanged finite-table cache. Earlier batches reached
their time limit or found stale cache imports. The last batch passed and left
no owned process running. All checked module records remain available.
The windowed witness and public-boundary templates now use the imported input
list length. They no longer fix the old 145-wire dimension. The public-table
tag proof uses the new ROM gate and pooled query columns. Its statement and
premises stay the same. All eleven final source and generator checks passed.
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
The combined stream target still needs its execution proof.
Its initialization adapter passed a focused kernel check. The adapter binds
the public text registry and native seed to the combined stream boot inputs.
Its two proofs use only the three allowed axioms.
Unified's native external-read specification and register-history execution
proof passed focused kernel checks. They keep the stream slot binding
explicit. Both proofs use only the three allowed axioms. Stream ordering and
the combined execution proof remain open.
The external-hint specification and exact register-history execution also
passed. Public text supplies aligned, bounded instruction PCs. Public setup
and initialization supply all ordinary execution inputs. The combined registry supplies native x0 rules for
ordinary, modular, external and worker rows. These proofs passed focused
kernel checks. Their axioms stay within the three allowed axioms. Exact
request and RAM matching remain explicit.
Native prefixes retain the same stream slots and public memory inputs.
The combined registry now supplies one machine and worker memory history.
This conditional history keeps the round-mask contract explicit.
Indexed cut composition carries the stream position through each cycle.
These proofs passed focused kernel and axiom checks.
External and modular instructions now retire in the actual shared cycle
history. Their cycle proofs passed focused kernel and axiom checks.
Ordinary arithmetic, TRIADD and XOR/rotate now retire in the stream registry's
shared native history. Their adapters passed focused kernel and axiom checks.
Control, comparison, binary, shift and RAM cycle adapters also passed focused
kernel and axiom checks. All instruction classes now have native cycle proofs
for the combined registry. The native read bit matches public metadata.
Ordinary, custom, modular and caller rows consume no stream words. These
selector proofs passed focused kernel and axiom checks.
The combined noncaller dispatcher also passed. It selects the public Sail
clause for every ordinary, custom, modular and external-input row. It proves
retirement in the actual native cycle and the exact stream-count change.
The current dispatcher uses the existing physical RAM profile. The native ROM
adapter must remove that intermediate restriction before it closes Unified.
Native clocks now prove the zero initial stream count, each cycle's exact
increment, and the total terminal count. These proofs passed focused kernel
and axiom checks. They add no ordering premise.
Indexed path composition now proves the combined execution from exact native
cycle facts. It includes the final PC, terminal memory and stream count.
Its kernel and axiom checks passed. This theorem retains native caller-cycle
facts and the physical code profile as explicit inputs.
The native caller adapters also passed focused kernel and axiom checks.
The conditional native stream entrypoint derives all caller cycles from
current worker equations and the shared history. It retains explicit bigint
commands, hash-controller contracts and the physical code profile.
The stream-aware prefix induction now derives those worker controls from
public supported use. It proves combined execution under the intermediate
physical RAM profile. Its kernel and axiom checks passed. Private command and
controller contracts are conclusions at this entrypoint.
The joint worker-control and worker-domain induction passed kernel checks.
It derives both contracts from public supported use and exact native prefixes.
Native prefix cutting now uses seed clock bounds. It does not equate native
zero ROM values to physical program bytes. The ROM input and terminal adapters
also passed. The native supported-path theorem now proves combined execution
with the original native terminal view. All checked roots use only the three
allowed axioms. The public decoder and acceptance adapter also passed.
The final `unified_soundness : Unified` theorem passed a focused kernel check.
Its axiom report lists only `propext`, `Classical.choice` and `Quot.sound`.
The check used the retained dependency cache. Full environment auditing and
transitive kernel replay remain pending. All 12,457 pre-rebase audit roots
remain in the explicit inventory. The reduced target proof is now also complete.
Its public ordinary and caller images and standalone initialization adapter
passed focused kernel and axiom checks. Its shared stream/caller memory theorem
also passed. Native matching derives clocks, zero-register reads, canonical
word bounds, worker operations and one actual Sail memory history. The round
controller contract remains explicit at this intermediate memory interface.
The public supported-use proof now derives this contract.
Reduced arithmetic, modular, external, shift, bitwise and control-flow clauses
now have shared-history execution adapters. Their focused kernel and axiom
checks passed. These adapters take actual operands and histories from the shared
transport. The control adapter keeps its native final-PC range explicit.
The native PC path now derives that range from state matching and the typed boundary.
The reduced LW/SW address, native transport and full instruction adapters
also passed focused kernel checks. They use shared initialized address codes
and readonly-ROM history. The native clock proofs derive unique aligned row
clocks, four-tick advancement and exact CPU event windows. Their axiom reports
use only the three allowed axioms. Global cycle and caller composition now pass.
Exact caller slots now identify every worker in each native instruction
window. The cycle split and ordinary row history passed focused kernel checks.
State matching and the existing typed boundary derive every final-PC range.
Native clocks derive the initial, per-cycle and terminal stream counts.
Their axiom reports use only the three allowed axioms. The ordinary dispatcher,
complete caller retirement and supported-use composition now pass.
The reduced ordinary dispatcher has now passed focused kernel and axiom checks.
It binds all four native CPU families to the public modular/external clauses,
actual shared cycle states and exact stream increments. The native ROM adapter
now supplies its readonly-event property. Caller retirement and supported-use
composition now pass.
The complete reduced caller-cycle adapter has now passed focused kernel and
axiom checks. Exact slots select one actual worker. Shared history supplies
its reads and frame. The extended-round reference and native caller PC equations
prove complete retirement. The full CSR query disables external reads on callers.
Round control, worker RAM binding and readonly-ROM history remain explicit at
this intermediate interface. The native prefix induction now derives them.
The complete reduced native path now composes those ordinary and caller cycles.
It proves `ReducedRealizes` with final PC, shared terminal memory and exact
stream consumption. Its focused kernel and axiom checks passed. Native worker
liveness places every worker event inside the same path. Seed-clock lemmas
also support raw native prefixes without equating ROM bytes to native zero.
Native ROM transport, joint supported-use induction and public decoder
acceptance assembly now complete the reduced target.
The ROM-aware code-frame lemmas passed focused kernel and axiom checks.
Interpreted ROM events refresh the same public word. Fetch transport can use
that readonly history without the global tracked-RAM lower bound. The worker
RAM binding remains explicit at this intermediate transport interface.
The full ROM-aware native path passed focused kernel and axiom checks.
It includes load/store retirement, caller retirement, and final stream count.
The public setup and initialization supply its ROM execution profile.
Worker ABI bounds now follow from each exact worker-port binding.
These results admit tracked low ROM cells. No global tracked-RAM lower bound
occurs in this path. The joint prefix induction must derive worker-port
binding from the public runtime argument contract. That induction has now
passed focused kernel and axiom checks.
The ROM-aware load/store cycle proof also passed. It uses the current native
equations for readonly loads. It removes the global RAM lower bound from this
cycle proof. A separate worker-port lemma derives each indirect RAM bound
from exact worker-domain binding. The public ROM profile admits low ROM
shadow cells. The joint worker-domain induction and final Unified target
assembly now pass.
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

The focused rebase qualification passed. The full frontend build, environment
audit and baseline refresh, transitive kernel replay, and Linux runtime and
warm-cache qualification did not run. They remain pending for user review.

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
| [Unified stream inclusion](Airbender/Proofs/UnifiedReduced/FullStreamInclusion.lean) | Every existing mixed ordinary/custom or complete delegated-call step lifts to the stream-aware unified relation without consuming a stream word. Finite runs lift, and existing no-read whole-execution results retain their terminal claims when the native read count is zero. The complete `Unified` target now proves native soundness of this combined relation from its explicit public and exact-matching premises. |
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

### Reduced native ROM obligation

The reduced native ROM adapter passed its focused kernel check. It derives
canonical addresses from exact shared matching and strict native clock order.
It does not assume physical values in the native zero seed. ROM interpretation
preserves imported constraints, decoder queries, callers, requests and shared
memory matching. It preserves public instruction bytes and external responses.
The physical initialization adapter and complete conditional reduced path pass.
Worker controls and RAM port locations remain explicit intermediate premises.
The public supported-use adapter now proves them. Public decoder acceptance
also passes. The final reduced machine target is proved.

The check used Lean 4.31.0 and retained unchanged dependency objects. All selected
roots use only the three allowed axioms. The full frontend, environment audit,
transitive kernel replay and Linux qualification did not run.

### Reduced public supported-use obligation

The reduced prefix and supported-use proofs passed focused kernel checks.
Each prefix keeps exact request and RAM matching. Its actual caller endpoint
supplies a typed verifier boundary. Joint induction proves native round controls
and each worker port location from reachable public reference arguments.
The native path now has no private worker-control or port-domain premise.
The public decoder and native acceptance adapter now pass. The final reduced
target is proved. Full validation remains pending as stated above.

### Reduced target proved

`MachineTargets.Proofs.unrolled_reduced_soundness` proves the unchanged
`UnrolledReduced` proposition. Public text and the actual imported masks supply
full decoder queries. The proof derives the omitted funct3 field where needed.
Native selectors classify ordinary and caller rows. Exact state matching bounds
the incoming PC without a separate CPU RAM permutation. The proof connects
standalone initialization and public supported use to the full reduced path.
No private worker control or port-domain premise remains in the final theorem.

The focused source and axiom check passed on Lean 4.31.0. Its selected roots use
only `propext`, `Classical.choice` and `Quot.sound`. It retains unchanged finite
table objects. It is not a full frontend or transitive replay. The environment
audit and Linux qualification remain pending. Work now resumes the full unsigned
machine and the blessed split Keccak sequence. The packed checker pilot stays
at its current scope until all three machine targets are done.

### Full unsigned initialization obligation

The full unsigned standalone initialization adapter passed a focused kernel
check. Public text constructs the six-family ordinary stream image and the
separate standard and split caller images. The standard filter retains exact
bigint and extended-round decoder metadata. The adapter derives boot inputs
from the unchanged standalone initialization boundary, public profile and setup.
The full unsigned machine target remains open. Its native combined path and
blessed split Keccak function are not yet proved. Full validation remains pending.

### Split native worker coverage obligation

The native invocation proof passed for all three split worker kinds and both
cache modes. An active worker cannot use invocation zero. The proof uses the
actual imported initial timestamp lookup. It adds no schedule or positive-clock
premise. Exact request matching can therefore account for every active worker.
The complete full unsigned execution proof remains open.

### Split generic controller binding obligation

The complete theta/rho and chi5 imports now supply their controller facts.
The row proofs select the exact controller regions from the native field tags.
The imports keep every physical column. They retain padding inside the
generic table extent. They omit the physical padding after that extent.
The proofs use certified block lengths to skip the large table prefixes. The runtime regression compares every parsed theta/rho block and value.
It also checks the complete table extent and native region data. A kernel
proof checks the exact source bytes. All checks passed. The fifteen new
audit roots use only the three allowed axioms. All old roots remain present.
The explicit inventory now contains 12,714 roots.

The source-to-data bridge in `FixedSetup` remains open. Its JSON parser has an
opaque kernel worker. The imported table proofs do not close this bridge.
The split worker functions and the complete blessed sequence also remain open.
Full validation remains pending.

### Split exact worker-accounting obligation

Exact native request matching now accounts for every active split worker.
The proof removes the zero-clock exception with the native liveness theorem.
Every worker has an actual caller with the same full-width CSR and timestamp.
Both new roots passed focused kernel and axiom checks. They use only the three
allowed axioms. The explicit inventory now contains 12,716 roots. All prior
roots remain present. No function or complete execution claim follows yet.

### Full unsigned public decoder obligation

Exact public lookup now classifies every actual row of all six CPU families.
The proof restores the unused funct3 slots from public instruction metadata.
Native selectors separate ordinary rows from standard and split callers.
All five admitted caller forms retain the original public Sail source and
complete CSR query. The public special5 exclusion stays explicit.

Six new roots passed focused kernel and axiom checks. They use only the three
allowed axioms. The inventory now contains 12,722 roots. All prior roots remain
present. This closes the target's public row-classification obligation.
The combined native execution and remaining split obligations stay open.

### Full unsigned split request-channel obligation

The full target's combined request permutation now supplies the split channel.
Filtering uses the complete CSR address. Standard worker requests cannot enter
this channel. Public decoder lookup supplies the split caller registry.
The public text image and initial PC boundary supply its input conditions.
Every active split worker has an actual caller with the same CSR and raw clock.
The proof adds no request-matching or witness-schedule premise.

Six new roots passed focused kernel and axiom checks. They use only the three
allowed axioms. The explicit inventory now contains 12,728 roots. All previous
roots remain present. Split functional effects, supported-use execution and
the setup-source bridge remain open. Full validation remains pending.

### Blessed split reference-composition obligation

The original split reference now produces the original Keccak permutation.
The proof composes all 361 calls. It checks all 24 parity, theta/rho and chi
phases. It includes the final delayed iota and the return to the original
physical lane layout. A kernel proof checks the finite index cache. The cache
changes no operation, reference or public theorem statement.

All 41 new roots passed focused kernel and axiom checks. They use only the
three allowed axioms. The explicit inventory now contains 12,769 roots. All
previous roots remain present. The last bounded group passed. It left no owned
process running. Earlier attempts found reduction limits or reached the memory
cap. Smaller proof units passed under the unchanged resource limits.

Native split circuit soundness remains open. The next obligations are the
fixed-table arithmetic facts, each worker's actual functional read/write
effect, and the combined native history with supported-use induction. The
`FixedSetup` source bridge also remains open. The full unsigned target and
final lengthy validation remain pending.

### Native chi5 lookup arithmetic obligation

The retained chi5 generic table now proves exact nibble arithmetic.
A tagged native lookup derives all five input bounds and output bounds.
Each actual output equals chi of its actual cyclic input fields. The proofs
cover every arithmetic row. They add no operand or expected-result premise.

The importer stores small shared literal leaves for the large native prefix.
It checks every parsed value before it emits the index view. The full-column
runtime regression passed after emission. It compares every value, including
physical padding. The controller proofs also passed with this representation.
The input bindings, output bindings and arithmetic identities use kernel proofs.
The final focused checks list only the three allowed axioms for all 29 new roots.
The explicit inventory now contains 12,798 roots. All prior roots remain present.

Native worker retirement and combined memory execution remain open. The
`FixedSetup` source bridge remains open. Full validation remains pending.

### Native chi5 arithmetic-query obligation

Both compiled cache modes now derive all sixteen arithmetic lookup results.
The proof uses their actual imported query entries and retained generic table.
It derives input bounds, output bounds and the exact cyclic chi operation.
The native constant tags need no execute or operand premise at this layer.

Eight new roots passed focused kernel and axiom checks. They use only the
three allowed axioms. The explicit inventory now contains 12,806 roots. All
previous roots remain present. Lane packing, worker retirement and combined
memory execution remain open. Full validation remains pending.

### Native chi5 lane-effect obligation

Both native cache modes now prove the complete chi effect on actual memory
lanes. The proof binds each native read and write limb to its four arithmetic
queries. All 80 packing cases passed kernel checks. Lookup bounds recover each
canonical sixteen-bit limb. Bitwise assembly proves the sixty-four-bit lane
operation. The proof adds no operand or expected-output premise.

Twelve new roots passed focused kernel and axiom checks. They use only the
three allowed axioms. The explicit inventory now contains 12,818 roots. All
previous roots remain present. The final bounded group passed and left no owned
process running. Native control and memory retirement remain open. The fixed
setup source bridge and the full unsigned target remain open. Full validation
remains pending.

### Native chi5 control and memory-effect obligation

The actual chi5 controller lookup now selects the original blessed call.
The proof binds its control transition and all five physical slots. Native
constraints force both control-register high limbs to zero. Exact token codes
retain these values. Port enumeration covers both registers and every lane
half. Both pointer limbs stay explicit in every raw RAM address.

The native outputs equal the original split reference result. These facts hold
for both cache modes. They add no operand, schedule or expected-output premise.
They do not yet prove Sail retirement or the complete mixed memory history.

Twenty-four new roots passed focused kernel and axiom checks. They use only the
three allowed axioms. The explicit inventory now contains 12,842 roots. All
previous roots remain present. The final bounded check passed and left no owned
process running. An explicit vector-index bound avoids the earlier memory-cap
failure. Resource limits stay unchanged. The fixed setup source bridge, other
split arithmetic workers and the full unsigned target remain open. Full
validation remains pending.

### Native chi5 call-ABI obligation

A successful reference control read now identifies the unique native blessed
call. The proof covers all 361 control words. Initialized pointer words recover
the exact supported reference pointer. Pointer alignment excludes low-limb
carry and word overflow for every state lane. Each actual RAM port then has
the original reference cell address. Both native lane halves have the exact
reference thirty-two-bit values.

Twelve new roots passed focused kernel and axiom checks. They use only the
three allowed axioms. The explicit inventory now contains 12,854 roots. All
previous roots remain present. The last bounded group passed and left no owned
process running. Sail write execution and the combined native history remain
open. The fixed setup source bridge and the full unsigned target remain open.
Full validation remains pending.

### Native chi5 Sail call-execution obligation

The actual native chi5 history now executes the original complete split call.
The proof projects the complete write list to the original reference writes.
It includes both registers, all lane halves and the Sail frame. Actual reads
recover every input lane. The imported equations prove each output lane.
The proof uses the explicit supported reference ABI, initialized pointer bound,
actual per-port observations and exact history permutation. The full mixed
history must still supply these intermediate facts.

Four new roots passed focused kernel and axiom checks. They use only the three
allowed axioms. The explicit inventory now contains 12,858 roots. All previous
roots remain present. Both cache modes passed the last bounded check. It left
no owned process running. The fixed setup source bridge, column-parity and
theta/rho call effects, and the full unsigned integration remain open. Full
validation remains pending.

### Native column-parity controller obligation

The retained parity controller now proves the original control transitions.
It selects the iota round only for iteration zero. It includes the final call
in round twenty-four. The separate slot table retains all six original physical
slots and the native execute-key offset. The leading padding row stays explicit.
The importer compares every selected value with the complete native source.
The kernel proves the emitted row properties and static-table soundness.

Seven new roots passed focused kernel and axiom checks. They use only the three
allowed axioms. The explicit inventory now contains 12,865 roots. All previous
roots remain present. The proof reuses the established kernel-checked slot cache.
The last bounded group passed and left no owned process running. Resource caps
stay unchanged. Parity arithmetic and call execution remain open. The fixed
setup source bridge, theta/rho call effect and full unsigned integration remain
open. Full validation remains pending.

### Native parity slot-key and byte-iota obligations

Exact slot-table membership now binds all six original physical lanes. The
proof checks the full control key and rejects the padding row for a live key.
The native byte-iota table now proves both byte bounds and the exact output.
Seven columns reuse the established imported iota data. The counter column has
a different RLE partition. A kernel proof shows that its values agree with the
original arithmetic reference. The proof retains every physical column.

Eight new roots passed focused kernel and axiom checks. They use only the three
allowed axioms. The explicit inventory now contains 12,873 roots. All previous
roots remain present. The final bounded group passed and left no owned process
running. Five-input parity arithmetic, native parity call execution, theta/rho
call execution, the fixed setup source bridge and full unsigned integration
remain open. Full validation remains pending.

### Native five-input parity lookup obligation

The actual five-input XOR table now proves the exact nibble operation. It bounds
all five inputs and the output. It preserves the zero field and native tag 64.
The literal importer checks all 8,388,608 values in the eight physical columns.
It stores shared literal nodes. The output uses sixteen nodes. Kernel proofs
check all 256 output transitions and the actual key-column transitions. They
derive the operation on every row. The proof adds no expected-result premise.

Nineteen new roots passed focused kernel and axiom checks. They use only the
three allowed axioms. The explicit inventory now contains 12,892 roots. All
previous roots remain present. The last bounded group passed and left no owned
process running. The packed-checker pilot stays unchanged. Native parity query
binding and call execution, theta/rho call execution, the fixed setup source
bridge and full unsigned integration remain open. Full validation remains
pending.

### Native parity generic-setup and query obligations

The complete parity setup view now retains all four native regions and physical
zero padding. A streaming regression reads the current source file. It compares
all 33,554,432 physical cells. It also checks every retained view's source bytes.
The regression passed. Kernel proofs select the exact region from each native
query discriminator. Both native cache modes now enforce all twenty-two actual
generic queries. The four byte-iota queries prove their exact byte operation.
The sixteen parity queries prove their exact five-input nibble operation.

Twenty new roots passed focused kernel and axiom checks. They use only the
three allowed axioms. The explicit inventory now contains 12,912 roots. All
previous roots remain present. The final bounded checks passed and left no owned
process running. The source comparison is a runtime fidelity check. It does not
close the formal JSON source bridge. Native parity lane effects and Sail call
execution, theta/rho call execution, the source bridge and full unsigned
integration remain open. Full validation remains pending.

### Native parity lane-effect obligation

Both native cache modes now prove the complete parity lane result. The proof
uses the actual twenty-two generic queries and all six physical lanes. It
derives each written limb from the queried nibbles. It proves the complete
five-input XOR. The four readonly inputs keep their values. The first lane
uses the four actual byte-iota queries and the three native linear equations.
Its complete write equals its read XOR the selected original round constant.
The native controller selects that constant only on the first column. It
also binds the original control transition and all six physical slots.
`parity_native_reference_schedule` gives the unchanged `Call.result` equality.
The proof adds no result or operand premise.

Fifty-two new roots passed focused kernel and axiom checks. They use only the
three allowed axioms. The explicit inventory now contains 12,964 roots. All
12,912 previous roots remain present. Earlier combined reference checks
reached the memory cap. The final proof separates the finite reference
calculation from the native values. The last bounded group passed. It used
633 MiB of physical memory and left no owned process running. Resource caps
stay unchanged. Native parity Sail call execution, theta/rho call execution,
the formal setup source bridge and full unsigned integration remain open.
The packed-checker pilot stays unchanged. Full validation remains pending.

### Native parity Sail call obligation

`parity_call_executes` now proves the original complete parity `Call.Executes`
relation. Both native cache modes pass. The proof binds the actual control and
pointer registers. It checks all twelve lane halves and the full native write
list. The initialized pointer leaves room for every state and scratch slot.
The proof retains initialized read-word bounds, exact event permutation,
actual read observations and `SailHistory`. These premises also bound the old
scratch input. The parity equations do not constrain that old input. The
history proof gives the complete Sail memory frame. It adds no result premise.

Twenty-five new roots passed focused kernel and axiom checks. They use only the
three allowed axioms. The explicit inventory now contains 12,989 roots. All
12,964 previous roots remain present. The last bounded group passed. It used
627 MiB of physical memory and left no owned process running. Chi5 and parity
now have native call-execution proofs. Theta/rho call execution, the formal
setup source bridge and full unsigned integration remain open. The combined
history must supply the initialized bounds, read observations and event
permutations. The packed-checker pilot stays unchanged. Full frontend checks,
environment audit and baseline refresh, transitive kernel replay and Linux
runtime and warm-cache qualification remain pending.

### Native theta/rho controller and slot obligations

The retained native controller now proves the original control transition and
all five exact column flags. The slot region retains all nine physical
columns. It proves all five state slots and both neighboring parity slots.
Exact slot-key membership rejects the leading padding row. The complete
control key selects the unique original call. The generic controller proof
uses the retained native generic extent. Both region views keep the same
complete source bytes. No production source or reference changed.

Twelve new roots passed focused kernel and axiom checks. They use only the
three allowed axioms. The explicit inventory now contains 13,001 roots. All
12,989 previous roots remain present. The last bounded group passed. It used
649 MiB of physical memory and left no owned process running. Native theta/rho
arithmetic and Sail call execution remain open. The formal setup source bridge
and full unsigned integration remain open. Design items 2 and 3 follow the
machine targets. The packed-checker pilot stays unchanged. Full validation
remains pending.

### Native theta/rho arithmetic lookup obligations

The full unsigned target now has both native theta/rho arithmetic lookup
proofs. `xor_byte_table_sound` proves the complete byte-XOR relation.
`theta_split_table_sound` proves the complete XOR/split relation. The proofs
bound both byte keys and the selected shift. They derive both exact output
fragments. They retain every physical padding field and discriminator.
The native XOR region has 65,536 rows. The native XOR/split region has 524,288
rows. Each region retains all nine physical columns.

Sixteen kernel certificates check every low and high fragment shift.
A general evaluation proof lifts the checked native node transitions to all
rows. The generator supplies finite node correspondences. Kernel proofs check
those correspondences against the imported nodes. The full frontend gate now
checks that the generated correspondence sources are current.

The shared literal importer keeps the exact native region length. It can add
zero encoding slots outside that length. Those slots cannot supply lookup
membership. It checks every original source value after encoding. The two new
regions passed all 5,308,416 source-cell comparisons. Serial proof elaboration
keeps the fragment certificates within the existing resource limits. Earlier
attempts reached the memory cap. The limits stay unchanged.

The final focused group passed 116 source-module checks. It includes the
affected parity consumers and the complete parity source-cell comparison.
All 98 new roots passed direct axiom checks. They use only the three allowed
axioms. The explicit inventory now contains 13,099 roots. All 13,001 previous
roots remain present. The last bounded group used 1,773 MiB of physical memory
and left no owned process running. A wider intermediate group stopped safely
after it reached unrelated reference proofs. The final group checks the
affected sources. Generator freshness and Python syntax checks also passed.

Native theta/rho query binding, lane effects and Sail call execution remain
open. The formal setup source bridge and full unsigned integration remain
open. Design items 2 and 3 follow the machine targets. The packed-checker pilot
stays unchanged. Full frontend checks, environment audit and baseline refresh,
transitive kernel replay, and Linux runtime and warm-cache qualification
remain pending.

### Native theta/rho fixed-query obligation

The full unsigned target now has all fifty native theta/rho fixed-query
bindings. Both cache modes pass. The eight byte-XOR queries enforce their
complete operation. The forty XOR/split queries enforce both exact shifted
fragments. The two remaining queries select the complete native slot and
control regions. Every query keeps all nine physical fields.

The new composed setup view retains all 4,194,304 physical rows. It selects
each original region at its native offset and retains the trailing zero rows.
All 37,748,736 physical source-cell comparisons passed. The region-selection
proof rejects every wrong discriminator and the physical zero padding.
It adds no operand or expected-result premise. The earlier generic view and
its public proofs remain present.

Both new proof modules passed focused kernel checks. The complete physical
source comparison passed. All 21 new roots passed direct axiom checks. They
use only the three allowed axioms. The explicit inventory now contains 13,120
roots. All 13,099 previous roots remain present. The last bounded proof group
used 724 MiB of physical memory and left no owned process running.

Native theta/rho lane effects and Sail call execution remain open. The formal
setup source bridge and full unsigned integration remain open. Exact lookup,
request and RAM matching stay explicit. Design items 2 and 3 follow the machine
targets. The packed-checker pilot stays unchanged. Full frontend checks,
environment audit and baseline refresh, transitive kernel replay, and Linux
runtime and warm-cache qualification remain pending.

### Native theta/rho byte-input binding obligation

The full unsigned target now has native theta/rho byte-input bindings in both
cache modes. Every state operand has its canonical byte bound. Every fragment
query consumes the same D byte and lane shift as the original native queries.
The D bytes and both fragments have their exact native arithmetic meaning.
Both readonly lanes preserve all four actual memory limbs.

The actual memory-port expressions pack each state read limb from its two
queried bytes. The previous parity lane has the same packing proof. These
equations and native byte bounds give canonical sixteen-bit read values for
all five state lanes and the previous parity lane. The proofs add no input
value or expected-result premise. The next parity lane still needs its
initialization-derived read bounds and its native carry proof.

Both new modules passed focused kernel checks. All 20 new roots passed direct
axiom checks. They use only the three allowed axioms. The explicit inventory
now contains 13,140 roots. All 13,120 previous roots remain present. The last
bounded group used 603 MiB of physical memory and left no owned process
running. An explicit small column-index bound removed an earlier elaboration
memory spike. Resource limits stay unchanged.

Native theta/rho rotation, write-lane effects and Sail call execution remain
open. The formal setup source bridge and full unsigned integration remain
open. Design items 2 and 3 follow the machine targets. The packed-checker pilot
stays unchanged. Full validation remains pending.

### Native theta/rho next-parity rotation and D-lane obligation

Native constraints now prove the original one-bit next-parity rotation.
The complete D lane equals the previous parity lane XOR that rotation.
`theta_d_native_reference` states this complete native relation. Both cache
modes use the current native equations. The proof uses the four initialized
read limb bounds for the next parity lane. It derives every top bit and carry
from native Boolean assertions and the actual byte-query expressions. No
top-bit value or D result is an input premise.

Both new modules passed focused kernel checks. All 18 new roots passed direct
axiom checks. They use only the three allowed axioms. The explicit inventory
now contains 13,158 roots. All 13,140 previous roots remain present. The last
bounded group used 445 MiB of physical memory and left no owned process
running. Resource limits stay unchanged.

Native theta/rho selected rotations, write-lane effects and Sail call execution
remain open. The formal setup source bridge and full unsigned integration
remain open. The combined history must supply the initialized read bounds.
Design items 2 and 3 follow the machine targets. The packed-checker pilot stays
unchanged. Full validation remains pending.

### Native theta/rho controller, slot and rho-selection obligation

Active native constraints now select the original theta/rho call and all five
exact column flags. Both actual controller queries bind all seven original
physical slots. The slot key retains the complete control word and execute
flag. The native byte shift equals the selected original rho offset modulo
eight. Both cache modes pass. The proof adds no expected-result premise.

The new module and affected consumers passed focused kernel checks. All eight
new roots passed direct axiom checks. They use only the three allowed axioms.
The explicit inventory now contains 13,166 roots. All 13,158 previous roots
remain present. The last bounded group used 601 MiB of physical memory and
left no owned process running. The slot theorem's comment now gives its actual
seven-lane scope. Its public statement stays unchanged.

Native theta/rho write-lane equations, complete lane effects and Sail call
execution remain open. The formal setup source bridge and full unsigned
integration remain open. Design items 2 and 3 follow the machine targets. The
packed-checker pilot stays unchanged. Full validation remains pending.

### Native theta/rho write-equation obligation

Native constraints now prove all twenty actual theta/rho write equations.
Each equation uses all five native flags and the original rho byte placement.
Exact column flags select each written limb's original rho expression. Both
cache modes pass. The proof derives the equations from the imported native
assertions. It adds no write-value or expected-result premise.

The new module passed focused kernel checks. All four new roots passed direct
axiom checks. They use only the three allowed axioms. The explicit inventory
now contains 13,170 roots. All 13,166 previous roots remain present. The last
bounded group used 1,368 MiB of physical memory and left no owned process
running. Resource limits stay unchanged.

Canonical write bounds, complete theta/rho lane effects and Sail call execution
remain open. The formal setup source bridge and full unsigned integration
remain open. Design items 2 and 3 follow the machine targets. The packed-checker
pilot stays unchanged. Full validation remains pending.

### Native theta/rho complete lane-effect obligation

Both native cache modes now prove the complete original theta/rho lane effect.
The actual write limbs have canonical sixteen-bit values. All twenty write
limbs pack the exact original byte rotation. The complete output lane equals
the original state lane XOR the native D lane, followed by the original rho
rotation. The native controller selects the original call and all seven
physical slots. Both parity-input lanes stay unchanged.

`theta_native_reference_schedule` gives the unchanged complete call reference.
The proof keeps the initialized next-parity read bounds explicit. Native
assertions derive all four top bits and carries. Exact native lookup membership
derives every byte XOR and fragment. The proof adds no expected-result premise.

All six new modules passed focused kernel checks. All 26 new roots passed
direct axiom checks. They use only the three allowed axioms. The explicit
inventory now contains 13,196 roots. All 13,170 previous roots remain present.
The byte-rotation kernel check used 1,596 MiB of physical memory. The final
native group used 476 MiB. Both checks left no owned process running. The proof
groups the sixty-four rotations into eight declarations. Resource limits stay
unchanged.

Native theta/rho Sail call execution and full unsigned integration remain open.
The combined history must supply the initialized read bounds. The formal setup
source bridge remains open. Design items 2 and 3 follow the machine targets.
The packed-checker pilot stays unchanged. Full frontend validation, environment
audit, baseline refresh, transitive replay and Linux qualification did not run.

### Native theta/rho Sail call obligation

`theta_call_executes` now proves the original complete theta/rho call from the
actual native memory ports. Both cache modes pass. The proof binds the exact
control word, pointer, seven physical slots and fourteen lane halves. It binds
every actual write to the original call write list.

The proof keeps initialized read bounds, exact read observations and the exact
event permutation explicit. Those read bounds supply the next-parity carry
proof. Native constraints bound state writes. Readonly parity refreshes retain
their initialized values. No result value or lane-effect premise is an input.
Production circuits and Rust stay unchanged.

All eleven new modules passed focused kernel checks. All 27 new roots passed
direct axiom checks. They use only the three allowed axioms. The explicit
inventory now contains 13,223 roots. All 13,196 previous roots remain present.
The bounded group used 514 MiB of physical memory and left no owned process
running. Resource limits stay unchanged.

The combined native split-call chain and full unsigned integration remain open.
The formal setup source bridge remains open. Design items 2 and 3 follow the
machine targets. The packed-checker pilot stays unchanged. Full frontend
validation, environment audit, baseline refresh, transitive replay and Linux
qualification did not run.

### Native split-pool controller and call-dispatch obligations

`fixed_control_setup_facts` derives the two controller facts from exact
membership in the complete retained native tables. `fixed_memory_history`
uses those facts with native equations and exact logical RAM matching. It
proves address preservation and strict read-before-write order for every
physical split port. No controller-semantic premise is an input.

`native_call_executes` dispatches each actual split row to the original
complete Sail call. It covers parity, theta/rho and chi5 in both cache modes.
It keeps initialized read bounds, exact read observations and the event
permutation explicit. These proofs use `fixedSetup`, the complete retained
tables. The original JSON source-to-table obligation remains separate and open.

All three new modules passed focused kernel checks. All four new roots passed
direct axiom checks. They use only the three allowed axioms. The explicit
inventory now contains 13,227 roots. All 13,223 previous roots remain present.
The final bounded group used 473 MiB of physical memory and left no owned
process running. Resource limits stay unchanged.

Full unsigned integration must connect these native worker calls to the same
initialized CPU history. It must close the formal setup source bridge. The
complete native 361-call chain must connect to the proved physical schedule.
Design items 2 and 3 follow the machine targets. The packed-checker pilot stays
unchanged. Full frontend validation, environment audit, baseline refresh,
transitive replay and Linux qualification did not run.

### Native complete split-permutation obligation

`native_permutation_of_initialized_chain` now proves the original Keccak
permutation from all 361 actual native split calls. Both cache modes pass.
The theorem uses the current imported equations and the complete retained
native setup tables. It adds no expected output or physical-step premise.

The proof binds each call index to its actual reference control read. It
derives distinct aligned write destinations and all final touched words.
Every untouched physical word retains its prior value. Exact low and high
word reads identify each complete canonical lane. These facts prove the
original physical micro-step for each native row. The existing complete
schedule theorem then gives the original permutation.

The theorem keeps initialized Sail histories, exact event permutations, read
observations, public arguments and physical snapshots explicit. The unused
padding lane has value zero and needs no initialized memory cell. Full unsigned
integration must derive these histories and snapshots from the combined CPU
and worker memory argument. It must also close the formal JSON source-to-table
bridge. The original full unsigned target stays unchanged.

All eight new modules passed focused kernel checks. All 20 new roots passed
direct axiom checks. They use only the three allowed axioms. The explicit
inventory now contains 13,247 roots. All 13,227 previous roots remain present.
The final bounded group used 491 MiB of physical memory and left no owned
process running. Generic list proofs replaced a large finite destination
check. Explicit lane-pair arguments removed an elaboration timeout. Resource
limits stay unchanged.

The combined full unsigned machine proof remains open. Design items 2 and 3
follow the machine targets. The packed-checker pilot stays unchanged. Full
frontend validation, environment audit, baseline refresh, transitive replay
and Linux qualification did not run.

### Native split combined-history write-bound obligation

`native_write_words_bounded` proves canonical raw write-word limbs for all
three split workers in both cache modes. Exact native equations and the
complete retained tables derive the control and state write bounds. Pointer
and readonly refreshes retain their initialized input bounds. No Sail history,
call argument or expected result is an input to this bound proof.

`native_write_rule` places each split row inside an arbitrary combined memory
pool. All actual ports write at the same imported offset two. The common time
induction can therefore supply all row read bounds and obtain each raw write
bound. This closes the split-worker component of the combined history's
write-bound rule. It does not assume the worker result or a separate split RAM
permutation.

Both new modules passed focused kernel checks. All five new roots passed
direct axiom checks. They use only the three allowed axioms. The explicit
inventory now contains 13,252 roots. All 13,247 previous roots remain present.
The bounded group used 514 MiB of physical memory and left no owned process
running. Resource limits stay unchanged.

The complete combined CPU and worker history still needs its clock facts,
path execution and initialization connection. The formal setup source bridge
remains open. Design items 2 and 3 follow the machine targets. The packed-checker
pilot stays unchanged. Full frontend validation, environment audit, baseline
refresh, transitive replay and Linux qualification did not run.

### Full unsigned combined-history clock and order obligations

`unrolled_request_times_unique` derives unique clocks for the complete native
caller set. `unrolled_request_clock_bounds` uses the exact combined request
permutation. It bounds every standard and split worker invocation. It also
proves exact live matching and unique live fulfillment clocks. No separate
worker permutation or typed decoder premise is an input.

`unrolledFullMemoryData` retains one architectural RAM pool. It contains all
CPU, standard worker and split worker edges. `unrolled_full_write_clocks`
bounds every produced clock. `unrolled_full_memory_clocks` uses exact combined
RAM matching to bound every read clock. `unrolled_full_memory_facts` derives
address preservation and strict read-before-write order for the complete pool.
The CPU's omitted virtual port has the native zero-clock token. The split
ports use the current derived-borrow equations. Seed clock bounds and fixed
controller provenance remain explicit. These are supporting obligations of
the unchanged full unsigned target.

All three new modules passed focused kernel checks. All six new roots passed
direct axiom checks. They use only the three allowed axioms. The explicit
inventory now contains 13,258 roots. All 13,252 previous roots remain present.
The final bounded group used 531 MiB of physical memory and left no owned
process running. Resource limits stay unchanged.

The combined history still needs its complete write rules, path execution
and initialization connection. The formal setup source bridge remains open.
Design items 2 and 3 follow the machine targets. The packed-checker pilot
stays unchanged. Full frontend validation, environment audit, baseline
refresh, transitive replay and Linux qualification did not run.

### Full unsigned combined-history raw write-rule obligation

`unrolled_full_ordinary_source` obtains the exact public instruction for each
non-caller row. `unrolled_full_cpu_write_rule` proves raw write bounds for all
six CPU families inside an arbitrary ambient history. Both caller classes
use the imported zero-destination equations. Ordinary rows use their original
instruction and physical ROM image. The proof does not equate the physical
ROM image with the verifier's native zero seed.

`unrolled_full_memory_write_rules` combines CPU, standard worker and split
worker rules in the same architectural pool. Chronological induction supplies
each row's read bounds. The proof keeps standard round masks and the split
equations under the complete retained tables explicit. Supported public use
must derive the round masks. The formal source bridge must transfer the
accepted split equations to those retained tables. These supporting premises
do not change the full unsigned target.

Both new modules passed focused kernel checks. All three new roots passed
direct axiom checks. They use only the three allowed axioms. The explicit
inventory now contains 13,261 roots. All 13,258 previous roots remain present.
The final bounded group used 530 MiB of physical memory and left no owned
process running. Resource limits stay unchanged.

The combined history still needs zero-register preservation, path execution
and its initialization connection. The public round-control and formal setup
source obligations remain open. Design items 2 and 3 follow the machine
targets. The packed-checker pilot stays unchanged. Full frontend validation,
environment audit, baseline refresh, transitive replay and Linux qualification
did not run.

### Full unsigned combined-history zero and realization obligations

`port_not_zero` checks all imported split port addresses in both cache modes.
Every port accesses a nonzero register or the separate RAM space. The result
needs no witness bounds. `unrolled_full_memory_zero_rules` proves zero-register
preservation for the complete CPU and worker pool. Caller writes use the
native zero equations. Ordinary writes use the exact public instruction.

`unrolled_full_memory_history` assembles the combined native history proof.
It derives zero seed values from initialized Sail reads and canonical seed
words. It then proves every raw read and write bound, every terminal word
bound, one exact Sail history and each terminal memory observation. No
separate CPU or worker RAM permutation is an input.

This supporting theorem keeps native initialization, public round masks and
split setup interpretation explicit. The target proof must derive them from
its existing public inputs. Physical ROM initialization remains separate from
the native verifier seed. The full unsigned target stays unchanged.

All three new modules passed focused kernel checks. All three new roots passed
direct axiom checks. They use only the three allowed axioms. The explicit
inventory now contains 13,264 roots. All 13,261 previous roots remain present.
The final bounded group used 538 MiB of physical memory and left no owned
process running. Resource limits stay unchanged.

Full unsigned path execution and initialization integration remain open.
The public round-control and formal setup source obligations remain open.
Design items 2 and 3 follow the machine targets. The packed-checker pilot
stays unchanged. Full frontend validation, environment audit, baseline
refresh, transitive replay and Linux qualification did not run.

### Full unsigned combined worker-schedule obligation

`unrolled_full_requests_match` removes zero-clock fulfillments with the
actual native activity and timestamp equations. Exact combined matching then
accounts for every worker row. `unrolled_full_fulfillment_times_unique`
excludes shared invocation clocks across both worker pools.

`unrolled_full_fulfillment_slot` obtains an actual selected CPU caller for
each fulfillment. The invocation clock equals the caller's initial clock plus
one. `unrolled_full_standard_worker_slot` and `unrolled_full_split_worker_slot`
place all physical worker events in that caller's final cycle slot. Both
split cache modes use their current imported offset two. No decoder registry,
worker occurrence plan or separate request permutation is an input.

The new module passed focused kernel checks. All five new roots passed direct
axiom checks. They use only the three allowed axioms. The explicit inventory
now contains 13,269 roots. All 13,264 previous roots remain present. The final
bounded group used 536 MiB of physical memory and left no owned process
running. Resource limits stay unchanged.

Full unsigned path execution and initialization integration remain open.
The public round-control and formal setup source obligations remain open.
Design items 2 and 3 follow the machine targets. The packed-checker pilot
stays unchanged. Full frontend validation, environment audit, baseline
refresh, transitive replay and Linux qualification did not run.

### Full unsigned exact instruction-window obligation

`unrolled_full_fulfillment_window` proves an exact instruction-window test.
A fulfillment event lies in a CPU cycle if and only if that CPU row selects
the same full-width request. Aligned state clocks and unique caller times
exclude every other cycle. The standard and split event-window theorems apply
this result to each actual physical port. Both split cache modes pass.

`unrolled_cpu_event_time` derives each CPU event's native access slot.
`unrolled_cpu_event_window` proves that each CPU event lies in exactly its
own instruction window. The proof covers all six CPU families and both
caller forms. These results supply the exact window membership needed to
extract native calls from the combined history. They add no occurrence plan
or per-worker permutation premise.

Both new modules passed focused kernel checks. All five new roots passed
direct axiom checks. They use only the three allowed axioms. The explicit
inventory now contains 13,274 roots. All 13,269 previous roots remain present.
The final bounded group used 535 MiB of physical memory and left no owned
process running. Resource limits stay unchanged.

Full unsigned path execution and initialization integration remain open.
The public round-control and formal setup source obligations remain open.
Design items 2 and 3 follow the machine targets. The packed-checker pilot
stays unchanged. Full frontend validation, environment audit, baseline
refresh, transitive replay and Linux qualification did not run.

### Full unsigned exact event-group obligation

`unrolled_full_instruction_events` partitions the actual combined event list
at each native instruction window. The group contains exactly that row's
CPU events, its matched standard worker events and its matched split worker
events. The theorem gives an equality of lists. It retains native row order
and leaves chronological permutation to the shared history proof.

`unrolled_full_ordinary_events` proves that an ordinary instruction window
contains only its own CPU events. No worker from either pool can enter that
window. These results close exact event grouping for full unsigned path
extraction. They assume no worker occurrence plan or separate RAM argument.

The new module passed focused kernel checks. Both new roots passed direct
axiom checks. They use only the three allowed axioms. The explicit inventory
now contains 13,276 roots. All 13,274 previous roots remain present. The final
bounded group used 531 MiB of physical memory and left no owned process
running. Resource limits stay unchanged.

Full unsigned path execution and initialization integration remain open.
The public round-control and formal setup source obligations remain open.
Design items 2 and 3 follow the machine targets. The packed-checker pilot
stays unchanged. Full frontend validation, environment audit, baseline
refresh, transitive replay and Linux qualification did not run.

### Full unsigned caller-history extraction obligation

The two caller event theorems reduce each full native caller window to its
own CPU events and one matched worker. Unique invocation times select the
worker. The native CSR values exclude contributions from the other pool.
This result covers standard and split callers in both split cache modes.

`unrolled_full_caller_zero_ports` uses exact public decoder matching to prove
that both architectural CPU ports address x0. The two caller history theorems
then extract each worker's exact Sail history from the combined history.
They remove only the CPU x0 events. The extracted event list is a permutation
of every actual worker port. The prefix and suffix histories keep the same
caller boundaries. No separate worker RAM permutation or expected effect
is an input.

All three new modules passed focused kernel checks. All five new roots passed
direct axiom checks. They use only the three allowed axioms. The explicit
inventory now contains 13,281 roots. All 13,276 previous roots remain present.
The final bounded group used 529 MiB of physical memory and left no owned
process running. Resource limits stay unchanged.

Full unsigned path execution still needs native input observations at these
boundaries and public supported-use controls. Initialization integration and
the formal setup source bridge remain open. Design items 2 and 3 follow the
machine targets. The packed-checker pilot stays unchanged. Full frontend
validation, environment audit, baseline refresh, transitive replay and Linux
qualification did not run.

### Full unsigned native split input-observation obligation

`history_unique_address_read` derives a cell's initial read when its address
occurs once in the actual history. Other addresses may repeat. The native
register proofs check that control and pointer registers each occur once in
every split layout. Their initial observations need no lane-address premise.

`native_call_addresses_distinct` uses these actual register reads and the
public call arguments. It derives the original aligned lane layout from the
native controller and pointer equations. The complete native write projection
then supplies distinct addresses for every real port. Both cache modes pass.

`native_call_input_observations` derives every remaining native read from the
same initialized history. `native_call_executes_of_history` proves the original
complete split call. It no longer takes input observations or address
distinctness as premises. Public call arguments, canonical raw read bounds,
initialized cells and exact event matching remain explicit. The complete
retained fixed tables still need the formal JSON source bridge.

All three new modules passed focused kernel checks. All nine new roots passed
direct axiom checks. They use only the three allowed axioms. The explicit
inventory now contains 13,290 roots. All 13,281 previous roots remain present.
The final bounded group used 480 MiB of physical memory and left no owned
process running. Resource limits stay unchanged.

Full unsigned path execution must connect the extracted caller windows to
these native calls and derive supported public arguments. Initialization
integration and the formal setup source bridge remain open. Design items 2
and 3 follow the machine targets. The packed-checker pilot stays unchanged.
Full frontend validation, environment audit, baseline refresh, transitive
replay and Linux qualification did not run.

### Full unsigned native split caller-retirement obligation

`unrolled_full_split_memory_call` connects each actual split caller window
to the original complete memory-call relation. The combined pool supplies
all raw read bounds. Its prefix history supplies readable cells at the call.
Supported public arguments remain explicit at this extracted boundary.

`unrolled_full_split_caller_source` identifies the public split instruction,
its full PC and its actual worker kind. The proof uses exact decoder lookup
and the complete request CSR. Standard worker CSRs cannot alias a split CSR.
`unrolled_full_split_pc_binding` derives canonical PC limbs, the four-byte
advance and original Sail PC retirement from the imported ADD/SUB equations.

`unrolled_full_split_caller_retirement` combines native memory execution with
that PC retirement. It executes the original complete split call between the
actual caller boundaries, with the native start and final PCs. PC preparation
preserves all supported call arguments and tracked cell reads. No native
effect, input observation or retirement result is a premise.

All four new modules passed focused kernel checks. All four new roots passed
direct axiom checks. They use only the three allowed axioms. The explicit
inventory now contains 13,294 roots. All 13,290 previous roots remain present.
The final bounded group used 534 MiB of physical memory and left no owned
process running. Resource limits stay unchanged.

The full path proof must still derive supported public arguments at each
reachable boundary and connect ordinary and standard worker cycles.
Initialization integration and the formal setup source bridge remain open.
Design items 2 and 3 follow the machine targets. The packed-checker pilot
stays unchanged. Full frontend validation, environment audit, baseline
refresh, transitive replay and Linux qualification did not run.

### Full unsigned ordinary-history and MUL/DIV execution obligations

`unrolled_full_ordinary_history` extracts the exact native instruction
history from the combined memory pool. It covers all six CPU families.
It supplies raw bounds for each actual CPU read port. The proof uses the
common ordered history and the exact global event permutation.

`unrolled_full_muldiv_execution` connects that history to the original
Sail MUL/DIV instruction. The public registry supplies the source and
decoder query. The native first read port supplies the operand bound.
The result uses the actual native start and final PCs.

Both new modules passed focused kernel checks. Both new roots passed
direct axiom checks. They use only the three allowed axioms. The explicit
inventory now contains 13,296 roots. All 13,294 previous roots remain
present. The final bounded group used 531 MiB of physical memory and
left no owned process running. Resource limits stay unchanged.

The full path proof must still connect the remaining ordinary and standard
worker cycles. It must derive supported public arguments at each reachable
boundary. Initialization integration and the formal setup source bridge
remain open. Design items 2 and 3 follow the machine targets. The packed
checker pilot stays unchanged. Full frontend validation, environment audit,
baseline refresh, transitive replay and Linux qualification did not run.

### Full unsigned subword execution obligation

`unrolled_full_subword_execution` executes all six original Sail subword
load and store forms at their actual shared-history boundaries. The public
registry supplies the source and full decoder query. The native history
supplies each initialized port address. Common read bounds and native
equations supply the effective address, containing word and byte offset.

The proof handles RAM and ROM. The same readonly prefix preserves public
ROM bytes. Those bytes give each ROM lookup its original Sail meaning.
The physical image stays separate from the verifier's raw boot seed.

The new module passed its focused kernel check. The new root passed its
direct axiom check. It uses only the three allowed axioms. The explicit
inventory now contains 13,297 roots. All 13,296 previous roots remain
present. The bounded group used 554 MiB of physical memory and left no
owned process running. Resource limits stay unchanged.

Full unsigned composition, supported-use derivation, initialization
integration and the formal setup source bridge remain open. Design items
2 and 3 follow the machine targets. The packed-checker pilot stays unchanged.
Full frontend validation, environment audit, baseline refresh, transitive
replay and Linux qualification did not run.

### Full unsigned stream-position obligation

`unrolled_full_cycle_count` derives each cycle's exact stream increment from
native clocks and state matching. `unrolled_full_initial_count` proves the
initial count is zero. `unrolled_full_terminal_count` proves the final count
includes each external read once. These results cover all six CPU families.

`unrolled_full_caller_read_disabled` proves that standard and split callers
consume no stream word. It uses exact public lookup and the imported packed
selector equations. It does not require a separate caller decoder registry.

The new module and all four roots passed focused kernel and direct axiom
checks. They use only the three allowed axioms. The explicit inventory now
contains 13,301 roots. All 13,297 previous roots remain present. The bounded
group used 540 MiB of physical memory and left no owned process running.
Resource limits stay unchanged.

Full unsigned composition, supported-use derivation, initialization
integration and the formal setup source bridge remain open. Design items
2 and 3 follow the machine targets. The packed-checker pilot stays unchanged.
Full frontend validation, environment audit, baseline refresh, transitive
replay and Linux qualification did not run.

### Full unsigned six-family ordinary-cycle obligation

`unrolled_full_ordinary_cycle` now executes every ordinary full native row
at its actual shared-history cuts. It covers arithmetic, modular operations,
external input, word memory, subword memory, shifts, bitwise operations,
control flow and multiply/divide. Each case uses its original Sail clause.
The result includes the exact stream increment and native PC endpoints.

`unrolled_full_ordinary_context` retains the filtered cycle history and its
canonical native order. `unrolled_full_pc_bounds` derives both PC endpoint
bounds from public queries, native state matching and verifier closure.
The subword shared-history lemma supports the complete cycle dispatch.
All previous public theorem statements stay unchanged.

The cycle proof derives raw x0 reads from the same Sail history and common
word bounds. It has no separate zero-value premise. Public configuration,
physical image, readonly ROM history and exact native matching stay explicit.

All changed modules and four new roots passed focused kernel and direct
axiom checks. They use only the three allowed axioms. The explicit inventory
now contains 13,305 roots. All 13,301 previous roots remain present. The
bounded group used 547 MiB of physical memory and left no owned process
running. Resource limits stay unchanged.

Standard-worker call integration, full path composition, supported-use
derivation, initialization integration and the formal setup source bridge
remain open. Design items 2 and 3 follow the machine targets. The packed
checker pilot stays unchanged. Full frontend validation, environment audit,
baseline refresh, transitive replay and Linux qualification did not run.

### Full unsigned standard-worker caller-cycle obligation

`unrolled_full_standard_caller_cycle` connects bigint and extended-round
workers to their actual caller cuts in the shared history. Each cycle
executes the original complete memory-call relation and Sail PC retirement.
The public source remains valid at the call. Native start and final PCs
match the same public instruction.

`unrolled_full_standard_addresses_distinct` derives port separation from
the complete initialized pool and exact matching. The observation theorem
then derives every input read. The worker-call theorem proves both native
call relations. The source and PC theorems connect full public lookup to
the actual matched worker. No call result, per-port observation or address
separation is a premise.

Commands, round controllers and worker RAM domains stay explicit. The
supported-use proof must derive them at reachable boundaries. The common
initialized boundary, raw bounds and exact matching also stay explicit.

All five new modules and six roots passed focused kernel and direct axiom
checks. They use only the three allowed axioms. The explicit inventory now
contains 13,311 roots. All 13,305 previous roots remain present. The bounded
group used 535 MiB of physical memory and left no owned process running.
Resource limits stay unchanged.

Full path composition, supported-use derivation, native ROM interpretation,
initialization integration and the formal setup source bridge remain open.
Design items 2 and 3 follow the machine targets. The packed-checker pilot
stays unchanged. Full frontend validation, environment audit, baseline
refresh, transitive replay and Linux qualification did not run.

### Full unsigned split-cycle and event-boundary obligations

`unrolled_full_split_caller_cycle` connects each split worker to its full
actual caller window. It retains the public source at that cut, the complete
native memory-call relation and original Sail retirement. Supported control
and pointer arguments remain explicit at the extracted boundary. Both cache
modes retain all actual native ports.

`unrolled_full_event_interval` places every CPU and worker event between
the native initial and terminal clocks. The complete combined request
permutation supplies each worker's slot. No separate worker schedule is
assumed. These results close the local split-cycle and event-boundary
obligations for full path composition.

Both modules and roots passed focused kernel and direct axiom checks. They
use only the three allowed axioms. The explicit inventory now contains
13,313 roots. All 13,311 previous roots remain present. The bounded group
used 537 MiB of physical memory and left no owned process running. Resource
limits stay unchanged.

Full path composition, supported-use derivation, native ROM interpretation,
initialization integration and the formal setup source bridge remain open.
Design items 2 and 3 follow the machine targets. The packed-checker pilot
stays unchanged. Full frontend validation, environment audit, baseline
refresh, transitive replay and Linux qualification did not run.

### Full unsigned physical-history path-composition obligation

`unrolled_full_cycle_transition` joins all six ordinary CPU families,
standard workers and split workers in one stream-indexed reference step.
It derives each native instruction and complete call result. The first
step starts from the original public Sail state. Later steps use the same
actual history cuts and native PCs.

`unrolled_full_physical_execution` composes the complete native state path.
It proves the combined full reference relation, terminal PC, tracked terminal
reads and exact total stream consumption. It uses the same initialized
physical history and exact combined matching throughout. It assumes no
instruction or worker execution result.

This theorem closes physical-history path composition. It is not yet a
proof of `UnrolledFullUnsigned`. The following named obligations remain:

1. Derive standard commands, round controllers and worker RAM domains from
   public supported use. Derive split arguments at each reachable caller cut.
2. Interpret native zero ROM tokens in the complete combined pool.
3. Connect the actual initialization boundary to that interpreted execution.
4. Prove the JSON source-to-fixed-setup bridge stated in `FixedSetup`.

Both new modules and roots passed focused kernel and direct axiom checks.
They use only the three allowed axioms. The explicit inventory now contains
13,315 roots. All 13,313 previous roots remain present. The bounded group
used 535 MiB of physical memory and left no owned process running. Resource
limits stay unchanged.

Design items 2 and 3 follow the machine targets. The packed-checker pilot
stays unchanged. Full frontend validation, environment audit, baseline
refresh, transitive replay and Linux qualification did not run.

### Full unsigned combined-pool ROM-interpretation obligation

`unrolled_full_rom_acceptance` now preserves full native acceptance under
public ROM interpretation. The proof covers all six CPU families and the
combined standard and split worker pools. CPU transfer projection uses
canonical addresses from that same native pool. It handles selected callers
through their two architectural x0 ports.

The complete transfer projection preserves exact state, request and RAM
permutations. `unrolled_full_rom_lookup` preserves every full-width public
decoder query. `unrolled_full_rom_unchanged` proves that each interpreted ROM
transfer refreshes its original public word. No alternate worker permutation
or execution result is a premise.

Worker RAM-domain contracts remain explicit. They keep standard and split
transfers fixed. Supported use must still derive those contracts together
with commands, round controls and split arguments at reachable caller cuts.
The native boot seed remains separate from the physical public byte image.

The new module and five roots passed focused kernel and direct axiom checks.
They use only the three allowed axioms. The explicit inventory now contains
13,320 roots. All 13,315 previous roots remain present. The bounded group
used 534 MiB of physical memory and left no owned process running. Resource
limits stay unchanged.

Public supported-use derivation, initialization-to-execution integration
and the formal setup source bridge remain open. Design items 2 and 3 follow
the machine targets. The packed-checker pilot stays unchanged. Full frontend
validation, environment audit, baseline refresh, transitive replay and Linux
qualification did not run.

### Full unsigned zero-boot execution-adapter obligation

`unrolled_full_boot_execution` now starts from the native zero boot image.
It constructs the physical initialized history through public ROM
interpretation. It derives common raw bounds, every cycle's execution,
terminal observations and exact stream consumption. The existing standalone
initialization-to-boot adapter supplies this theorem's boot interface.
The result returns the unchanged native terminal tokens through `ROMView`.

Round masks follow from the explicit round controller contract and native
packing equations. Exact lookup, request and RAM matching stay explicit.
No instruction, call result or completed reference trace is a premise.

The new module and root passed focused kernel and direct axiom checks.
It uses only the three allowed axioms. The explicit inventory now contains
13,321 roots. All 13,320 previous roots remain present. The bounded group
used 547 MiB of physical memory and left no owned process running. Resource
limits stay unchanged.

Two full-target obligations remain. Public supported use must supply
commands, round controls, worker RAM domains and split arguments at actual
caller cuts. The formal JSON source-to-fixed-setup bridge must supply the
canonical setup interpretation. The full target statement stays unchanged.
Design items 2 and 3 follow the machine targets. The packed-checker pilot
stays unchanged. Full frontend validation, environment audit, baseline
refresh, transitive replay and Linux qualification did not run.

### Full unsigned accepted-prefix obligation

`unrolled_full_prefix_accepted` constructs an accepted native prefix before
any actual positive-clock CPU boundary. It retains the same standard and
split setup data and both cache modes. The exact native memory split gives
the prefix its terminal frontier and preserves the full suffix facts.

The three prefix functions select actual CPU and worker rows. The transfer
theorem proves that they select exactly the writes before one common cut.
The request theorem restricts the complete combined ledger to that cut.
State matching restricts to the actual next CPU state. No independent prefix
match, command, round mask, supported argument or reference result is used.

All three new modules and six roots passed focused kernel and direct axiom
checks. They use only the three allowed axioms. The explicit inventory now
contains 13,327 roots. All 13,321 previous roots remain present. The bounded
group used 539 MiB of physical memory and left no owned process running.
Resource limits stay unchanged.

This closes native prefix construction for supported-use induction. Public
supported use must still supply the worker input contracts. The formal setup
source bridge also remains open. Design items 2 and 3 follow the machine
targets. The packed-checker pilot stays unchanged. Full frontend validation,
environment audit, baseline refresh, transitive replay and Linux qualification
did not run.

### Full unsigned prefix-frontier input obligations

`unrolled_full_prefix_worker_read` proves that a nonzero worker read in
the caller's final native slot comes from the exact prefix frontier. CPU
writes earlier in that cycle touch x0. Standard and split workers occupy
aligned final slots. Exact suffix matching excludes an intervening write.
No input value, valid command or reference result is assumed.

`unrolled_full_prefix_boot` preserves the public boot interface at the actual
prefix endpoint. Full public queries bound that endpoint's PC. Native clock
equations bound its timestamp. The accepted prefix closes the same typed
verifier boundary.

`unrolled_full_boot_execution_and_bounds` retains canonical terminal-word
bounds beside complete boot execution. These bounds let supported-use
induction recover worker registers from native frontier tokens. The existing
boot-execution theorem keeps its original public statement.

All changed modules and three new roots passed focused kernel and direct
axiom checks. They use only the three allowed axioms. The explicit inventory
now contains 13,330 roots. All 13,327 previous roots remain present. The
bounded group used 563 MiB of physical memory and left no owned process
running. Resource limits stay unchanged.

Public supported-use induction and the formal setup source bridge remain
open. Design items 2 and 3 follow the machine targets. The packed-checker
pilot stays unchanged. Full frontend validation, environment audit, baseline
refresh, transitive replay and Linux qualification did not run.

### Full unsigned reachable-input conversion obligations

`unrolled_full_supported_standard_inputs` converts reachable public full
reference arguments into native standard-worker commands, round controls
and RAM domains. The proof uses bounded actual frontier observations. It
reuses one extracted native ABI argument proof. The existing unified stream
reference theorem keeps its original public statement.

`unrolled_full_supported_split_inputs` obtains the blessed split index and
register arguments from public full-reference reachability. The native
split RAM-domain theorem then locates every actual port. It uses only the
pointer-word bound and two register observations. Native lane-value bounds
and an expected operation result are not premises. Both cache modes and
all three split layouts use their complete port enumeration.

All changed modules and four new roots passed focused kernel and direct
axiom checks. They use only the three allowed axioms. The explicit inventory
now contains 13,334 roots. All 13,330 previous roots remain present. The
bounded group used 541 MiB of physical memory and left no owned process
running. Resource limits stay unchanged.

The full native-prefix induction must connect these converters to the
proved boot execution and frontier facts. The formal setup source bridge
also remains open. Design items 2 and 3 follow the machine targets. The
packed-checker pilot stays unchanged. Full frontend validation, environment
audit, baseline refresh, transitive replay and Linux qualification did not run.

### Full unsigned reusable split-input obligation

`nativeCallArguments` retains only a derived blessed input control, a bounded
pointer word and its public RAM/alignment conditions. It stores no output,
memory effect or execution result. Actual reachable reference observations
prove these facts for the native tokens. The same tokens recover the public
arguments at any actual history cut that observes them.

`unrolled_full_supported_split_native_inputs` derives those reusable facts
and every native port domain from public full-reference reachability. This
removes the reference-state identity from the inputs needed by prefix
induction. Both cache modes retain their actual register ports.

All changed modules and four new roots passed focused kernel and direct
axiom checks. They use only the three allowed axioms. The explicit inventory
now contains 13,338 roots. All 13,334 previous roots remain present. The
bounded group used 531 MiB of physical memory and left no owned process
running. Resource limits stay unchanged.

Full native-prefix induction and the formal setup source bridge remain
open. Design items 2 and 3 follow the machine targets. The packed-checker
pilot stays unchanged. Full frontend validation, environment audit, baseline
refresh, transitive replay and Linux qualification did not run.

### Full unsigned native-input execution-interface obligation

`unrolled_full_split_arguments_at_cut` recovers public split arguments from
derived native input tokens at the exact caller cut. Exact combined matching
and initialized history supply its register observations. No lane value or
per-cut argument is assumed by the execution interface.

`unrolled_full_boot_execution_of_native_inputs` now executes the complete
boot trace from reusable standard and split input facts. It proves the full
reference relation and canonical terminal bounds. The native input facts
contain commands, controls, pointers and RAM locations. They contain no
worker output, instruction result or reference trace.

The selected-caller composition interfaces apply these facts at actual
selected callers. All three earlier public composition/execution statements
stay unchanged. Their existing interfaces now use the same kernel-checked
proofs through wrappers. The full machine target also stays unchanged.

All changed modules and five new roots passed focused kernel and direct
axiom checks. They use only the three allowed axioms. The explicit inventory
now contains 13,343 roots. All 13,338 previous roots remain present. The
bounded group used 533 MiB of physical memory and left no owned process
running. Resource limits stay unchanged.

Full native-prefix induction must still derive all reusable input facts
from public supported use. The formal setup source bridge also remains open.
Design items 2 and 3 follow the machine targets. The packed-checker pilot
stays unchanged. Full frontend validation, environment audit, baseline
refresh, transitive replay and Linux qualification did not run.

### Full unsigned supported-use induction obligation

`unrolled_full_supported_native_inputs` now derives every standard and split
worker input contract from public full-reference supported use. The proof
uses strong induction on the actual caller clock. Each earlier accepted
prefix executes from the original boot state. Its actual terminal frontier
supplies the current worker's bounded register reads.

Native request clocks prove that each earlier worker belongs to a smaller
caller clock. Exact prefix and suffix matching identify every current read
token. Public reachable arguments then give commands, round controls, split
input facts and all worker RAM domains. No native input contract, operation
result or completed reference trace is a premise of this induction.

`unrolled_full_supported_execution` composes those inputs with complete native
boot execution. `unrolled_full_soundness_of_setup_interpretation` connects the
original target and actual standalone initialization interface to that proof.
The wrapper exposes one open importer obligation: parsed fixed JSON must
imply the canonical setup interpretation. The target statement stays unchanged.

All changed modules and five new roots passed focused kernel and direct
axiom checks. They use only the three allowed axioms. The explicit inventory
now contains 13,348 roots. All 13,343 previous roots remain present. The
bounded group used 554 MiB of physical memory and left no owned process
running. Resource limits stay unchanged.

The formal setup source bridge remains open. Complete that bridge before
claiming the full target. Design items 2 and 3 follow the machine targets.
The packed-checker pilot stays unchanged. Full frontend validation,
environment audit, baseline refresh, transitive replay and Linux qualification
did not run.


### Full unsigned setup transport obligation

`equations_of_setup_refinement` now transports every native split equation
to a refined fixed table. It preserves every assertion and timestamp query.
The proof covers the three workers in both cache modes.
`control_of_fixed_setup_refinement` derives the native controller facts.

`unrolled_full_soundness_of_source_rows` connects this transport to the
original full target and its initialization adapter. It requires three
`FixedSetupRows` certificates. They cover parity, theta/rho and chi5. Each
certificate must map every parsed physical row, including padding, into the
complete fixed table. All three certificates remain open. No target or
existing premise changed.

The changed modules and six new roots passed focused kernel and direct axiom
checks. They use only the three allowed axioms. The explicit inventory now
contains 13,354 roots. All 13,348 previous roots remain present. The bounded
group used 554 MiB of physical memory and left no owned process running.
Resource limits stay unchanged.

A total JSON decoder prototype stays in the evidence directory. Its small
kernel tests and all 18 retained setup-directory JSON differential checks
passed. Direct kernel source evaluation exceeded the memory cap. The guard
stopped each probe and left no worker running. The prototype is not adopted.
The source certificates still need a compact kernel representation.

Design items 2 and 3 follow the machine targets. The packed-checker pilot
stays unchanged. Full frontend validation, environment audit, baseline
refresh, transitive replay and Linux qualification did not run.


### Full unsigned source-decoder transparency obligation

`Setup.parse` now uses `Import.SetupJson`. All decoder recursion is total.
`run_append` proves exact source-block composition. `parse_of_run` connects
checked block execution and a checked final state to the decoded JSON.
The kernel can keep earlier array data abstract during a later block check.

Focused checks passed for 101 modules. They include the changed importer,
source-interpretation proofs and complete theta/rho physical-table comparison.
All 18 retained setup-directory JSON files match the earlier parser. Every
decoded artifact field also matches. The edge controls cover numbers, Unicode,
duplicate keys, delimiters and malformed input. All seven named kernel
controls pass. Static setup checks also pass for 16 setup artifacts, 731
native source hashes, 15 production circuits and one derived fixture.

All 18 new roots passed direct axiom checks. They use only the three allowed
axioms. The explicit inventory now contains 13,372 roots. All 13,354 previous
roots remain present. The bounded focused group used 769 MiB of physical
memory and left no owned process running. Resource limits stay unchanged.

The decoder keeps the existing 64-bit number bound as an explicit integer.
The retained source bytes, imported values and target statements stay
unchanged. The three `FixedSetupRows` certificates remain open. A separate
block-certificate generator stays in the evidence directory until its kernel
checks pass. No full-source certificate is claimed by the decoder change.

Design items 2 and 3 follow the machine targets. The packed-checker pilot
stays unchanged. Full frontend validation, environment audit, baseline
refresh, transitive replay and Linux qualification did not run.


### Full unsigned parsed-field transport obligation

`SetupFields` proves that a successful setup parse preserves the complete
column field and the physical domain length. The proof retains the artifact
validation premise. `fixed_setup_rows_of_decoded_columns` connects these
fields to the original `FixedSetupRows` predicate. It includes physical padding.
It does not require a second evaluation of unrelated circuit fields.

The new module passed focused kernel checks. All five new roots passed direct
axiom checks. They use only the three allowed axioms. The explicit inventory
now contains 13,377 roots. All 13,372 previous roots remain present. The bounded
focused group used 399 MiB of physical memory and left no owned process
running. Resource limits stay unchanged.

The separate source-block experiment proved complete theta/rho JSON parsing.
It covered 909,925 bytes in 238 seconds and used 1,308 MiB of physical memory.
It used a character block representation of the same source bytes. This
experiment remains outside the branch. It does not close the three source
table certificates. Those certificates remain open. The parity source has
107,052 RLE block entries but only 283 distinct blocks. The chi5 source has
63,011 entries but only 539 distinct blocks. Reuse these blocks to reduce
certificate cost.

Design items 2 and 3 follow the machine targets. The packed-checker pilot
stays unchanged. Full frontend validation, environment audit, baseline
refresh, transitive replay and Linux qualification did not run.


### Full unsigned source-array composition obligation

The source composition rules now reuse a checked block at every occurrence.
`eager_array_family` preserves its exact byte order. The column-object rule
preserves the native object format. The decoder rules preserve every block
and its order. `parse_of_eager` gives the exact JSON parse result.

Focused checks passed for all three new modules. All 11 kernel controls pass.
They cover affine, dense and periodic blocks, negative stride, repeated array
entries and column objects. They reject a changed value and a missing comma.
All 23 new roots passed direct axiom checks. They use only the three allowed
axioms. The explicit inventory now contains 13,400 roots. All 13,377 previous
roots remain present. The bounded group used 293 MiB of physical memory and
left no owned process running. Resource limits stay unchanged.

The production sources and captures have not changed. The three source-table
certificates remain open. Generate their shared block libraries next. Design
items 2 and 3 follow the machine targets. The packed-checker pilot stays
unchanged. Full frontend validation, environment audit, baseline refresh,
transitive replay and Linux qualification did not run.


### Full unsigned number-token source obligation

`check_number_token` checks each distinct number spelling. Its soundness
theorem proves the exact value in every array and object context. The check
requires full token consumption and exact JSON number equality. Array and
object composition now use these facts. The shared block generator can reuse
number certificates inside different RLE objects.

Focused checks passed for the importer, source composition rules and their
users. All 18 retained setup-directory JSON differential checks still pass.
All ten new kernel controls pass. They cover signed numbers, exponents,
repeated values and duplicate-key order. They reject incomplete tokens,
trailing characters, wrong values and leading zeros.

All 29 new roots passed direct axiom checks. They use only the three allowed
axioms. The explicit inventory now contains 13,429 roots. All 13,400 previous
roots remain present. The bounded focused groups used at most 713 MiB of
physical memory. They left no owned process running. Resource limits stay
unchanged.

The separate parity library experiment also passed. It proves source and
decoder facts for all 283 distinct blocks. These blocks occur 107,052 times.
The experiment used 294 seconds and 1,819 MiB of physical memory. It remains
outside the branch. Number-token reuse now supplies a smaller composition
method for the larger source libraries. The three production source-table
certificates remain open. No target or existing premise changed.

Design items 2 and 3 follow the machine targets. The packed-checker pilot
stays unchanged. Full frontend validation, environment audit, baseline
refresh, transitive replay and Linux qualification did not run.


### Full unsigned shared source composition obligation

The string checker now has a kernel soundness theorem. One check supplies
both a JSON value and an object key. Shared source nodes compose numbers,
strings, booleans, null values, arrays and objects. Their proofs preserve
source order and the exact JSON result. The source generator can reuse these
proofs for each distinct node.

The string checker rejects characters that require JSON escapes. A runtime
scan found no such characters in the three retained split sources. The source
rules add no restriction to the target statements or to the setup parser.

Focused checks passed for the importer and source rules. The 18 retained
setup-directory JSON differential checks still pass. All 14 new kernel
controls pass. They cover empty strings, spaces, Unicode, keys, both Boolean
values, null values and mixed nodes. They reject quotes, backslashes and
control characters in the unescaped representation.

All 39 new roots passed direct axiom checks. They use only the three allowed
axioms. The explicit inventory now contains 13,468 roots. All 13,429 previous
roots remain present. The bounded focused groups used at most 749 MiB of
physical memory. They left no owned process running. Resource limits stay
unchanged.

The three production source-table certificates remain open. Generate their
shared source nodes and prove physical row matching next. Design items 2 and
3 follow the machine targets. The packed-checker pilot stays unchanged. Full
frontend validation, environment audit, baseline refresh, transitive replay
and Linux qualification did not run.


### Full unsigned captured-source parsing obligation

The shared table interpreter now proves source parsing for parity, theta/rho
and chi5. Its soundness theorem covers every table and depth. The theorem
uses the proved string and number checks. The object adapter supplies complete
source consumption. Equality proofs retain every byte and JSON value when
array and object children share their evaluation.

The generator retains all keys, values and field order from each source. Its
freshness check passes for all six generated modules. Exact byte comparisons
pass for all 11,980,612 retained source bytes. These comparisons are importer
checks. The kernel proves parsing for each represented source. Runtime code
does not supply a theorem proof. The full validation driver now requires both
generation freshness and exact byte identity.

The focused source group passed 21 checks. It includes all three data imports,
all three parser certificates, the interpreter, the proof generator and its
controls. Eleven new kernel controls pass. They cover field order, array
contents, negative numbers, Unicode, lookup branches, default entries, bounded
cycles and the zero-depth result. They reject an incorrect numeric value.

All 63 new roots passed direct axiom checks. They use only the three allowed
axioms. The explicit inventory now has 13,531 roots. It retains all 13,468
previous roots. The final combined group used 168 seconds and 879 MiB of
physical memory. The separate theta data import used at most 1,701 MiB.
All guards left no owned process running. Resource limits stay unchanged.

The three `FixedSetupRows` certificates remain open. The next step must decode
the retained columns and match every physical row to the original canonical
tables. Padding stays in the physical domain. No target statement or existing
premise changed. The packed-checker pilot stays unchanged.

Full frontend validation, environment audit, baseline refresh, transitive
replay and Linux qualification did not run.
