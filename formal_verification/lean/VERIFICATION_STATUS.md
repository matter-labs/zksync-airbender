# Verification status

<!-- source-names: keccak_special5 -->

The model proves the public Unified and UnrolledReduced machine targets.
Both proofs include the native combined stream relation, public program binding
and initialization. The full unsigned target remains open. Exact lookup,
request and RAM matching remain explicit. The final full validation is pending.

## Production machine targets

| Setup machine | Current target status |
| --- | --- |
| Unrolled full unsigned | Open. The standalone initialization inputs and public ordinary, standard caller and split caller images are proved. The public decoder now classifies every native row across all six families and both caller registries. Connect the combined native path. Prove standard worker supported use, split worker functions and the complete blessed split sequence. The target excludes special5 calls. |
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
