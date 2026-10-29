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
| Unrolled full unsigned | Open: program-parametric native setup, caller/worker and initialization composition, and functional soundness of the blessed split Keccak workers. Their compiled equations, fixed lookups, timestamp queries and public call schedule are imported; complete setup and worker effects are not proved. Special5 calls require an explicit public exclusion until their intended sequence is specified. |
| Unrolled reduced | Open: program-parametric native setup, BLAKE2 extended-round caller/worker composition, and stream-aware initialization. The four-family stream/caller relation, its pooled inclusion, and a public all-stream use contract are present; native soundness is not. |
| Unified | Open: program-parametric native setup, native soundness for the combined stream/modular/caller relation, and its initialization adapter. Special5 calls require an explicit public exclusion. |

These are required target scopes, not proved theorems. The corresponding Lean
`Prop` declarations and complete circuit acceptance interfaces are still being
designed. Exact lookup matching and state/RAM permutations remain explicit
logical assumptions in all three targets.

Both cached and uncached native captures remain required. The checker migration
must qualify all 22 capture configurations.

A direct one-line `decide +kernel` pilot for the shift/AND table exceeded the
bounded process memory limit after 12.79 seconds without a proof error. The
existing per-block certificate remains; a packed-data checker and a cold-build
cost baseline are still required before migration.

## Supporting proved results

| Area | Result and scope |
| --- | --- |
| [Ordinary circuits](Airbender/Review/Circuits/README.md) | Arithmetic, branches/jumps, comparisons, shifts/bitwise and word/subword memory have reference soundness proofs. Local public-image histories and native ROM-shadow histories are distinct interfaces. |
| [Whole execution](Airbender/Review/Trace/README.md) | Pooled and unified source/trace execution bind final PC and every tracked cell, including registers, for programs admitted by their selected registry. Branches and repeated-PC loops are supported. Discarded x0 writes missing from a registry remain outside it. |
| [Delegated workers](Airbender/Review/Trace/Workers/README.md) | Bigint, BLAKE2 and special5 Keccak compose under explicit call contracts. Complete algorithms require protocol coverage and valid memory gaps. Extended-round masks remain witness premises in lower-level integrated APIs as well as worker APIs. |
| [Supported delegation use](Airbender/Review/Trace/UnifiedReduced/SupportedUseExecution.lean) | Public wrapper shapes, safe entry and reference-prefix validity derive bigint/G/extended-round worker contracts. G pointer separation remains in the public domain; accepted complete G spans also derive separation from memory matching. Public initialization, tracked RAM, configuration, setup and exact matching remain explicit. |
| [Provided Keccak wrapper](FINDINGS.md#f12--blessed-keccak-path-is-outside-current-proof-coverage) | Uncovered. The blessed 361-call split order and control progression are checked; the three public CSR caller forms now have a separate Sail decoder registry and complete code-shape interface. All three compiled worker constraint/lookup cores are imported. Their complete setup, memory effects, all-stream supported-use condition and functional composition are still required for the full unsigned target. The modeled 649-call special5 protocol is separate. |
| [Initialization](Airbender/Review/Trace/Initialization.lean) | Native standalone/inline adapters derive seeds for ordinary pooled/unified execution. External-read, modular, TRIADD/XORROT and delegation extensions retain their own seed premises. |
| [Compiler preservation](Airbender/Review/Compiler/README.md) | Base-field arithmetic preservation covers 22 captures. Fourteen row compositions derive helper bounds, authored lookup membership and source validity from physical native arithmetic/active rows and exact emitted-tuple matching. Separate public-text row models have generic active-PC membership for ordinary instructions and full-width delegation-CSR caller rows, with captured masks and ROM capacity. Pure Sail decoding and the public text-image premise prove ordinary projected entry/program source for pooled and unified setups, plus each caller entry's actual bytes, decoded CSR shape and configuration allowlist. An effectful decoder result is not silently accepted. A generic initial-ROM lemma places each present public text word into the modeled word-ROM table. The caller projection also requires a public well-formed call-group premise to match native preprocessing. The compiler wrappers still require retained four-entry tables; the differential checks do not yet replace that premise. |

The unified base-layer verifier entrypoint currently discards the verified
outputs and returns the fixed eight-word success output beginning with one.
This implementation behavior is recorded without changing the production code.
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
| Public-text decoder row model | Focused guarded builds prove ordinary and caller-aware membership, table inclusion, 16-bit sentinel exclusion, pooled/unified ordinary and caller source, and generic public text-word ROM membership. The caller source records the exact CSR instruction shape and allowlist. The native model keeps the complete virtual CSR in the lookup query, rejects over-capacity text, keeps one row per padded word and applies the imported family mask. The pure-decoder tightening still matches native add/sub rows for a seven-call BLAKE2 example in full/reduced and unified configurations, both cache modes. Direct axiom smoke for the new pooled/unified membership, ordinary/caller source and text-ROM theorems reports only `propext`, `Classical.choice` and `Quot.sound`; split caller metadata uses `propext` alone. The complete environment audit remains pending. This does not yet replace the fixed decoder premise in compiler theorems. |
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
