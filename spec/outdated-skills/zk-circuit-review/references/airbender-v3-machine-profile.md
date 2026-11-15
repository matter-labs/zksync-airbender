# Airbender V3 GKR Machine Profile

This is a versioned specification snapshot for one repository state. It is not a timeless definition of Airbender and must not be applied to Boojum or any unrelated system.

## Contents

- Profile identity and applicability
- Fast applicability and delta check
- Machine profiles used by the proving flow
- Versioned semantic delta from RV32I
- Custom CSRRW carriers
- Custom Zimop carriers
- Initialization, output, and termination
- Known profile hazards
- Evidence map and maintenance rule

## Profile identity and applicability

| Field | Value |
|---|---|
| Profile ID | `airbender-v3-gkr-2026-08-11` |
| Repository | `matter-labs/zksync-airbender` |
| Verified commit | `0b8febeb44c2794c028372561bb0ed41bcb5fc56` |
| Observed branch | `av_gkr_compiler` (informational; branch names move) |
| Commit subject | `perf(gpu_gkr): add compiler-optimized evaluation pipeline (#376)` |
| Commit date | `2026-08-07T16:44:41+02:00` |
| Profile validation date | `2026-08-11` |
| Normative ISA baseline | [Normative RV32 Machine Baseline](riscv32-machine-baseline.md) |
| Circuit architecture | [Airbender V3 GKR Circuit Architecture](airbender-v3-circuit-architecture.md) |

Use this profile as verified fact only for the exact commit above. For a dirty worktree, another commit, or a copied subset, run the delta check below and label the result `matched`, `changed`, `absent`, or `not checked` in the specification dossier.

- Same repository and matching fingerprints: use this document as the prior specification, with changed items overridden by current evidence.
- Older/newer Airbender without matching fingerprints: use it only as a search checklist. Build a new versioned delta before confirming a finding.
- Non-RISC-V repository or a different architecture such as Boojum: do not load this document or the RV32 baseline.

## Fast applicability and delta check

Do not repeat the original repository-wide research. Identify the revision, then verify these high-information symbols and their active call sites:

1. `git remote -v`, `git rev-parse HEAD`, and `git status --short` identify provenance and local changes.
2. `DecodingOptions`, `FullUnsignedMachineDecoderConfig`, and `ReducedMachineDecoderConfig` define feature flags in `riscv_transpiler/src/ir/mod.rs`.
3. `IMStandardIsaConfigUnsignedMulDivOnly` and `ReducedMachineWithDelegation` define allowed delegation sets in `riscv_transpiler/src/cycle/mod.rs`.
4. The actual CLI/prover entrypoint selects those profiles. On the verified commit, inspect `tools/cli/src/prover_utils.rs` and `gpu/execution_prover/src/precomputations/unrolled.rs`.
5. `preprocess_bytecode` and `process_binary_into_separate_tables_ext` select the same decoder options used by the constraint setup.
6. `NON_DETERMINISM_CSR`, delegation CSR constants, `ROM_BYTE_SIZE`, `INITIAL_PC`, `INITIAL_TIMESTAMP`, and `TIMESTAMP_STEP` retain the values documented below.
7. `riscv_common::EXIT_SEQUENCE`, setup construction, and the full-statement verifier still bind the claimed program and final PC as documented below.

If any of checks 2–7 changes or cannot be connected to the named circuit's proving entrypoint, mark this profile `changed` or `not checked`; investigate that delta before treating the affected rule as intended behavior. An exact commit hash does not cover uncommitted changes.

## Machine profiles used by the proving flow

The verified primary recursion flow is not one uniform ISA:

| Layer/path | Decoder/profile | Supported differences relevant to circuit review |
|---|---|---|
| Base user program | `IMStandardIsaConfigUnsignedMulDivOnly` / `FullUnsignedMachineDecoderConfig` | RV32I word and subword memory; M subset `MUL`, `MULHU`, `DIVU`, `REMU`; MOP field operations; four delegation CSRs. Preprocessing also emits a special MOP-I rotate, but its current unrolled circuit reachability is unresolved as described below. |
| Unrolled recursive verifier | `ReducedMachineWithDelegation` / `ReducedMachineDecoderConfig` | no M; no subword memory; word memory; MOP field operations; Blake-specific tri-add/XOR-rotate preprocessing; Blake full/G delegations only |
| Unified recursive verifier | reduced unified circuit | reduced profile plus circuit support for `ZimopTriAdd` and `ZimopIXorRot` |

`IMStandardIsaConfig` and `FullMachineDecoderConfig` also exist and advertise signed M operations. They are not the primary CLI recursion path at this snapshot. Treat their support as unverified for a named production path until setup generation is traced end to end.

## Versioned semantic delta from RV32I

### Unsupported system and instruction behavior

There is no privileged machine, architectural trap handler, or general CSR state. `FENCE`, `FENCE.I`, `ECALL`, `EBREAK`, privileged operations, compressed instructions, and arbitrary CSRs are not part of this profile.

The failure mode is not uniform:

- some unknown encodings preprocess to `Illegal`;
- profile-disabled known operations preprocess to `Illegal`;
- several malformed SYSTEM/CSR/MOP forms panic during preprocessing;
- decoder tables may omit unsupported PCs when setup permits unsupported bytecode, making execution of that row unprovable.

Therefore, do not claim that every unsupported instruction is accepted in fixed bytecode or that every unsupported instruction traps identically. Trace the exact encoding through preprocessing and the active decoder table.

### `rd = x0` preprocessing

`Instruction::pure_from_imm` rewrites pure result instructions with `rd = x0` to the project NOP. This includes loads, deliberately suppressing the access and any alignment failure—a divergence from standard RISC-V. Side-effecting control-flow and custom CSR carriers use other constructors and retain their effects. Stores are not subject to the destination rewrite.

### Alignment and memory policy

- Instructions are 32-bit and instruction addresses are four-byte aligned; compressed instructions are absent.
- Memory is byte-addressed and little-endian.
- Word accesses must be four-byte aligned; halfword accesses must be even; byte accesses may use any byte address.
- `JALR` clears bit zero as RV32I requires, then this machine requires four-byte instruction alignment.
- The fixed ROM region is the low `2^22` bytes (4 MiB). ROM values are authenticated through preprocessed bytecode/ROM lookup data, and stores to ROM are unprovable.
- The supported mutable RAM bound is a proving/runtime parameter. Current primary CLI/GPU flows commonly use or require at most `2^30` bytes; verify the active call rather than treating 1 GiB as an ISA constant.
- Addresses remain 32-bit even when the initialized/supported memory range is smaller.

### M profiles

The verified base path uses unsigned-only M setup: `MUL`, `MULHU`, `DIVU`, and `REMU`. The reduced recursion profiles omit M. Do not infer `MULH`, `MULHSU`, `DIV`, or `REM` support from enum variants or the presence of signed circuit code.

### Custom rotation profiles

Ordinary RISC-V `ROL`/`ROR` encodings are explicitly rejected by preprocessing. In the full-unsigned profile, selected MOP-I encodings instead produce `Ror` with an immediate rotation, but the standalone shift/binary decoder does not accept `Ror` at this commit; treat intended production support as unresolved. In the reduced profile the same carrier class produces `ZimopIXorRot`; the unified circuit accepts only rotations `16`, `12`, `8`, and `7`.

## Custom CSRRW carriers

These encodings are VM carriers, not architectural CSR state. Only `CSRRW` form is accepted.

| CSR | Accepted form and semantics | Availability at verified commit |
|---|---|---|
| `0x7c0` | `rs1=x0, rd!=x0`: prover-supplied 32-bit nondeterministic read. `rs1!=x0, rd=x0`: host-side nondeterminism write; the circuit intentionally models the instruction as an ADD/NOP-shaped row and does not bind the written value. | all listed profiles |
| `0x7c7` | repeated `csrrw x0, csr, x0` carrier for Blake2s full/round delegation; preprocessing accepts runs of 7 or 10 calls | base and reduced-with-delegation |
| `0x7c8` | Blake2s G-function delegation; preprocessing accepts 7×8 or 10×8 repeated calls | base and reduced-with-delegation |
| `0x7ca` | bigint-with-control delegation, issued one at a time | base full-unsigned only |
| `0x7cb` | Keccak special delegation, requiring exactly 649 repeated calls | base full-unsigned only |
| `0x7ff` | development-only transpiler marker | rejected by the proving path; not production ISA |

Delegation instructions emit invocation traffic for a separate fulfillment circuit. Audit the local producer tuple and the fulfillment circuit separately; assuming the global bus is a sound permutation does not validate an incorrect type, identifier, timestamp, or payload.

Nondeterministic reads are unconstrained inputs by design. Integrity must be established by guest computation or later proof-statement binding. A nondeterminism write is observable to the host/simulator but is not, by itself, a proved public output.

## Custom Zimop carriers

MOP numbers at this snapshot are add `0`, sub `1`, multiply `2`, fused multiply-add `3`, and tri-add `4`.

- `ZimopAdd`, `ZimopSub`, and `ZimopMul` interpret the two register words as the circuit field's **raw representation**, reduce each raw word if needed, perform the field operation, and write the reduced raw representation.
- `ZimopFMA` computes `rd_old + rs1 * rs2` in that same field/raw representation and overwrites `rd`.
- The current GKR proving circuits use BabyBear (`p = 0x78000001`) whose stored raw representation is Montgomery. This representation fact is part of this profile, not of generic Zimop or RISC-V.
- `ZimopTriAdd` computes `rd_old + rs1 + rs2` modulo `2^32`; it is emitted by the reduced profile and enforced only by the unified reduced circuit in the verified primary path.
- `ZimopIXorRot` computes `(rs1 XOR rd_old) ror imm`, with the old `rd` routed as the second source; the unified reduced circuit accepts only `16`, `12`, `8`, and `7`.
- Full-profile MOP-I `Ror` computes a rotate-right carrier without XOR. Verify its unrolled decoder/circuit reachability for the named proving path before claiming support.

All pure MOP results with `rd=x0` are rewritten to NOP during preprocessing.

## Initialization, output, and termination

- Initial PC is `0`; initial timestamp is `4`; a normal cycle advances the global timestamp by `4`.
- The global state argument supplies register initialization/finalization and PC/timestamp continuity. Do not assume every register starts at zero without tracing the initialization statement and program convention.
- Successful program binaries contain exactly one authenticated `riscv_common::EXIT_SEQUENCE`: sixteen loads into `a0..a7` and `s2..s9`, followed by `jal x0, 0`.
- The execution engine treats that self-loop as the end of execution. The verifier derives the expected exit PC from the unique sequence and hashes final PC plus program-specific setup commitments into `end_params`.
- The full-statement verifier carries final registers `x10..x17` as eight output words. At the base layer it requires `x18..x25` to be zero and starts the recursion-chain binding; later layers use those registers for the authenticated recursion chain.
- Program success is therefore not a generic RISC-V halt. It depends on the exact final-PC/program/setup binding and recursion statement. Audit the relevant verifier layer whenever the target can influence output or termination.

## Known profile hazards

These are specification/reachability checks, not confirmed circuit findings:

- The GPU unrolled setup builder maps both `MachineType::Full` and `MachineType::FullUnsigned` to full-unsigned decoder data and unsigned M circuits, even though binary preprocessing distinguishes them. Do not claim production signed-M support without resolving this path.
- `DebugReducedMachineDecoderConfig` enables both special rotation modes even though MOP-I preprocessing asserts they are not simultaneously enabled. It is a development profile, not a stable production contract.
- Reduced preprocessing can emit tri-add and XOR-rotate, but the standalone unrolled family decoders do not accept them; the unified reduced decoder does. Resolve the exact execution kind before judging completeness.
- The historical Soundcalc Airbender report concerns older proof-system/security parameters and does not establish this machine profile.

## Evidence map and maintenance rule

Primary evidence for this snapshot:

- profile flags and preprocessing: `riscv_transpiler/src/ir/mod.rs`, `riscv_transpiler/src/ir/simple_instruction_set.rs`;
- active machine/delegation configs: `riscv_transpiler/src/cycle/mod.rs`;
- VM semantics: `riscv_transpiler/src/vm/mod.rs` and `riscv_transpiler/src/vm/instructions/`;
- constants and exit convention: `common_constants/src/`, `riscv_common/src/lib.rs`;
- circuit decode and operation support: `cs/src/gkr_circuits/*/decoder.rs` and `cs/src/gkr_circuits/unified_reduced_machine/`;
- current proving selection: `tools/cli/src/prover_utils.rs`, `gpu/execution_prover/src/prover/binary.rs`, and `gpu/execution_prover/src/precomputations/unrolled.rs`;
- final statement: `circuit_defs/setups/src/program_setups.rs`, `full_statement_verifier/src/unrolled_proof_statement.rs`, and `full_statement_verifier/src/unified_circuit_statement.rs`.

When the repository changes, do not edit this snapshot into a timeless document. Copy it to a new profile ID, update the fingerprint/date/evidence, record semantic deltas, and route the skill to the new profile. Preserve old profiles when they remain useful for auditing old releases or branches.
