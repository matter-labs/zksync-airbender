# Airbender Verifier Architecture Profile

## Contents

1. Applicability and version split
2. Current GKR verifier stack
3. Current transcript/proof flow
4. Full-statement composition
5. Historical STARK stack
6. EVM/L1 settlement path
7. Repository investigation procedure
8. Airbender-specific risk register

## 1. Applicability and version split

This is a search profile, not a timeless specification. Confirm paths and symbols against the requested commit.

The current GKR-era tree commonly contains:

- `verifier_common/`: shared native verifier types, parsing helpers, generated-verifier interface, GKR/WHIR utilities, proof flattening;
- `verifier_generator/`: code generation for per-circuit GKR and WHIR verification;
- `full_statement_verifier/`: aggregation across circuit families, chunks, delegation proofs, recursion layers, and final public outputs;
- `transcript/`: Blake2s/Keccak transcript and PoW implementation;
- `tools/gkr_verifier/`: concrete verifier binaries/wrappers;
- generated verifier crates or artifacts selected by features/configuration;
- `prover/`, `cs/`, and circuit artifacts as protocol/specification references.

Historical tagged versions commonly contain:

- `verifier/src/skeleton.rs` and generated/concrete verifier modules;
- `verifier_common/src/fri_folding.rs`, proof structures, and flatteners;
- `verifier_generator/` quotient/inlining generation;
- `prover/src/prover_stages/stage1.rs` through `stage5.rs`;
- `transcript/` and `full_statement_verifier/`.

Do not decide GKR versus STARK from a release number alone. Resolve the files and entrypoint in the target tag.

## 2. Current GKR verifier stack

The broad native flow is:

```text
full-statement wrapper
  -> read externally shared permutation/delegation challenges
  -> call concrete per-circuit verifier
      -> make initial transcript from top bits, external challenges, setup/memory/witness caps
      -> verify lookup-challenge PoW and draw lookup challenges
      -> verify dimension-reducing GKR layers
      -> verify standard GKR layers
      -> verify output lookup/memory identities
      -> verify PCS-batching PoW and draw WHIR batching challenge
      -> verify WHIR openings of base-layer claims
      -> return memory products, setup/memory caps, and init/teardown products
  -> aggregate all per-proof outputs
  -> reconstruct shared external challenges from the full memory-cap transcript
  -> inject verifier-owned initial/final machine-state contributions
  -> compare global read/write products
  -> hash/emit final recursive statement
```

Verify this shape against actual source. Current code uses compile-time counts and generated code extensively; a mismatched instantiation can alter the proof layout without an obvious parser function.

## 3. Current transcript/proof flow

### Per-circuit initial transcript

An `InitialGKRTranscript`-like structure may contain:

- initialization/teardown top bits;
- flattened external challenges;
- setup caps;
- memory caps;
- witness caps;
- structural zero padding for aligned hashing.

The meaningful prefix, not arbitrary Rust padding, must be hashed. Check struct representation, offsets, alignment assertions, count bounds, and that prover and verifier hash the same word order. A cap may be absent only for a zero-column class supported coherently by generated constants and WHIR.

### GKR proof stream

A typical flattened order is:

1. top bits and initial caps;
2. lookup-challenge PoW nonce;
3. early final explicit output-pair evaluations;
4. dimension-reducing layer Sumcheck polynomials and final evaluations;
5. standard layer Sumcheck polynomials, at-point evaluations, and cached extras;
6. batched-proximity/WHIR PoW nonce;
7. WHIR rounds: Sumcheck polynomials, intermediate caps, OOD samples, round PoW nonces, and query data;
8. terminal monomials and final queries.

Treat this only as a checklist. Derive exact order from the target's flattener and generated verifier.

### Output families and tuple randomization

At the inspected GKR snapshot, `OutputType` distinguishes one global permutation-product pair, three lookup/LogUp pair classes (`Lookup16Bits`, `LookupTimestamps`, and `GenericLookup`), and an optional initialization/teardown product pair. The prover exposes small explicit polynomials for these pairs; GKR binds them to the base computation, after which the verifier multiplies permutation entries and directly checks each rational lookup identity. Confirm which output types are present in each compiled circuit rather than assuming all five.

The inspected memory/delegation tuple key has six nonconstant parts (address low/high, timestamp low/high, and value low/high), randomized by six **independently drawn** extension-field linearization challenges plus one additive challenge. Some historical symbol names say “challenge powers”; do not infer that the implementation uses powers of one alpha. Compare every independent challenge and its field position across all circuits, machine-state injections, and delegation encoders.

### Shared external challenges

Memory/delegation challenges can be supplied to each per-circuit verifier before the whole-program verifier has finished rebuilding them. Soundness then depends on the outer verifier:

- committing every relevant per-proof memory cap and metadata into one transcript;
- drawing/verifying the external challenges only after all contributors are fixed;
- comparing the rebuilt tuple with the exact tuple used by every inner proof;
- preventing one proof class from using a partial or different tuple;
- accounting for PoW/grinding and the total permutation-element bound.

This deferred-equality pattern is valid only if no adversarial freedom escapes the final comparison.

## 4. Full-statement composition

### Circuit families and chunks

Execution can span many fixed power-of-two chunks. The wrapper reads counts and iterates circuit families. Audit:

- count bounds and integer overflow;
- mandatory/nonempty circuit classes;
- fixed family order and type tags;
- per-family trace length used to accumulate total cycles;
- setup cap equality for every instance;
- inclusion of every instance's memory read/write product;
- initialization/teardown coverage and top-bit ordering;
- delegation/precompile proof counts and type-specific setup caps;
- neutral accumulator behavior for zero contributors;
- transcript framing between variable numbers of proofs.

At the inspected branch, the unrolled full-statement verifier increments `total_cycles` by a hard-coded `1 << 24` per main proof and marks it `TODO`. Treat any such fixed trace-size assumption as a target-specific obligation: prove it matches every selected family/setup or derive the size from authenticated configuration.

### Cycle/timestamp bound

Do not assume a remembered `2^32` limit. In the current profile, `MAX_CYCLES` is derived from timestamp representation:

```text
2^(TIMESTAMP_COLUMNS_NUM_BITS * NUM_TIMESTAMP_COLUMNS_FOR_RAM)
  >> NUM_EMPTY_BITS_FOR_RAM_TIMESTAMP
```

At the inspected snapshot, the constants were two 19-bit timestamp columns and two empty low bits, yielding `2^36` possible cycle slots before additional strict-bound details. Re-read the constants in the target version and distinguish maximum representable timestamp, maximum initial timestamp, strict `< MAX_CYCLES` checks, and the initial offset.

### Machine-state closure

The global memory/permutation equality may carry registers, PC, timestamp, ordinary memory, and delegation traffic. The outer verifier commonly injects an initial machine-state read and final-state write using externally parsed final values. Audit:

- register zero and every public final register value;
- initial PC/timestamp constants;
- final PC/timestamp range and encoding;
- timestamp step and limb split;
- address-space/type tags distinguishing machine state, memory, and delegation;
- which side of the global argument receives each injected contribution;
- public-output hash/preimage checks;
- no missing or double-counted machine-state tuple.

### Setup and recursion

Setup caps may commit to program binaries and fixed tables. Some recursion proof classes may be setup-independent while the wrapper propagates a commitment to the set of setup keys for final comparison. Audit exactly what is compared now versus merely returned for a later layer.

Check recursion dispatch tags, security-level dispatch, base versus recursion setup sets, unified versus unrolled proof paths, combination of several inner recursion proofs, and final output framing.

## 5. Historical STARK stack

In historical tags, use the staged prover only after deriving the verifier schedule. A representative mapping is:

- stage 1: witness/memory LDEs and caps;
- stage 2: lookup/memory challenges, auxiliary columns, and their commitments;
- stage 3: quotient batching challenges and quotient construction/commitment;
- stage 4: OOD point/evaluations, DEEP batching, and initial FRI oracle;
- stage 5: FRI commitments/folding, terminal polynomial, PoW, and queries.

Confirm every stage transition in the verifier. Historical code may have separate concrete/generated skeletons, row-domain-specific quotient evaluators, several cosets, and caps optimized around fold-by-eight schedules.

## 6. EVM/L1 settlement path

The on-chain verifier is a separate implementation and deployment boundary,
not merely another Rust wrapper. Current work may generate Solidity/Yul from a
selected GKR circuit artifact and WHIR schedule, flatten the proof into custom
calldata, and split GKR from WHIR verification across contracts/transactions.
Reconstruct the actual deployed design from `verifier_evm/`, generated sources,
compiler settings, runtime bytecode, registry/helper contracts, and the L1
state-transition caller.

Determine whether L1 verifies a base execution chunk, one unified recursive
verifier-program chunk, or a final proof that represents a deeper recursion
chain. A single outer chunk can close its memory argument locally only if all
outer computation and verifier-injected initial/final machine-state tuples are
present. Global closure of the original many-chunk execution must already be
proved by the authenticated recursive verifier program.

If GKR and WHIR are verified separately, treat their handoff digest and
persistent registry as part of the proof protocol. Both marks must be produced
by authenticated verifier code, bind the complete same PCS state and public
statement, resist replay/overwrite/reordering, and be consumed by one final
settlement rule. Check every low-level call success bit.

The L1 endpoint must authenticate the outer verifier program/setup and success
PC, then check the expected recursive-chain terminus and base program output.
It need not replay every recursion link if the proved verifier program soundly
enforces the induction, but it cannot accept an arbitrary chain digest or an
arbitrary verifier setup supplied by the caller. Use `evm-l1-verifier.md`.

## 7. Repository investigation procedure

1. Resolve public verifier entrypoint and call sites.
2. Record commit, branch/tag, Cargo features, target architecture, and security mode.
3. List relevant files before reading; generated files may be large.
4. Locate proof reads, transcript commits/draws, asserts/errors, and verifier outputs.
5. Trace concrete verifier trait implementations to the generator and circuit artifact.
6. Locate proof flattener/serializer and compare read order mechanically or by a ledger.
7. Trace full-statement aggregation and recursion wrappers.
8. Read prover phases only to resolve intended messages and mismatches.
9. Inspect scoped history for relevant verifier fixes; preflight changed paths before diffs.
10. Recompute constants from the active source rather than copying this profile.

For an EVM target, additionally pin the exact compiler binary/settings, emitted
runtime bytecode, deployed address/code hash, helper/registry authorization,
proxy/upgrade state, and settlement entrypoint.

## 8. Airbender-specific risk register

- omitted top bits or memory caps from shared external-challenge derivation;
- external challenge tuple only partially compared across circuit classes;
- setup cap checked for some instances but not all;
- stale generated verifier after circuit/layout change;
- cached or virtual polynomial evaluation used but not checked;
- cached evaluations absorbed after the batching challenge;
- mismatch between proof flatten order and generated address order;
- LSB/MSB sumcheck migration affecting only part of the stack;
- final-round optimization changing coefficient/evaluation count asymmetrically;
- empty zero-column oracle skipping transcript or query offsets incorrectly;
- reduced hash-round or security-level feature skew;
- a `sec_100`-named wrapper/binary linked to an `security_80` outer full-statement verifier or memory-grinding constant;
- PoW nonce placement/draw-word skip mismatch;
- total permutation-element bound inconsistent with security derivation;
- delegation type, setup, or address-space mismatch;
- padding chunk contributing unauthorized global memory/state tuples;
- missing initialization/teardown chunk or invalid top-bit partition;
- total-cycle overflow or incorrect timestamp-limb range;
- unified/unrolled/recursion dispatch accepting the wrong proof class;
- setup commitment propagated but never anchored by a final verifier;
- public final register/PC/state parsed but not bound to memory closure/output hash.
- final recursive proof accepted without checking the expected recursion-chain
  terminus or the authenticated outer verifier program/setup;
- one-outer-chunk assumption used to localize memory without proving all outer
  computation and machine-state injections fit that chunk;
- GKR/WHIR split joined through an incomplete or unauthenticated handoff;
- registry marks callable by the wrong sender, overwriteable, replayable, or
  accepted after only one verifier half;
- ignored low-level-call success or malformed/unchecked return data;
- custom calldata truncation, dirty high bits, or mixed-endian mismatch;
- Yul memory/spill overlap or an invalid `memory-safe` annotation under the
  deployed compiler pipeline;
- generated Solidity or runtime bytecode drifting from the selected circuit,
  setup, WHIR schedule, PoW/security parameters, or final-PC constant;
- settlement consumes an event/debug return/registry field whose provenance is
  not the cryptographically verified public output.
