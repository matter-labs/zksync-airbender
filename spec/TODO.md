# Specification TODO

> Actionable migration work that has not yet acquired a canonical specification
> owner. Move each item into its named module when that module is completed, then
> remove the item from this file.

## Tables

- [ ] Add one definition under `tables/` for every supported fixed semantic table,
  specifying its stable identifier, ordered key/value row schema, and complete row
  generator; include ZeroEntry, TruncateShiftAmountAndRangeCheck8,
  GetSignExtensionByte, ShiftImplementationOverBytes, WideXor, WideOr, WideAnd,
  XorRotate16, XorRotate12, XorRotate8, XorRotate7, RegIsZero, U16GetSign,
  ConditionalJmpBranchSlt, ConditionalJmpBranchSltUnified, JumpCleanupOffset,
  U16GetLowByte, RangeCheck8x8, RangeCheck9x9, RangeCheck10x10, RangeCheck11,
  RangeCheck12, RangeCheck13, StoreByteSourceContribution,
  StoreByteExistingContribution, LoadHalfwordSignextend, LoadByteSignextend, Xor,
  And, Or, Xor3, Xor4, Xor7, Xor9, BlakeGFunctionControlLookup,
  KeccakPermutationIndices, XorSpecialIota, AndN, and RotL.
- [ ] Add program-derived decoder and ROM-table construction to their execution and
  memory owners; require those generated rows to use `tables/encoding.md` without
  treating program-derived tables as fixed semantic tables.
- [ ] Add a validation check that every table selected by a circuit has one table
  definition, that selected table identifiers are unique, and that the encoded setup
  fits the circuit's declared setup length.

## Lookup instances

- [ ] Add decoder lookup admission to `execution/decoder.md`, preserving
  REQ-LOOKUP-003: an executed row queries
  `[pc_lo, pc_hi, rs1, rs2, rd, imm_lo, imm_hi, funct3?, family_mask?]` with exactly
  the optional columns selected by the family, matches the preprocessed row at
  `pc / 4`, uses `-1` for unsupported entries, and contributes coefficient zero when
  `execute = 0`.
- [ ] Add the compiled lookup-instance input to each circuit specification, preserving
  IN-LOOKUP-001: fix the trace length, selected table inventory, query relations,
  output map, and maximum fraction count as part of the compiled artifact.
- [ ] Add each concrete query schema to its producing circuit, preserving
  IN-LOOKUP-003: specify the selected table class, exact payload columns, byte-pair
  routing, and decoder activation coefficient.
- [ ] Add the lookup output map to every compiled circuit, preserving
  REQ-LOOKUP-INT-001: expose exactly one numerator/denominator pair for every present
  class and expose no pair for an absent class.
- [ ] Add concrete setup binding to every compiled circuit and its verifier consumer,
  preserving REQ-LOOKUP-INT-002: distinguish committed setup columns from
  verifier-derived range tables and bind both to the same declared table instance.
- [ ] Add the lookup GKR reduction to the circuit-output and FSV specifications,
  preserving REQ-LOOKUP-INT-003: prove that pair gates and each dimension reduction
  preserve the rational sum, including the implemented `s = 4` reduction and its 16
  terminal pairs.

### Unrolled executor

- [ ] Add the per-family unrolled lookup model to `execution/unrolled.md`, preserving
  ASM-LOOKUP-UNR-001..002 and REQ-LOOKUP-UNR-001..003: use an independent lookup
  instance and decoder table per family, admit a PC in at most one family, and expose
  only the GenericLookup, Lookup16Bits, and LookupTimestamps pairs present for that
  family.
- [ ] Add this exact unrolled lookup inventory to the corresponding circuit modules
  and preserve OUT-LOOKUP-UNR-001:

  | Circuit | Fixed or derived tables | Generic queries | Width | ID column | 16-bit queries | Timestamp queries |
  |---|---|---:|---:|---|---:|---:|
  | AddSubLuiAuipcMopCircuit | none | 1 | 8 | no | 6 | 8 |
  | JumpBranchSltCircuit | RegIsZero, U16GetSign, ConditionalJmpBranchSlt, JumpCleanupOffset | 5 | 10 | yes | 4 | 8 |
  | ShiftBinaryCircuit | ZeroEntry, TruncateShiftAmountAndRangeCheck8, GetSignExtensionByte, ShiftImplementationOverBytes, Xor, And, Or | 6 | 10 | yes | 2 | 8 |
  | UnsignedMulDivCircuit | U16GetLowByte, RegIsZero, RangeCheck8x8, RangeCheck13 | 9 | 9 | yes | 8 | 8 |
  | LoadStoreWordOnlyCircuit | ZeroEntry and program-derived AlignedRomRead | 2 | 9 | yes | 3 | 8 |
  | LoadStoreSubwordOnlyCircuit | ZeroEntry, StoreByteSourceContribution, StoreByteExistingContribution, LoadHalfwordSignextend, LoadByteSignextend, and program-derived LoadHalfwordRomRead and LoadByteRomRead | 3 | 9 | yes | 5 | 8 |
  | initialization and teardown | none | 0 | — | no | 0 | 0 |

- [ ] Add the unrolled timestamp-query derivation to the memory-access circuit
  modules: account for two cycle-end timestamp limbs and two limbs for every RAM
  access in each of the three RAM access sets, yielding eight timestamp queries where
  the inventory above says eight.

### Unified executor

- [ ] Add the pooled unified lookup model to `execution/unified.md`, preserving
  ASM-LOOKUP-UNI-001..002 and REQ-LOOKUP-UNI-001..004: use one lookup instance and one
  unified decoder table carrying a 19-bit family mask. Define bits `0..10` for F1,
  `10..15` for F2, `15..17` for F3, and `17..19` for F4. Require the 18 opcode-dispatch
  bits to be one-hot on an executed row; the F2 `rd_is_zero` bit is auxiliary and is
  excluded from that sum. Require padding rows to set all 19 mask bits to zero, gate
  execution by the selected dispatch bit, and make inactive bodies neutral.
- [ ] Add the unified inventory to its circuit module and preserve
  OUT-LOOKUP-UNI-001: width 10, six generic queries, thirteen 16-bit queries, eight
  timestamp queries, and the fixed tables ZeroEntry,
  TruncateShiftAmountAndRangeCheck8, GetSignExtensionByte,
  ShiftImplementationOverBytes, WideXor, WideOr, WideAnd, XorRotate16, XorRotate12,
  XorRotate8, XorRotate7, RegIsZero, U16GetSign,
  ConditionalJmpBranchSltUnified, and JumpCleanupOffset, plus program-derived
  AlignedRomRead.
- [ ] Add the unified initialization/teardown rule to `memory/init-teardown-unified.md`:
  folded initialization and teardown rows issue no lookup queries.

### Delegation circuits

- [ ] Add the delegation lookup model to the precompile fulfillment-circuit modules,
  preserving ASM-LOOKUP-DEL-001, REQ-LOOKUP-DEL-001..003, and
  OUT-LOOKUP-DEL-001.
- [ ] Add this exact delegation lookup inventory to the corresponding fulfillment
  circuits:

  | Circuit | Rows | Fixed tables | Generic queries | Width | ID column | 16-bit queries | Timestamp queries | Table rows |
  |---|---:|---|---:|---:|---|---:|---:|---:|
  | BLAKE2s G | `2^22` | Xor, Xor3, Xor4, Xor7, Xor9, BlakeGFunctionControlLookup | 19 | 9 | yes | 0 | 20 | 344896 |
  | BLAKE2s round | `2^20` | Xor, Xor3, Xor4, Xor7, Xor9 | 208 | 4 | yes | 0 | 88 | 344384 |
  | bigint | `2^22` | RangeCheck9x9, RangeCheck10x10, RangeCheck11, RangeCheck12, RangeCheck13, U16GetLowByte | 61 | 3 | yes | 32 | 40 | 1390592 |
  | Keccak special5 | `2^22` | ZeroEntry, Xor, KeccakPermutationIndices, XorSpecialIota, AndN, RotL | 41 | 8 | yes | 0 | 30 | 1249281 |

### Lookup soundness and validation

- [ ] Add each circuit's maximum fraction and query count to its circuit module and
  enforce the characteristic margin required by REQ-LOOKUP-SND-001, preserving the
  work formerly tracked as GAP-LOOKUP-SND-002.
- [ ] Add every lookup invocation's concrete collision and reduction error to
  `soundness/error-budget.md`, including the lookup term formerly tracked as
  GAP-LOOKUP-002 and GAP-LOOKUP-SND-004.
- [ ] Add the concrete GKR-to-WHIR lookup opening edges and terminal-zero checks to the
  FSV proof inventory, preserving the topology work formerly tracked as
  GAP-LOOKUP-001 and GAP-LOOKUP-SND-003.
- [ ] Update all consumers to import the standalone lookup and table requirements,
  remove references to displaced circuit-specific lookup IDs, and run the complete
  spec validator.

## Event encoding and global-product instances

- [ ] Add `execution/event-encoding.md` with the shared event schema: assign tags
  Register = 0, RAM = 1, and PC = 2; encode address as two 16-bit limbs, timestamp as
  two 19-bit limbs, and value as two 16-bit limbs; require low-limb-first
  recomposition, additive tag placement, inactive-row factor one, and read/write
  orientation by product side.
- [ ] Add the common fingerprint challenge to `execution/event-encoding.md` as seven
  extension-field elements
  `[alpha_a0, alpha_a1, alpha_t0, alpha_t1, alpha_v0, alpha_v1, beta]` and define the
  tuple-compression formula
  `beta + tag + alpha_a0 a_0 + alpha_a1 a_1 + alpha_t0 t_0 + alpha_t1 t_1 + alpha_v0 v_0 + alpha_v1 v_1`
  imported by each event producer; require omitted coordinates to contribute zero.
- [ ] Add the delegation event namespace to its precompile carrier: reuse tag zero and
  use the delegation type as the address while preserving the common tuple schema.
- [ ] Add register-event rows, read/write orientation, and ordering to
  `memory/registers.md`.
- [ ] Add RAM and ROM-shaped event rows, read/write orientation, and ordering to
  `memory/common.md`.
- [ ] Add PC and machine-state event rows, read/write orientation, and ordering to
  `execution/common.md`.
- [ ] Add delegation invocation and fulfillment mirror factors and closure to the
  precompile carrier specification.
- [ ] Add initialization and finalization events to the two memory-boundary modules,
  including the separate unrolled proof and folded unified packaging.
- [ ] Add each circuit's local read and write products to its GKR output layout,
  including the second initialization/teardown pair where present and the identity
  value where absent.
- [ ] Add per-class history-chain closure to the register, memory, execution, and
  delegation modules that own the relevant ordering, preserving the substance of
  OUT-GP-REL-002.
- [ ] Add sorted memory-log framing over `(address, timestamp, operation, value)` and
  initial/final scans to the memory modules; cite [Thaler, Section
  6.6.2](https://people.cs.georgetown.edu/jthaler/ProofsArgsAndZK.pdf) for this framing.
- [ ] Add the permutation and local-consistency lineage for the memory argument using
  address, value, and version; cite [Two Shuffles Make a
  RAM](https://eprint.iacr.org/2023/1115) only for those roles.

### Full-statement verifier integration

- [ ] Add full-statement product accumulation to the FSV, preserving
  ASM-GP-REL-002 and REQ-GP-INT-001: sample one fingerprint challenge after the
  bound statement and reuse it for every participating product.
- [ ] Add proof and output-pair inventory to the FSV, preserving the concrete parts of
  ASM-GP-VER-002 and REQ-GP-VER-001 and rejecting a missing, extra, duplicated, or
  reordered pair.
- [ ] Add setup-cap and proof-cap continuity checks to the FSV, preserving
  REQ-GP-VER-002 and REJ-GP-VER-001.
- [ ] Add product challenge recomputation and its proof-of-work position to the FSV,
  preserving the concrete portion of REQ-GP-VER-003.
- [ ] Add boundary insertion to the FSV, preserving REQ-GP-REL-003 and
  REQ-GP-VER-004: form the write boundary from register values at timestamp zero plus
  initial PC/state, and form the read boundary from final register values with their
  final read timestamps plus final PC/state.
- [ ] Add executor invocation products and fulfillment products to the same FSV
  accumulation, preserving REQ-GP-INT-002, and bind the carrier selected by the
  precompile profile.
- [ ] Add the initialization/teardown contribution selected by each memory profile to
  the FSV accumulation, preserving REQ-GP-INT-003.
- [ ] Export delegation closure, machine-state closure, initialization/teardown
  inclusion, and register/RAM closure from their owning modules and consume them in
  the FSV, preserving OUT-GP-INT-001..004.
- [ ] Add final timestamp-limb validation to the FSV and retain the confirmed drift as
  DEV-FSV-STR-002 until the implementation conforms or the intended relation changes.

### Product soundness

- [ ] Split the work formerly tracked as GAP-GP-SND-005 between memory soundness,
  delegation closure, and the end-to-end error budget; add an explicit bound for each
  selected event class and invocation count.
- [ ] Count zero fingerprint factors as roots already covered by REQ-GP-SND-002; do
  not add a separate zero-denominator or zero-factor gap.

## Protocol ownership

- [ ] Move target-selected fields and hash backends out of the generic protocol
  relations and into named soundness configurations; keep only the parameterized
  transcript, Sumcheck, GKR, and WHIR relations under `protocols/`.
- [ ] Move below-L1 and L1 proof framing from the protocol modules into the owning FSV
  and public-I/O modules.
- [ ] Move Airbender circuit output-channel inventories from `protocols/gkr/` into the
  corresponding circuit and FSV proof inventories.
- [ ] Move memory, witness, and setup-cap layouts from `protocols/gkr/` into the
  circuit, memory, WHIR, and FSV modules that produce or consume them.
- [ ] Move uncommitted range-polynomial selection and evaluation from
  `protocols/gkr/` into `tables/ranges.md`, leaving only the generic GKR opening claim
  in the protocol.
- [ ] Move initialization top-bit rules and packing modes from `protocols/gkr/` into
  the unified memory-boundary and FSV modules.
- [ ] Move target schedules and field choices from `protocols/whir/` into named
  soundness configurations; keep WHIR's fold, commitment, opening, and authentication
  relations in the WHIR module.
- [ ] Move Airbender oracle-class selection and ordering from `protocols/whir/` into
  each circuit's proof-format owner while keeping Merkle authentication in WHIR.

## Serialization ownership

- [ ] Add field-element absorption encoding and proof-of-work nonce encoding to
  `protocols/transcript/`; make every transcript consumer import that encoding.
- [ ] Add Merkle-cap node order and cap serialization to `protocols/whir/`.
- [ ] Add the challenge-vector order, proof-stream order, boundary commitments, and L1
  calldata framing to the owning FSV and public-I/O modules; encode the product
  challenge on the wire as alpha_a0, alpha_a1, alpha_t0, alpha_t1, alpha_v0,
  alpha_v1, then beta, with each extension element represented by four base-field
  words in coefficient order starting at c_0, for 28 words total.
- [ ] Add program-image and precompile-ABI byte/word endianness to their ISA owners.
- [ ] Add PC and timestamp representation, including two 19-bit timestamp limbs, to
  the execution and memory modules that exchange them.
- [ ] Add ROM/RAM address-domain encoding and populated-set representation to
  `memory/common.md`, including ROM addresses below `2^22` and RAM addresses at or
  above that boundary.
- [ ] Add unified initialization/teardown top-bit ordering, the bound below 64, and
  window shifting to `memory/init-teardown-unified.md` and the consuming FSV module.
- [ ] Add every vector's element order to the module that produces and consumes that
  vector; keep abbreviations local to the owning module.
- [ ] Extract a shared serialization module only if two owners must implement one
  byte-identical boundary encoding and neither existing owner can canonically define
  it; otherwise keep serialization with the owning transcript, WHIR, FSV, memory,
  execution, ISA, or ABI module.

## ISA, execution, memory, recursion, and soundness

- [ ] Complete the unified ISA from the adopted RISC-V and RValp relations, document
  every intentional deviation from the official RISC-V specification as a DEV claim,
  and include the JIT transpiler relation needed to audit circuit compliance.
- [ ] Verify that the repository supports exactly the full unrolled, reduced unrolled,
  and reduced unified proven machines; update the profile catalog if another accepted
  ISA/execution combination exists.
- [ ] Add shared architectural pre-state/post-state assignment and unchanged-state
  semantics to the ISA common owner.
- [ ] Complete execution activation, padding, trace capacity, chunking, decoder
  authentication, and within-chunk continuity for unrolled and unified modes.
- [ ] Complete register, ROM, RAM, initialization, teardown, and final-state closure
  under `memory/`.
- [ ] Complete the FSV and recursion flow under `recursion/`, including base proof
  consumption, bridge and continuation transitions, terminal acceptance, and every
  genuinely supported target even when no prebuilt binary is checked in.
- [ ] Add the recursion-chain relation and hash assumptions to `recursion/`: initialize
  with `H(0^8 || end_params)`, extend with `H(previous_hash || end_params)`, and make a
  repeated identical `end_params` value a no-op.
- [ ] Add `soundness/assumptions.md` with the adopted algebraic and cryptographic
  assumptions imported by the protocol soundness modules.
- [ ] Add `soundness/parameters.md` with named configurations using BabyBear below L1,
  Proth120 at L1, and Sec100 as the only supported security mode.
- [ ] Add public links for every paper and standard cited by a normative or soundness
  claim, using the local reference library only to check the specification.
- [ ] Add `soundness/error-budget.md` and complete the composed error budget for
  transcript, lookup, global-product, Sumcheck, GKR, WHIR, recursion, and L1
  acceptance.

## Validation and migration completion

- [ ] Migrate every remaining module to `METADATA.md` and `notation.md`, preserving
  one canonical owner and one metadata row for every normative statement.
- [ ] Replace every displaced ID reference with the canonical owner or remove it when
  the former statement was intentionally superseded.
- [ ] Keep implementation file, symbol, and line mappings in audit output or skills;
  remove them from normative specification sources.
- [ ] Add the missing dependency modules named above, remove each completed item from
  this file, and run `python3 spec/check.py` until every structural, ID, import,
  metadata, content, and dependency-cycle check passes.
