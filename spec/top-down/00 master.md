# Airbender proof system

> State what the complete system proves, show how that claim decomposes across
> chunks, explain one chunk, then descend into GKR/WHIR, recursion, and
> soundness.

This document describes the important properties of Airbender from the outside of
the system inward. Standard constructions may be referenced without restating their
usual details. Airbender-specific behavior, production deviations, interfaces, and
security-critical details should be stated explicitly.

## 1. The machine and final claim

### What Airbender proves

_State the end-to-end claim in terms of an accepted program execution and its
observable result._

- **AirBender** is a cryptographic proof system capable of proving the execution of any RISCV32IM+Ziscr+custom compatible program up to ... cycles of runtime.

- **Program binaries** must be pre-processed during the offline phase of AirBender, before any proving takes place, allowing us to setup our decoding tables. Afterwards, a bytecode simulator executes the program to generate witness data pertaining to all "machine state" memory accesses, which are committed to setup our cross-chunk "global memory argument". From just the memory traces which we are able to generate all the witness data that will be used by the prover and circuits.

- **Execution cycles** are represented as unordered entries in the witness traces,  grouped according to the portion of the isa they belong to, and split into multiple 2^... sized chunks. An "execute" flag present in the witness data determines whether the cycle is part of the execution or just padding for the chunk. There are also witness traces ("virtual cycles") not directly related to the isa: they are used for initialisation and finalisation of the global memory argument, or fulfillment of precompile execution requests made by actual riscv cycles.

- **Chunks** are converted by the prover into standalone proofs by applying their respective circuit constraints (frontend) to a 100-bit compliant implementation of GKR and WHIR (backend). Each chunk proof outputs a local memory argument fingerprint, which can be collected by the verifier to construct the global memory argument fingerprint, and machine state, across all chunks.

- **Order** of execution is not relevant to the prover, as both the chunks and the witness traces contained therein are processed in arbitrary order. Sound progression of program execution can be inferred from the semantics enforced by the setup decoder, global memory argument, and the circuit constraints. The consistency of this "timed progression argument" will be explained later.

### Program and execution boundary

_Describe the program representation, how the proved program is identified, and
which part of that program may be executed._

- **Program Execution** is the timed sequential execution of riscv operations (cycles) found in the program binary. At any point in time, Riscv instructions are loaded from the binary address stored in the program counter (PC) and then executed.

### Architectural state

_Describe the program counter, timestamp, registers, ROM, RAM, and any additional
machine-visible state._

- The **Program Counter** is initialised to ROM address 0 at timestamp 4, the earliest possible time available after global memory initialisation, and is updated through the global memory argument by each cycle according to the instruction semantics encoded by the decoder and circuit constraints.

  | addr_space | addr_lo | addr_hi | ts_lo | ts_hi | val_lo | val_hi |
  |---|---|---|---|---|---|---|
  | 2 (PC) | 0 | 0 | timestamp[18:0] | timestamp[37:19] | pc[15:0] | pc[31:16] |

- The **RAM** is logically represented by 2^30 bytes of word-addressed word-sized slots, initialised by the memory argument at time 0 to zero values.

  | addr_space | addr_lo | addr_hi | ts_lo | ts_hi | val_lo | val_hi |
  |---|---|---|---|---|---|---|
  | 1 (RAM) | address[15:0] | address[31:16] | timestamp[18:0] | timestamp[37:19] | value[15:0] | value[31:16] |

- The **ROM** is logically represented by the lower 2^22 read-only bytes of the RAM, where writes are disallowed by the constraint system, but reads are concretely defined by tables that were setup during the offline phase of Airbender. Tables are accessed via word-aligned addresses, and contain all the contents of the raw program binary padded by invalid opcodes to 2^22.

- The **Decoder** is a collection of multiple setup decoder tables of the same width, one per circuit, meant for selecting and decoding riscv instructions to execute and indexed by the address contained in the program counter at any cycle. Decoder table indexes are restricted to the continuous address range formed by the low executable portion of the program binary (the rest being static data). Each decoder table is referenced by a respective circuit and encodes a unique subset of that executable portion of the binary. Padding of the tables and missing word-aligned entries are defined by repeated sentinel tuples containing values that however cannot satisfy other circuit constraints.

  | pc_lo | pc_hi | rs1 | rs2 | rd | imm_lo | imm_hi | funct3 | mask |
  |---|---|---|---|---|---|---|---|---|
  | pc[15:0] | pc[31:16] | first register index | second register index | destination register index | immediate[15:0] | immediate[31:16] | family-specific | opcode-family bitmask |

- **Registers** is a collection of the default 32 registers of RISCV, initialised to 0 values, plus special constant index registers which are not initialised so that they can be used for delegation (writes) and fulfillment (reads) of precompile calls via the permutation guaranteed by the global memory argument once tuple values remain fixed (therefore, not operating as timed updates). Register x0 is preserved equal to 0 through decoder table and constraint system invariants.

  | addr_space | addr_lo | addr_hi | ts_lo | ts_hi | val_lo | val_hi |
  |---|---|---|---|---|---|---|
  | 0 (REG) | register_index[15:0] | register_index[31:16] | timestamp[18:0] | timestamp[37:19] | value[15:0] | value[31:16] |

- **Timestamps** are 38-bit values used by the memory argument to enforce consistency of memory updates over time. Initialisation of the argument is at a fixed time of 0, and initialisation of the program counter state is at a fixed time of 4, preventing conflicting reads and writes between machine initialisation and execution. Time is always monotonically increased by 4 during each cycle for any non-delegation memory access, allowing for up to 4 unique memory accesses to the same address during any execution cycle. The combination of timed program counter accesses and program counter updates constrained by circuits guarantees the uniqueness of each cycle and the absence of missing or illicit cycles (to be explained in detail later).

### Initial state

_Describe the initial program counter, timestamp, registers, ROM contents, RAM
contents, and any verifier-supplied initial values._

- **Verifier Initialisation** enforces initialisation of the 32 base registers and program counter by injecting those tuples into the accumulators collected from the proof outputs. The memory initialisation constraints enforced by the circuits skip over such memory address spaces, to avoid insecure duplicates and allow for leaner circuits.

### Supported instruction set and custom operations

_Reference standard RISC-V behavior and enumerate only the supported subset,
Airbender extensions, precompile carriers, and material divergences._

- The **Instruction Set Architecture** of the machine closely follows that of RISCV32IM+Ziscr, with slight variations or addition of custom instructions. The various instructions are collected into instruction families, each represented by a circuit or "circuit family".

  | Instruction | Definition or distinction† |
  |---|---|
  | LUI rd, imm20 | RISC-V |
  | AUIPC rd, imm20 | RISC-V |
  | JAL rd, offset | RISC-V |
  | JALR rd, rs1, imm12 | RISC-V; all funct3 values are also accepted. |
  | BEQ rs1, rs2, offset | RISC-V |
  | BNE rs1, rs2, offset | RISC-V |
  | BLT rs1, rs2, offset | RISC-V |
  | BGE rs1, rs2, offset | RISC-V |
  | BLTU rs1, rs2, offset | RISC-V |
  | BGEU rs1, rs2, offset | RISC-V |
  | ADD rd, rs1, rs2 | RISC-V |
  | SUB rd, rs1, rs2 | RISC-V |
  | SLT rd, rs1, rs2 | RISC-V; all funct7 values except 0000001 (MULHSU) are also accepted. |
  | SLTU rd, rs1, rs2 | RISC-V; all funct7 values except 0000001 (MULHU) are also accepted. |
  | XOR rd, rs1, rs2 | RISC-V; all funct7 values except 0000001 (DIV) are also accepted. |
  | OR rd, rs1, rs2 | RISC-V; all funct7 values except 0000001 (REM) are also accepted. |
  | AND rd, rs1, rs2 | RISC-V; all funct7 values except 0000001 (REMU) are also accepted. |
  | ADDI rd, rs1, imm12 | RISC-V |
  | SLTI rd, rs1, imm12 | RISC-V |
  | SLTIU rd, rs1, imm12 | RISC-V |
  | XORI rd, rs1, imm12 | RISC-V |
  | ORI rd, rs1, imm12 | RISC-V |
  | ANDI rd, rs1, imm12 | RISC-V |
  | SLL rd, rs1, rs2 | RISC-V |
  | SRL rd, rs1, rs2 | RISC-V |
  | SRA rd, rs1, rs2 | RISC-V |
  | SLLI rd, rs1, shamt | RISC-V |
  | SRLI rd, rs1, shamt | RISC-V |
  | SRAI rd, rs1, shamt | RISC-V |
  | LB rd, imm12(rs1) | RISC-V, but loads from distinct ROM and RAM regions; when rd = x0 only pc advances by 4. |
  | LBU rd, imm12(rs1) | RISC-V, but loads from distinct ROM and RAM regions; when rd = x0 only pc advances by 4. |
  | LH rd, imm12(rs1) | RISC-V, but loads from distinct ROM and RAM regions; requires 2-byte alignment unless rd = x0, when only pc advances by 4. |
  | LHU rd, imm12(rs1) | RISC-V, but loads from distinct ROM and RAM regions; requires 2-byte alignment unless rd = x0, when only pc advances by 4. |
  | LW rd, imm12(rs1) | RISC-V, but loads from distinct ROM and RAM regions; requires 4-byte alignment unless rd = x0, when only pc advances by 4. |
  | SB rs2, imm12(rs1) | RISC-V, but writes to ROM are rejected. |
  | SH rs2, imm12(rs1) | RISC-V, but requires 2-byte alignment; writes to ROM are rejected. |
  | SW rs2, imm12(rs1) | RISC-V, but requires 4-byte alignment; writes to ROM are rejected. |
  | MUL rd, rs1, rs2 | RISC-V |
  | MULHU rd, rs1, rs2 | RISC-V |
  | DIVU rd, rs1, rs2 | RISC-V |
  | REMU rd, rs1, rs2 | RISC-V |
  | MOP.RR.0 rd, rs1, rs2 | Airbender ADDMOD: rd ← (rs1 + rs2) mod p |
  | MOP.RR.1 rd, rs1, rs2 | Airbender SUBMOD: rd ← (rs1 − rs2) mod p |
  | MOP.RR.2 rd, rs1, rs2 | Airbender MULMOD: rd ← (rs1 × rs2 × R⁻¹) mod p |
  | MOP.RR.3 rd, rs1, rs2 | Airbender FMAMOD: rd ← (rd_old + rs1 × rs2 × R⁻¹) mod p |
  | MOP.RR.4 rd, rs1, rs2 | Airbender TRIADD: rd ← (rd_old + rs1 + rs2) mod 2³² |
  | MOP.R.16 rd, rs1 | Airbender XORROT16: rd ← (rs1 XOR rd_old) ror 16 |
  | MOP.R.12 rd, rs1 | Airbender XORROT12: rd ← (rs1 XOR rd_old) ror 12 |
  | MOP.R.8 rd, rs1 | Airbender XORROT8: rd ← (rs1 XOR rd_old) ror 8 |
  | MOP.R.7 rd, rs1 | Airbender XORROT7: rd ← (rs1 XOR rd_old) ror 7 |
  | CSRRW rd, 0x7C0, x0 | Airbender nondeterminism read‡: rd ← arbitrary prover-supplied 32-bit witness value |
  | CSRRW x0, 0x7C0, rs1 | Airbender nondeterminism write‡: no-op; during witness generation, the simulator passes the current value of source register rs1 to application-defined logic as an unproven hint |
  | CSRRW x0, 0x7C7, x0 | Invokes an Airbender BLAKE2s round delegation; accepted only as a sequence of 7 or 10 instructions |
  | CSRRW x0, 0x7C8, x0 | Invokes an Airbender BLAKE2s G-function delegation; accepted only as a sequence of 56 or 80 instructions, representing 7 or 10 rounds of eight G-functions each |
  | CSRRW x0, 0x7CA, x0 | Invokes an Airbender controlled 256-bit arithmetic delegation for one operation |
  | CSRRW x0, 0x7CB, x0 | Invokes an Airbender Keccak-f[1600] delegation; accepted only as a sequence of 649 instructions implementing the special5 micro-operation schedule |

    *† RISC-V instructions retain their standard pc update unless stated otherwise. Custom instructions advance pc by 4 unless stated otherwise. In instruction syntax, rd, rs1, and rs2 are 5-bit register indices. In definitions, rs1 and rs2 denote the corresponding 32-bit register values, rd denotes the destination register, and rd_old denotes its preceding 32-bit value.*

    *‡ During witness generation, nondeterminism writes provide unproven request metadata and arguments to application-defined logic, which prepares values consumed by subsequent nondeterminism reads. Writes only control witness construction; reads inject the responses into proved register state. The proven program must validate the injected data through its own computation.*

- The **Circuit Families** of the Machine encode all of the constraints that are applied to the witness data by the Sumcheck-based proof system. Circuits not only simulate execution of individual instruction cycles, but also cover special operations which are not directly associated with a specific cycle such as initialisation and finalisation of the global memory argument, or fulfillment of special "precompile instruction" delegations.

  | Circuit family | Supported operations or role |
  |---|---|
  | add_sub_lui_auipc_mop | NOP + ADD + ADDI + LUI + SUB + AUIPC + MOP.RR.0 + MOP.RR.1 + MOP.RR.2 + MOP.RR.3 + nondeterminism CSRRW + delegation CSRRW |
  | jump_branch_slt | JAL + JALR + BEQ + BNE + BLT + BGE + BLTU + BGEU + SLT + SLTI + SLTU + SLTIU |
  | shift_binary | AND + ANDI + OR + ORI + XOR + XORI + SLL + SLLI + SRL + SRLI + SRA + SRAI |
  | load_store_word_only | LW + SW |
  | load_store_subword_only | LB + LBU + LH + LHU + SB + SH |
  | mul_div_unsigned | MUL + MULHU + DIVU + REMU |
  | unified_reduced_machine | Combines add_sub_lui_auipc_mop + jump_branch_slt + shift_binary + load_store_word_only; adds MOP.RR.4 + MOP.R.16 + MOP.R.12 + MOP.R.8 + MOP.R.7; embeds memory initialisation and teardown |
  | inits_and_teardowns | Initialises and finalises the memory-argument address windows used by unrolled proofs |
  | blake2_with_compression | Fulfills delegated BLAKE2s round and compression operations |
  | blake2_g_function | Fulfills delegated BLAKE2s G-function operations |
  | bigint_with_control | Fulfills delegated controlled 256-bit arithmetic operations |
  | keccak_special5 | Fulfills the delegated Keccak-f[1600] special5 micro-operation schedule |

- **Profiles** are collections of circuits and chunking metadata that can be used to prove RISCV programs more efficiently, according to the concrete needs of different Prover and Verifier infrastructures and processes (such as chunk sizes). The Prover selects a proving profile, and organises execution cycles and proving chunks accordingly. The circuits found in each profile are non-overlapping in terms of the machine operations they constrain, and typically target efficient execution of a reduced instruction set.

  | Profile | Circuit composition | Parameters and status |
  |---|---|---|
  | Full-unsigned unrolled | add_sub_lui_auipc_mop + jump_branch_slt + shift_binary + load_store_word_only + load_store_subword_only + mul_div_unsigned + inits_and_teardowns + all four delegation circuits | IMStandardIsaConfigUnsignedMulDivOnly; FullUnsignedMachineDecoderConfig; MachineType::FullUnsigned. Executor and initialisation/teardown chunks: 2^24 rows. blake2_with_compression: 2^20 rows. Other delegation chunks: 2^22 rows |
  | Reduced unrolled | add_sub_lui_auipc_mop + jump_branch_slt + shift_binary + load_store_word_only + inits_and_teardowns + the two declared Blake delegation carriers | ReducedMachineWithDelegation; ReducedMachineDecoderConfig; MachineType::Reduced. Executor and initialisation/teardown chunks: 2^24 rows. Blake delegation chunks: 2^20 and 2^22 rows. The current GPU decoder setup admits only blake2_with_compression |
  | Reduced unified | unified_reduced_machine + separate delegation circuits | ReducedMachineDecoderConfig; MachineType::Reduced; ExecutionKind::Unified. Unified chunks: 2^23 rows with inline initialisation and teardown. Adds MOP.RR.4 and four fixed XOR-rotate MOPs. Its decoder admits all four delegation carriers, while ReducedMachineWithDelegation declares only the two Blake carriers |
  | Full signed declaration | Same nominal unrolled families as the full profile | IMStandardIsaConfig; FullMachineDecoderConfig; MachineType::Full. Declares signed multiply/divide, but the proving setup installs mul_div_unsigned; not a complete production proving profile |
  | Reduced no-delegation declaration | Reduced instruction families with no delegation circuits | ReducedMachineWithoutDelegation. Not selected by the current main proving pipeline |
  | Debug reduced declaration | No stable circuit manifest | DebugReducedMachineDecoderConfig. Development-only; enables subword memory and both special-rotation modes |

### Admitted and rejected executions

_Describe alignment, address, cycle-count, unsupported-instruction, exception,
termination, and other execution boundaries._

- If execution continues after a control-flow instruction, its next pc must identify a supported word-aligned decoder-table entry; otherwise the execution is rejected rather than trapped.

### Final state and public outputs

_Describe the final program counter and timestamp, final registers or memory values
available to the verifier, application output, and the condition under which the
whole execution is accepted._

- **Program Output** is a subset of the final machine state values communicated by the Prover and validated by the Verifier. The Verifier can use such data to keep track of desired program invariants, including valid recursive verification.

- **Verifier Finalisation** takes the final program counter, timestamp, and base register values (encoding the programs' "output") provided by the Prover and enforces finalisation by injecting their tuples into the folded memory accumulator pairs collected from the various proof outputs. The standard invariants provided by memory access constraints guarantee that no cycles have been skipped and that the injected values relate to a valid last proven state of the machine. Whether this last proven state is actually the accepting final state of the provided Riscv program depends on the correct program's termination conditions described below.

- **Chunk Proof Outputs** include the Read Set and Write Set pair of extension field accumulators produced by the memory permutation argument's grand product relations. The pairs are accumulated across every chunk via multiplication, so that ultimately the Verifier ends up with a single pair. After injection of the initialisation and finalisation values described above, the Verifier can conclude the proof by checking that the accumulator pair values are equal.

- **Public Inputs** are technically absent in the system, beyond those encoded directly in the circuit constraints and known final recursion identifier constants. The Prover dynamically provides, via proof data, advices on the final program's state to the Verifier. The Verifier then uses such advice values to complete the global memory argument's verification step, and forwards them into a "recursion hash chain" (along with metadata related to the proof) for later verification by either the same verifier or a future recursive one.

- **Correct Program Termination** depends on the program binary that is being proven, and the end state validation logic found in the verifier. The verifier therefore collects advices on final machine execution state provided by the Prover, and optionally checks them against known public inputs representing valid machine termination state, depending on whether the verifier sits at the end of a recursive chain of proving or not. If the execution being checked is that of a recursive verifier program, it is incumbent on that program's binary to encode a correct end state in its instructions, and the propagation of a "recursion hash chain" which accurately encodes the history of the programs that were proven. It is possible for the Verifier to identify the proven program by its table setup Merkle Tree commitment root caps, which are communicated as advices by the Prover in the proof data, and which are required for validation of table lookups relating to the Decoder and ROM.

## 2. Whole-proof decomposition

### From one execution to many proofs

_Explain why execution is divided into fixed-capacity chunks and how the complete
execution is represented by their proofs._

### Execution profiles

_Describe the unrolled, reduced-unified, recursion, and terminal profiles that
materially change the accepted proof structure._

### Instruction-family chunks

_Describe program-dependent family circuits, their responsibilities, and how
executed instructions are assigned to them._

### Precompile chunks

_Describe delegated computations, their carrier instructions, their separate
fulfillment circuits, and how invocations are matched to fulfillments._

### Initialization and teardown chunks

_Describe why memory initialization and finalization are proved, including the
difference between separate unrolled proofs and data folded into unified chunks._

### Chunk capacities and invocation counts

_State the fixed capacities and the rule determining how many instances of each
chunk type appear._

### Predication and padding

_Describe active rows, inactive rows, padding placement, and the requirement that
inactive rows make no machine transition or shared-argument contribution._

### Per-chunk inputs and outputs

_Summarize what each chunk consumes, commits to, proves, and exports to the
full-statement verifier._

### Full-statement verification

_Describe how all chunk proofs, setup commitments, boundary values, and exported
argument values are combined into one accepted program-proof statement._

## 3. Cross-chunk consistency

### State as read and write events

_Describe the alternative view of machine execution as read-side and write-side
multisets of state-transition events._

### Event tuple encoding

_Define the address-space tag, address, timestamp, value, limb representation, and
read/write orientation used by an event._

### Address-space namespaces

_Describe how ordinary registers, RAM, the program counter, and synthetic
delegation entries share or separate their namespaces._

### Grand-product multiset argument

_Describe tuple compression, the read and write products, inactive-row identity
factors, and the final equality checked by the verifier._

### Challenge derivation and binding

_Describe when the tuple-compression challenges are sampled and what must already
be committed before they are known._

### Timestamp ordering and state continuity

_Explain the local timestamp relations that, together with multiset equality, turn
unordered events into coherent state histories._

### Register consistency

_Describe initial and final register entries, ordinary register accesses, the zero
register, and any special use of register-space addresses._

### RAM and ROM consistency

_Describe mutable RAM histories, authenticated ROM reads, forbidden writes, address
alignment, initialization, and finalization._

### Program-counter consistency

_Describe the initial PC entry, one transition per active cycle, timestamp steps,
and the final PC entry._

### Delegation consistency

_Describe how executor-side precompile invocations and fulfillment-circuit outputs
contribute matching events._

### Boundary contributions

_Describe which initial and final entries are supplied directly by the verifier and
which are proved by initialization/teardown circuits._

### From global closure to one execution

_Summarize why the cross-chunk argument and the local circuit relations jointly
describe one state-consistent execution rather than unrelated valid chunks._

## 4. Inside one chunk

### Chunk trace and witness

_Describe the rows, committed witness data, fixed setup data, and values derived by
the circuit._

### Program preprocessing and setup

_Describe how the program is split between circuit families and how program-specific
decoder or setup data is constructed and authenticated._

### Instruction fetch and decoder lookup

_Describe how an active row binds its PC to one supported instruction and selects
exactly one local operation relation._

### Active-cycle transition

_Describe how a row reads the current PC, timestamp, registers, and memory; applies
the selected instruction; and produces the next state._

### Local register and memory accesses

_Describe the ordering of accesses within a cycle and the constraints on addresses,
values, and timestamps._

### Contributions to global arguments

_Describe the register, RAM, PC, lookup, and delegation values emitted by the chunk
for later cross-chunk aggregation._

### Local lookups and range checks

_Describe decoder membership, fixed semantic tables, limb range checks, timestamp
range checks, and how their local claims are closed._

### Instruction-family circuits

_Summarize the circuit families and only the nonstandard instruction behavior or
family-specific invariants that must be known at this level._

### Precompile fulfillment circuits

_Summarize each delegated computation, its calling convention, its state effects,
and the invariant connecting it to its carrier instructions._

### Unrolled and unified chunk differences

_Describe differences in dispatch, setup, trace capacity, lookup layout,
initialization/teardown placement, and exported outputs._

### Chunk outputs

_List the claims and values handed from one verified chunk to the full-statement
verifier._

## 5. Proving one chunk and recursion

### Arithmetization and committed polynomials

_Describe how the chunk relation becomes a layered algebraic circuit and which
polynomials or columns are committed._

### GKR and Sumcheck

_Describe the layered claim, the sequence of reductions, batching, and the claim
that remains at the end of GKR._

### Lookup and global-argument handoffs

_Describe how local lookup products and memory-like grand-product outputs are bound
to the same committed chunk._

### WHIR polynomial commitment proof

_Describe how WHIR proves the remaining polynomial evaluation or proximity claims
and what verifier inputs bind it to GKR._

### Transcript and Fiat-Shamir order

_Describe the important commitment, absorption, challenge, proof-of-work, and
opening order, emphasizing Airbender-specific choices._

### Chunk-proof acceptance

_Summarize the checks that make one GKR, Sumcheck, and WHIR proof an accepted proof
of the selected chunk relation._

### Recursive verification as machine execution

_Explain that recursion proves an execution of a verifier program under the same
machine-and-chunk architecture._

### Base proof and unrolled continuation

_Describe the base full-statement verifier, the proof data passed to it, and the
unrolled recursive continuation layers._

### Unrolled-to-unified bridge

_Describe what changes at the bridge, what inner statement remains the same, and
which values bind the two recursion modes._

### Unified continuation

_Describe repeated unified recursive verification and its stopping condition._

### Terminal verification and external acceptance

_Describe the final proof shape, public claim, optional L1 path, verifier identities,
and the condition under which an external consumer accepts the result._

## 6. Soundness and assumptions

### End-to-end soundness goal

_State the intended consequence of final-proof acceptance and the knowledge or
existence claim made about a complete program execution._

### Algebraic and cryptographic assumptions

_List the field, hash, Fiat-Shamir, polynomial-commitment, and extraction assumptions
on which the claim depends._

### Baseline constructions

_Identify the standard or clean baseline for GKR/Sumcheck, WHIR, lookups, memory
consistency, batching, and recursion._

### Airbender production deviations

_Enumerate every soundness-relevant difference between those baselines and the
production protocol, omitting purely operational optimizations._

### Local proof-system errors

_Account for GKR/Sumcheck, WHIR, lookup, range-check, memory-fingerprint, batching,
and other algebraic error terms._

### Challenge causality and reuse

_State which values are bound before each challenge, where challenges are reused,
and why prover-controlled data cannot adapt to them._

### Composition across chunks and recursion

_Explain how individual chunk claims, the full-statement verifier, recursive layers,
and terminal verification compose without omissions or duplicated execution._

### Concrete security parameters

_Record the selected fields, extension degrees, query counts, fold schedules,
grinding, hash modes, and other parameters needed for a concrete bound._

### Total error bound

_Combine invocation multiplicities and component errors into the claimed end-to-end
soundness bound without double-counting shared challenges._

### Remaining proof obligations

_List the standard, adapted, and new lemmas or implementation-binding arguments that
must still be completed for the W2 or W3 deliverable._

### Open questions

_Keep unresolved semantic decisions and disputed implementation interpretations here
until they are reviewed. Do not silently turn them into accepted specification
claims._
