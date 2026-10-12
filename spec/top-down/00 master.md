# Airbender proof system

> State what the complete system proves, show how that claim decomposes across
> chunks, explain one chunk, then descend into GKR/WHIR, recursion, and
> soundness.

This document describes the important properties of Airbender from the outside of
the system inward. Standard constructions may be referenced without restating their
usual details. Airbender-specific behavior, production deviations, interfaces, and
security-critical details should be stated explicitly.

## 1. The Airbender Machine at a bird's eye view

### What Airbender proves

_State the end-to-end claim in terms of an accepted program execution and its
observable result._

- **AirBender** is a cryptographic proof system capable of proving the execution of any program compatible with its supported RISC-V RV32IM subset, selected Zicsr CSRRW-based machine-interface operations (external nondeterminism-oracle access and the internal precompile-delegation bus), and Airbender-defined Zimop operations, up to ... cycles of runtime.

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

- The **Decoder** is a collection of multiple setup decoder tables of the same width, one per circuit, meant for selecting and decoding riscv instructions to execute and indexed by the address contained in the program counter at any cycle. Decoder table indexes are restricted to the 4-byte aligned continuous address range formed by the low executable portion of the program binary (the rest being static data). Each decoder table is referenced by a respective circuit and encodes a unique subset of that executable portion of the binary. Padding of the tables and missing word-aligned entries are defined by repeated sentinel tuples containing values that however cannot satisfy other circuit constraints.

  | pc_lo | pc_hi | rs1 | rs2 | rd | imm_lo | imm_hi | funct3 | mask |
  |---|---|---|---|---|---|---|---|---|
  | pc[15:0] | pc[31:16] | first register index | second register index | destination register index | immediate[15:0] | immediate[31:16] | family-specific | opcode-family bitmask |

- **Registers** is a collection of the default 32 registers of RISCV, initialised to 0 values, plus special constant index registers which are not initialised so that they can be used for delegation (writes) and fulfillment (reads) of precompile calls via the permutation guaranteed by the global memory argument once tuple values remain fixed (therefore, not operating as timed updates). Register x0 is preserved equal to 0 through decoder table and constraint system invariants.

  | addr_space | addr_lo | addr_hi | ts_lo | ts_hi | val_lo | val_hi |
  |---|---|---|---|---|---|---|
  | 0 (REG) | register_index[15:0] | register_index[31:16] | timestamp[18:0] | timestamp[37:19] | value[15:0] | value[31:16] |

- **Timestamps** are 38-bit values used by the memory argument to enforce consistency of memory updates over time. Initialisation of the argument's memory locations is at a fixed time of 0, and initialisation of the program counter state is at a fixed time of 4, preventing conflicting reads and writes between machine initialisation and execution. Time is always monotonically increased by 4 during each cycle for any non-delegation memory access, allowing for up to 4 unique memory accesses to the same address during any execution cycle. Accesses to provably distinct memory cells may share a timestamp, including accesses performed by delegated precompile fulfillments rather than literal machine cycles. The combination of timed program counter accesses and program counter updates constrained by circuits guarantees the uniqueness of each cycle and the absence of missing or illicit cycles (to be explained in detail later).

### Initial state

_Describe the initial program counter, timestamp, registers, ROM contents, RAM
contents, and any verifier-supplied initial values._

- **Verifier Initialisation** enforces initialisation of the 32 base registers and program counter by injecting those tuples into the accumulators collected from the proof outputs. The memory initialisation constraints enforced by the circuits skip over such memory address spaces, to avoid insecure duplicates and allow for leaner circuits.

### Supported instruction set and custom operations

_Reference standard RISC-V behavior and enumerate only the supported subset,
Airbender extensions, precompile carriers, and material divergences._

- The **Instruction Set Architecture** of the machine is a subset of RISC-V RV32IM+Zicsr+Zimop, with the deviations and Airbender-defined operations listed below. The various instructions are collected into instruction families, each represented by a circuit or "circuit family". Support for signed M-extension operations has been removed for performance and development purposes, but can be added back if needed.

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
  | CSRRW x0, 0x7C7, x0 | Airbender BLAKE2s round delegation request: when fulfilled, 128-byte-aligned x10 points to the input/output state h[0..7] followed by the work state v[0..15]; 64-byte-aligned x11 points to the message block m[0..15]; x12 selects the round, 7- or 10-round schedule, and mode. Direct-block mode compresses m into h using the counter and final-block values in v. Two-to-one mode compresses h ∥ m[0..7], or the reverse order, into h; 10-round mode gives BLAKE2s-256 of the concatenation, while 7-round mode is Airbender's BLAKE3-inspired reduced variant. Each instruction performs one round; a complete run updates h and v in place. (Airbender Decoder preprocessing accepts this instruction only in exact runs of 7 or 10 consecutive copies.) |
  | CSRRW x0, 0x7C8, x0 | Airbender BLAKE2s G-function delegation request: when fulfilled, 64-byte-aligned x10 points to v[0..15], the sixteen-word local work vector persisted by Airbender, while 64-byte-aligned x11 points to m[0..15], the sixteen-word message-block vector. x12 selects either the standard 10-round schedule or Airbender's first-7-round variant and the current G-function index. Each instruction performs one G function; a complete run updates v in place. (Airbender Decoder preprocessing accepts this instruction only in exact runs of 56 or 80 consecutive copies.) |
  | CSRRW x0, 0x7CA, x0 | Airbender controlled 256-bit arithmetic delegation request: when fulfilled, x10 and x11 point to 32-byte-aligned little-endian 256-bit RAM operands a and b, while x12 selects ADD (a + b + κ), SUB (a − b − κ), SUB_NEGATE (b − a − κ), MUL_LOW (the low 256 bits of a × b), MUL_HIGH (the high 256 bits), EQ (preserves a and tests a = b), or MEMCOPY (b + κ), where κ is x12's carry/borrow input bit. The 256-bit result, reduced modulo 2²⁵⁶ when applicable, overwrites a at x10; x12 returns carry for ADD and MEMCOPY, borrow for SUB and SUB_NEGATE, overflow for MUL_LOW, equality for EQ, and 0 for MUL_HIGH. |
  | CSRRW x0, 0x7CB, x0 | Airbender Keccak-f[1600] delegation request: when fulfilled, x11 points to a 256-byte-aligned RAM region containing twenty-five little-endian 64-bit state lanes followed by six scratch lanes, while x10 holds the mode, iteration, and round control. Its seven modes decompose each round into a deferred ι/column-parity step, two D-mixing steps, a θ column update, a ρ rotation with implicit π indexing, and two χ half-row steps. Each instruction performs one such micro-operation, updates the selected lanes, and advances x10. A complete run performs the standard 24-round Keccak-f[1600] permutation in place. (Airbender Decoder preprocessing accepts this instruction only in exact runs of 649 consecutive copies.) |

    *† RISC-V instructions retain their standard pc update unless stated otherwise. Custom instructions advance pc by 4 unless stated otherwise. In instruction syntax, rd, rs1, and rs2 are 5-bit register indices. In definitions, rs1 and rs2 denote the corresponding 32-bit register values, rd denotes the destination register, and rd_old denotes its preceding 32-bit value. For modular MOPs, p = 0x78000001 = 2³¹ − 2²⁷ + 1 is the BabyBear modulus, R = 2³² is the Montgomery radix, and R⁻¹ is its inverse modulo p.*

    *‡ During witness generation, nondeterminism writes provide unproven request metadata and arguments to application-defined logic, which prepares values consumed by subsequent nondeterminism reads. Writes only control witness construction; reads inject the responses into proved register state. The proven program must validate the injected data through its own computation.*

  - in the delegation arguments there is no "fake/shadow-ROM" range check. accessing that is UB!
  - pc + 4 (mod 2^32)

- The **Circuit Families** of the Machine encode all of the constraints that are applied to the witness data by the Sumcheck-based proof system. Circuits not only simulate execution of individual instruction cycles, but also cover special operations which are not directly associated with a specific cycle such as initialisation and finalisation of the global memory argument, or fulfillment of special "precompile instruction" delegations.

  | Circuit family | Supported operations or role |
  |---|---|
  | add_sub_lui_auipc_mop | ADD + ADDI + LUI + SUB + AUIPC + MOP.RR.0 + MOP.RR.1 + MOP.RR.2 + MOP.RR.3 + nondeterminism read/write CSRRW + delegation-request CSRRW |
  | jump_branch_slt | JAL + JALR + BEQ + BNE + BLT + BGE + BLTU + BGEU + SLT + SLTI + SLTU + SLTIU |
  | shift_binary | AND + ANDI + OR + ORI + XOR + XORI + SLL + SLLI + SRL + SRLI + SRA + SRAI |
  | load_store_word_only | LW + SW |
  | load_store_subword_only | LB + LBU + LH + LHU + SB + SH |
  | mul_div_unsigned | MUL + MULHU + DIVU + REMU |
  | unified_reduced_machine | Combines add_sub_lui_auipc_mop + jump_branch_slt + shift_binary + load_store_word_only; adds MOP.RR.4 + MOP.R.16 + MOP.R.12 + MOP.R.8 + MOP.R.7. For every address in its verifier-bound 4-byte-aligned RAM windows, it embeds the same Write-Set initialisation and Read-Set teardown tuples as inits_and_teardowns, closing the global RAM access history inline. |
  | inits_and_teardowns | For every 4-byte-aligned address < 2³⁰, contributes the Write-Set initialisation tuple (1 (RAM), address[15:0], address[31:16], 0, 0, 0, 0) and Read-Set teardown tuple (1 (RAM), address[15:0], address[31:16], ts_final[18:0], ts_final[37:19], val_final[15:0], val_final[31:16]). The addresses are split across 16 fixed contiguous windows; together with execution reads and writes, these tuples close the global RAM access history between the zero-initialised and final RAM states. |
  | blake2_with_compression | Fulfills BLAKE2s round and compression delegation requests |
  | blake2_g_function | Fulfills BLAKE2s G-function delegation requests |
  | bigint_with_control | Fulfills controlled 256-bit arithmetic delegation requests |
  | keccak_special5 | Fulfills Keccak-f[1600] special5 micro-operation delegation requests |

- **Profiles** are collections of circuits and chunking metadata that can be used to prove RISCV programs more efficiently, according to the concrete needs of different Prover and Verifier infrastructures and processes (such as chunk sizes). The Prover selects a proving profile, and organises execution cycles and proving chunks accordingly. The circuits found in each profile are non-overlapping in terms of the machine operations they constrain, and typically target efficient execution of a reduced instruction set.

  | Profile | Circuit composition and supported operations† |
  |---|---|
  | Reduced unrolled | add_sub_lui_auipc_mop + jump_branch_slt + shift_binary + load_store_word_only + inits_and_teardowns + blake2_with_compression + blake2_g_function |
  | Full unrolled | Inherits Reduced unrolled; adds load_store_subword_only + mul_div_unsigned + bigint_with_control + keccak_special5 |
  | Reduced unified | unified_reduced_machine + blake2_with_compression + blake2_g_function + bigint_with_control + keccak_special5 |

  *† Circuits whose operations do not occur during execution may be omitted from the proof.*

### Admitted and rejected executions

_Describe alignment, address, cycle-count, unsupported-instruction, exception,
termination, and other execution boundaries._

- **Unsupported Operations** such as invalid opcodes, input parameters, or addresses cannot satisfy the constraint system, which includes Decoder-table lookups, and are rejected by the Verifier.

- **Dynamic Traps** and **Priviledged System** functionalities are not supported by Airbender.

### Final state and public outputs

_Describe the final program counter and timestamp, final registers or memory values
available to the verifier, application output, and the condition under which the
whole execution is accepted._

- **Program Output** is a subset of the final machine state values communicated by the Prover and validated by the Verifier. The Verifier can use such data to keep track of desired program invariants, including valid recursive verification.

- **Verifier Finalisation** takes the final program counter, timestamp, and base register values (meant to encode the "program output") provided by the Prover and enforces finalisation by injecting their Read-Set tuples into the folded memory accumulator pairs collected from the various proof outputs. The standard invariants provided by memory access constraints guarantee that no cycles have been skipped and that the injected values relate to a valid last proven state of the machine. Whether this last proven state is actually the accepting final state of the provided Riscv program depends on the correct program's termination conditions described below.

- **Chunk Proof Outputs** include the Read Set and Write Set pair of extension field accumulators produced by the memory permutation argument's grand product relations. The pairs are accumulated across every chunk via multiplication, so that ultimately the Verifier ends up with a single pair. After injection of the initialisation and finalisation values described above, the Verifier can conclude the proof by checking that the accumulator pair values are equal.

- **Public Inputs** are absent from the system circuits. However the Prover dynamically provides, via proof data, values on the final machine's state and the program's setup Merkle tree caps to the Verifier. The Verifier then uses the relevant input values to complete the global memory argument's verification step, propagate the program output, or update a "recursion hash chain" (along with metadata related to the proof) for later verification by either the same verifier or a future recursive one.

- **Correct Program Termination** depends on the program binary that is being proven, and the end state validation logic found in the verifier. The machine has no HALT instruction: a proof terminates after a bounded number of cycles, and the Verifier determines whether the resulting state satisfies the program-specific termination conditions. The verifier therefore collects values on final machine execution state provided by the Prover and optionally checks them against fixed expected constants representing valid machine termination state, depending on whether the verifier sits at the end of a recursive chain of proving or not. If the execution being checked is that of a recursive verifier program, it is incumbent on that program's binary to encode a "correct end state" in its instructions, and the propagation of a "recursion hash chain" which accurately encodes the history of the programs that were proven. It is possible for the Verifier to identify the proven program by its table setup Merkle Tree commitment root caps, which are communicated as public inputs by the Prover in the proof data, and which are required for validation of table lookups relating to the Decoder and ROM.

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

- A global **Offline Memory Checking** permutation argument is used to guarantee consistency of our ROM, RAM, PC state, Register states, NonDeterminism I/O, and precompile Delegation subarguments. The argument is taken from the seminary Two Shuffles Make A RAM paper (https://eprint.iacr.org/2023/1115) and is implemented via standard Grand Product permutation fingerprinting: accesses are split between Read Set (RS) and Write Set (WS) sets that must complement one another, and each read/write access is defined by a fixed-width tuple. Access tuples contain sufficient information to uniquely identify both the subargument and entry index or address, and contain a 38-bit timestamp and 32-bit value to record the data. The argument works in-circuit by multiplicatively accumulating the RS and WS values after each access, including special initialisation and finalisation setup accesses, and returning the final pair to the Verifier. The Verifier then enforces its own final state by appending access tuples to the pair, and then checks them for equality. For any write tuple appended to the global memory argument, range checks on individual tuple elements are enforced; range checks on the read tuple counterparts are omitted, and their correctness hinges directly on the permutation argument.
  -  all accesses have write_ts > read_ts, except for the csrrw access in a delegation precompile row which cannot have it (as the ts is inverted)

- **ROM / RAM / Register Subarguments** work as regular accesses, wherein each read tuple fulfills the permutation by using the same value and timestamp registered by the last write to that index, and each write tuple records a new timestamp and value, using the current cycle's current timestamp. The permutation therefore stays open at the first read and the last write, as they require matching asymmetric accesses which will be fulfilled by the initialisation and finalisation phases detailed below. 
  - no ROM, add RAM >= threshold
  - > Shadow-ROM range. The RAM address space includes a shadow range corresponding to the architectural ROM region. This range is initialized and participates in the global memory argument through dummy or shadow accesses, rather than ordinary program-visible RAM operations. Its values do not represent the program’s ROM contents; those are authenticated separately through setup-table lookups.

- **Init and Teardown Phases** are the names given to the initialisation and finalisation constraints of the argument, as encoded within the circuit constraints. As each regular (ROM/RAM/Register) memory access comes with an asymmetric pair of read and write tuples which advance the access slot's timestamp, a correct permutation will end up requiring an initial state (first write) and a final state (last read) to close the gap. These first writes and final reads are enforced by special symmetrical constraints which initialise the entire ROM/RAM memory regions and finalise them with prover-provided values and timestamps. PC and Register subarguments are directly initialised and finalised by the Verifier, which also uses part of those values for identification of the proven program. Finalisation and consistency of the PC State subargument (including final timestamp), as detailed below, will guarantee correctness for the entire memory. The precompile Delegation subargument does not require any initialisation or finalisation, as its accesses are always symmetrical and automatically result in a closed permutation.

- The **PC Subargument** works via single-slot global memory accesses which during every cycle update the same slot to a new value and timestamp. The value of the program counter is constrained by the execution circuits, which, in combination with the monotonically increasing timestamp and the permutation-based nature of the global memory argument, forbids cycle duplicates or skips and ensures consistency of machine execution over time. The timestamp is always increased by increments of four, to enforce proper time sequence within cycles themselves and allow for up to four concurrent accesses to the same memory slot in a single cycle: duplicate accesses could break the permutation argument and invalidate the global memory argument. In practice, a normal RISCV32 cycle might access the same slot up to three times (eg rs1, rs2, and rd), and fulfillment of delegation would fill in the fourth access slot. Finally, the Verifier enforces the initialisation and finalisation of machine execution by appending to the memory argument: the first cycle is set to timestamp 4, and the last cycle is set to whatever timestamp and program counter is provided by the Prover. A favourable property of this design is that it decouples ordering of cycles from witness trace entries, allowing the Prover to prove execution consistency by opening just a single row at a time instead of two.
  - forbidden overflow/wraparound for ts is fundamental!

- The **Delegation Subargument** leverages a fixed register address range that cannot appear in any normal RISCV cycle register access. When executing a CSRRW "delegation call" cycle, a global argument write tuple to a constant register with id greater or equal to 32 is appended, containing value 0 and assigned to the current cycle timestamp. A matching row in the delegation precompile chunks will then append a symmetric read tuple to the global memory argument, with all values fixed except for the timestamp. The correctness of the timestamp is then implicitly enforced, thanks to the permutation of the global memory argument.
  - one sided = dummy tuple 

- The **NonDeterminism Subargument** is used by the machine to retrieve unconstrained or "non-deterministic" data from the Prover, to simulate I/O. This data must then be validated directly by the host OS, when validation is required. NonDeterministic write cycles function as a no-op for the machine, not as actual global memory writes, and are a performance trick used to generate hints for Prover's witness generation in preparation of a NonDeterministic read. NonDeterministic read cycles function as global memory argument accesses to specified registers, with the read tuple matching the correct previous value of that register and the write value being entirely unconstrained other than a 32-bit range check.

- **Execute Padding** is a mode of operation used by the machine to enforce 2-smooth execution chunk sizes by appending execution traces with dummy rows. This mechanism hinges on the presence of a boolean "execute" variable present on any circuit row. When the execute variable is set to 1, the memory read and write tuples generated by the circuit are appended to the global memory argument, and when it is set to 0 they are not. Since our global memory's PC Subargument enforces correct sequential execution of the machine over time, it is not possible for a malicious prover to use Padding to either inject fictitious cycles into the execution, or remove valid ones.

### Event tuple encoding

_Define the address-space tag, address, timestamp, value, limb representation, and
read/write orientation used by an event._

- **Tuple Encoding**
  - (a, b, c, ...)

### Address-space namespaces

_Describe how ordinary registers, RAM, the program counter, and synthetic
delegation entries share or separate their namespaces._

- **Tuple Address Ranges**
  - ROM: (id, addr)
  - RAM: (id, addr)
  - ...

### Grand-product multiset argument

_Describe tuple compression, the read and write products, inactive-row identity
factors, and the final equality checked by the verifier._

- **Grand-Product Permutation Argument**
  - follows standard function: theoretical fingerprinting, compression of tuples and then appending to a multiset. updates recordev via monotonically increasing timestamps, wraparound not permitted.

### Challenge derivation and binding

_Describe when the tuple-compression challenges are sampled and what must already
be committed before they are known._

- **Setup and Challenges** of the global memory argument
  - follows standard function: we precommit to all memory traces, extract challenges, use them for compression and also permutation/grand-product.

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

- the **Witness Execution Trace** is the collection of all polynomials that contain variable data to satisfy the proven circuit chunks (see Section 1). Each polynomial row identifies a fixed cycle and timestamp, allowing the Verifier to query the same point for all of the witness polynomials to validate a single machine cycle.
  
- the **Memory Execution Trace** is the subset of the witness trace containing values for the variables that directly contribute to the global memory access tuples (see Section 3). As described in the memory section, the LDE evaluations of the polynomials for this data are committed before extracting the random challenges that are required by the global memory argument. Any variables that directly contribute to the global memory (permutation) argument are included in the "pre-commit" phase, along with the global padding "execute" variable which is used to enable or disable the memory contributions. In practice, each opcode cycle will include 4 memory accesses: one for the fixed PC subargument slot, and 3 for distinctly-timed variable memory slots required by the circuit; precompile circuits are free to occupy a fourth distinct memory access timestamp, with any number of further accesses as long as the addresses are guaranteed to be unique.

### Program preprocessing and setup

_Describe how the program is split between circuit families and how program-specific
decoder or setup data is constructed and authenticated._

- **Decoder Binary Setup**

- **ROM Binary Setup**

### What one chunk proves

_State the local relation for instruction, precompile, and initialization/teardown
chunks, including active rows, padding, and the argument contributions they produce._

- <mark>A <strong>Chunk Relation</strong> requires every row to satisfy its circuit's local constraints and lookup relations. For active instruction rows these describe the selected machine operation; for precompile rows, the delegated computation; and for initialization/teardown rows, the prescribed memory boundaries. The chunk also proves that its argument outputs are computed from those same rows.</mark>

- <mark>The <strong>Chunk Interface</strong> consists of a circuit family and fixed trace capacity, its setup tables, the Prover's witness and commitments, and the external memory challenges. The witness includes auxiliary values such as carries and lookup multiplicities. Lookup challenges are derived within the chunk proof. The resulting proof authenticates the local argument outputs; setup identity and global memory closure are checked by the full-statement Verifier.</mark>

### Instruction fetch and decoder lookup

_Describe how an active row binds its PC to one supported instruction and selects
exactly one local operation relation._

### Active-cycle transition

_Describe how a row reads the current PC, timestamp, registers, and memory; applies
the selected instruction; and produces the next state._

- <mark><strong>Circuit Constraints</strong> are field equations whose residuals must equal zero. Boolean variables satisfy b × (b − 1) = 0, while range lookups and constrained carries or borrows give limb equations their intended integer meaning. Decoder-authenticated selectors choose the operation relation. An activation flag disables only the relations explicitly multiplied by it; the remaining equations and lookup requirements still apply.</mark>

- <mark><strong>Padding Witnesses</strong> must still satisfy the circuit equations, fixed-table queries, and range checks that are not gated by execute. The decoder lookup has coefficient execute, so inactive rows need not decode a program instruction. Their memory factors are 1 + execute × (encoded_tuple − 1), hence equal 1 on both sides when execute = 0. Padding therefore adds no execution events without making the rest of the witness unconstrained.</mark>

- <mark>An <strong>ADD Row</strong> with nonzero destination authenticates its PC and register indices through the decoder lookup, and claims the operand values x and y through ordered register accesses. For result z, the limb equations are x_lo + y_lo = z_lo + 2^16 × c0 and x_hi + y_hi + c0 = z_hi + 2^16 × c1, with boolean carries and 16-bit result limbs. The row contributes the PC update, value-preserving source accesses, and destination update to the memory argument. Local constraints establish z = (x + y) mod 2^32; global closure establishes the claimed input values, including when register indices coincide.</mark>

### Local register and memory accesses

_Describe the ordering of accesses within a cycle and the constraints on addresses,
values, and timestamps._

- <mark><strong>Prior State Values</strong> supplied to a row are claims about earlier writes. Their consistency, including any read-side ranges omitted locally, depends on the completed global memory argument in Section 3. The same argument supplies chronological ordering and delegation matching; a chunk does not establish those guarantees independently.</mark>

### Contributions to global arguments

_Describe the register, RAM, PC, lookup, and delegation values emitted by the chunk
for later cross-chunk aggregation._

### Local lookups and range checks

_Describe decoder membership, fixed semantic tables, limb range checks, timestamp
range checks, and how their local claims are closed._

- <mark><strong>Lookup Channels</strong> separate generic tuple membership from 16-bit and 19-bit timestamp-limb ranges. The generic setup concatenates the circuit's fixed semantic tables and program decoder table, padded to the trace capacity. Tuples share a fixed width, with zero padding and a table identifier when distinct table classes coexist. The range tables are fixed virtual polynomials containing the respective integer ranges and padding zeros. Queries use the same encoding as their table; ordinary queries have coefficient 1, while decoder queries have coefficient execute.</mark>

- <mark><strong>LogUp Multiplicities</strong> are witness columns aligned with the lookup tables. Honest multiplicities count the contributing queries at each table entry. For a channel with queries q, contribution coefficients a(q), table rows T[i], and multiplicities m[i], the required identity is Σ_q a(q)/(β + enc_α(q)) − Σ_i m[i]/(β + enc_α(T[i])) = 0. Here enc_α(t) = Σ_j α^j × t[j], and α and β are extension-field challenges drawn after commitment of the queries and multiplicities. Honest counts are embedded in the base field; the channel's query bound must prevent multiplicity wraparound. The circuit represents the identity through numerator/denominator pairs, completed as described in Section 5.</mark>

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

- <mark><strong>Polynomial Representations</strong> associate each column of 2^k rows with a multilinear polynomial whose evaluations on {0,1}^k are the column entries. Its multilinear coefficients also define a univariate polynomial by assigning coefficient index i to X^i; LDE evaluations use this univariate encoding on the commitment domain. A random multilinear evaluation is therefore distinct from a trace-row query or an LDE evaluation. Memory, witness, and nonvirtual setup columns are committed; intermediate circuit values are derived, and virtual setup evaluations are computed by the Verifier.</mark>

### GKR and Sumcheck

_Describe the layered claim, the sequence of reductions, batching, and the claim
that remains at the end of GKR._

- <mark><strong>Constraint Aggregation</strong> combines local residuals with transcript-derived coefficients and tests their equality-weighted sum through Sumcheck. The equality weights select a random multilinear evaluation of the row residuals. Constraint claims have expected value zero; other circuit relations establish their claimed outputs, including lookup fractions and memory products. Random batching and evaluation points bound the probability that violations cancel, rather than ruling out cancellation algebraically. Each required output must participate in the corresponding local or global completion check.</mark>

- <mark><strong>GKR and Sumcheck</strong> reduce output and zero-constraint claims layer by layer to evaluations of the circuit inputs. Each Sumcheck round checks the prescribed sum over 0 and 1, including any factored equality weight, absorbs a polynomial of the prescribed maximum degree, and samples a challenge determining the next evaluation claim. The final check evaluates the layer relation at the resulting point. Repeated reductions reach the committed or verifier-computed base polynomials.</mark>

### Lookup and global-argument handoffs

_Describe how local lookup products and memory-like grand-product outputs are bound
to the same committed chunk._

- <mark><strong>Fraction Reduction</strong> combines (N0,D0) and (N1,D1) into (N0 × D1 + N1 × D0, D0 × D1), preserving their rational sum while reducing the number of row positions. GKR authenticates these reductions back to the chunk's inputs. The Verifier combines the terminal pairs for each lookup channel and requires accumulated numerator zero and accumulated denominator nonzero. Zero denominators cause rejection, including on inactive queries.</mark>

### WHIR polynomial commitment proof

_Describe how WHIR proves the remaining polynomial evaluation or proximity claims
and what verifier inputs bind it to GKR._

- <mark><strong>Terminal Evaluation Claims</strong> identify the base polynomials, a common multilinear evaluation point, and their claimed values. WHIR authenticates the committed-column claims under the selected polynomial encoding and commitment layout. Virtual setup claims are checked against their fixed definitions. Intermediate values are bound through the preceding GKR relations and do not require separate commitments.</mark>

- <mark><strong>WHIR Verification</strong> establishes the batched opening claims and proximity to the configured low-degree encoding through folding, Sumcheck reductions, Merkle-authenticated queries, and final polynomial checks. Its inputs are the commitments and terminal evaluation claims from the same chunk proof. The selected security configuration fixes the folding schedule, query counts, degree bounds, and proof-of-work requirements; acceptance requires every configured check to pass.</mark>

### Transcript and Fiat-Shamir order

_Describe the important commitment, absorption, challenge, proof-of-work, and
opening order, emphasizing Airbender-specific choices._

- <mark><strong>Shared Memory Challenges</strong> are derived from the whole-execution transcript, binding final-state data and the ordered participating memory commitments and their context. Every chunk uses these external challenges, and the full-statement Verifier reconstructs their derivation and checks equality. Lookup challenges are instead sampled separately within each chunk after its setup, memory, and witness commitments, including multiplicity columns. The chunk transcript also binds the supplied external memory challenges.</mark>

### Chunk-proof acceptance

_Summarize the checks that make one GKR, Sumcheck, and WHIR proof an accepted proof
of the selected chunk relation._

- <mark><strong>Proof Interpretation</strong> follows the selected verifier format's prescribed sequence of words, field elements, commitments, and protocol messages. In the machine nondeterminism stream, field-element reads reduce supplied words into the base field, so distinct word encodings may denote the same field value. A chunk Verifier consumes its scheduled proof data within a stream that can contain further chunks. Whole-proof exhaustion remains to be specified at the enclosing format boundary; the streaming chunk interface provides no end-of-stream check.</mark>

### Recursive verification as machine execution

_Explain that recursion proves an execution of a verifier program under the same
machine-and-chunk architecture._

- <mark><strong>Recursive Layer Outputs</strong> are sixteen words returned by a full-statement verifier program: eight application-result words and eight recursion-chain words. The next layer proves that program's execution, including verification of the supplied inner proof. Acceptance binds the execution to the intended verifier program and its successful termination point. The base layer initializes the chain; continuation layers authenticate and propagate the inner result and chain.</mark>

- <mark><strong>Recursion History</strong> uses the configured hash variant to derive an end-parameter digest E from the final PC, padded to sixteen words, followed by the ordered setup commitments. The base chain is H(0^8 ∥ E). A continuation authenticates a supplied preimage against the incoming chain hash, preserving that hash when the latest E equals the current end-parameter digest, or updating it to H(previous_hash ∥ E) otherwise. Terminal acceptance checks the chain against the intended application and verifier sequence. Consecutive repetitions are compressed, so the chain does not count recursion depth.</mark>

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
