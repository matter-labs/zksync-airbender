# Airbender 2026, Architecture

by the Matter Labs crypto team

# 1. Execution Model

**ISA**: RISCV32IM+Zicsr+Zimop with custom exceptions for a given fixed ROM/bytecode

**ISA Exceptions**: 

**ALL**: instructions containing`dst=x0` register writes are mapped to `add x0, x0, x0` which is effectively a NOP, except for JAL/JALR/CSRRW which ignore them.

**LOAD/STORE**: no misaligned word accesses, no odd-misaligned halfword accesses, no STORE to ROM address region

**FENCE/FENCE.I/ECALL/EBREAK/PrivilegedISA**: not supported

**CSR**: only CSRRW with `csr` $\in$  `[1984 (NonDeterminismReadWrite), 1991 (blake2s), 1994 (bigint), 1995 (keccakSpecial5)]` custom redefined to call precompiles or read/write NonDeterministic I/O

**MOP**: only MOP.RR.n with `n` $\in$ `[0 (add), 1 (sub), 2 (mul)]` custom redefined to native field ops

**ISA Exceptions Enforcement**: 

**SETUP**: when possible, exceptions are excluded from decoder lookup tables during fixed bytecode/ROM preprocessing

**RUNTIME**: exceptions are mapped to unsatisfiable constraints

**Fixed ROM/Binary**: 4MB, fixed at setup/preprocessing, padded with `add x0, x0, x0`

**Runtime**: max 2^36 cycles

**ZKVM Proving Profiles**: 

`IMStandardIsaConfigUnsignedMulDivOnly`: no signed MUL/DIV/REM ops (not needed in our ZKsync-OS binary). uses unrolled family circuits (see Section 2)

`ReducedMachineWithDelegation`: no MUL/DIV/REM ops, no subword LOAD/STORE (not needed in our ZKP verifier binaries), and only blake precompile delegation/calls or NonDeterminism CSR reads/writes. uses multiple unrolled family circuits or a single unified family circuit family circuit (see Section 2), along with a blake circuit.

**ZKVM Machine State**: defined by global memory argument (see Section 3). witness traces and public setups are added to satisfy constraints.

# 2. Segmentation

**Unrolled Opcode Families**: when not recursing (or initial recursion layers), collect executed cycles by opcode family (each is a circuit)

`add_sub`: covers ADD/ADDI/SUB/AUIPC/LUI/MOP.RR/CSRRW(Delegation or Nondeterminism)

`binary_shifts`: covers AND/ANDI/OR/ORI/XOR/XORI/SLL/SLLI/SRL/SRLI/SRA/SRAI

`jump_branch_slt`: covers JAL/JALR/BEQ/BNE/BLT/BLTU/BGE/BGEU/SLT/SLTI/SLTU/SLTIU

`mem_word_only`: covers LW/SW

`mem_subword_only`: covers LH/LHU/LB/LBU/SH/SB

`mul_div`: covers MUL/MULH/MULHU/MULHSU/DIV/DIVU/REM/REMU (* signed ops are disabled by our default proving profiles, but can be manually re-enabled)

`delegation/bigint_with_control`: fulfills CSRRW requests for bigint ops

`delegation/blake2_round_with_extended_control`: fulfills CSRRW requests for blake2s

`delegation/keccak_special5`: fulfills CSRRW requests for Keccak 

**Unified Opcode Family**: when recursing (especially deepest recursion layers), all cycles map to these families

`reduced_machine_circuit_with_preprocessed_bytecode`: covers all opcodes from`add_sub, binary_shifts, jump_branch_slt, mem_word_only`. selects them via disjunction.

`delegation/blake2_round_with_extended_control` : also used by recursion

**Global Inits/Teardowns**: a special circuit covers the initialisation and final “teardown” of the global memory argument (according to “2 Shuffles Make a RAM” paper) when executing in Unrolled recursion mode, but when in Unified mode it is integrated into the unified circuit.

**Circuit Chunks**: a group of family cycles is further split into chunks of size 2^20 through 2^24. one chunk is usually reserved for global inits/teardowns.

**Circuit Chunks Padding**: 

all: inject inactive cycles (through an `execute`boolean masking flag) which disable reads/writes to our global memory and state permutation and delegation permutation argument.

**Precompile Delegations**: 

**Calls**:`add_sub`or`reduced_machine_circuit_with_preprocessed_bytecode`chunks use global memory and state permutation and delegation permutation argument to issue “empty” writes at fixed (uninitialised) “delegation registers” using unique timestamps

**Fulfillments**: `delegation/*` chunks issue empty global reads at fixed “delegation registers”

# 3. Interaction

**Global Memory Argument**: our global memory argument supports reading and writing to registers or RAM (up to 32bits address range + 1 `type` selector field),  according to the “2 Shuffles Make a RAM” paper. Tuples are of the form `(type: {Register = 0, RAM = 1, PC = 2}, addr: u32, ts: u38, value: u32)` split into limbs where necessary for range checking. Global randomness is drawn after having committed to a “memory” trace Merkle tree, whose leaves are computed in advance by a custom RISCV32 simulator before any proving, chunking, or other witness generation can begin.

**Global Memory Initialisation**: 1GB of RAM address values are initialised to 0, as well as all 32 RISCV32 base registers, through the Global Inits/Teardowns proven circuit chunk (finalisation of the argument by fulfilling final reads is also covered by the same circuit and injection of public inputs by the verifier into the accumulator). A single`type=2` entry is initialised to `write_addr=INIT_PC` and `write_timestamp=INIT_TS=4` and finalised to `read_addr=FINAL_PC` and `read_timestamp=INIT_TS+TOT_CYCLES*4` with`INIT_PC` and `TOT_CYCLES` public inputs. The  finalisation of the 32 RISCV32 register values also uses public inputs, for the purposes of the proof recursion pipeline.

**ROM Region**: the lowest 4MB of the RAM address space in the global memory argument are reserved for reading the ROM. Since ROM addresses are initialised with zeros, Loads from ROM are logically enforced via preprocessed bytecode lookup tables, in parallel with concrete (and ignored) reads/writes to fulfill the global memory argument .

**Global State Permutation**: we use `type=2` address space to identify the global (PC, TIMESTAMP) state permutation. Every non-delegation circuit chunk cycle reads a tuple `(READ_PC, READ_TS)` and updates it with `(NEXT_PC, READ_TS+4)` with `NEXT_PC` defined according to appropriate RISCV32 semantics embedded in the circuit.

**Global Delegation Permutation (Bus)**: global memory argument registers beyond address=31 are not initialised or finalised. When an`add_sub`or`reduced_machine_circuit_with_preprocessed_bytecode` chunk cycle needs to issue a delegation call it issues a read/write tuple with `read_addr=CSR_ID, read_timestamp=0, read_value=0, write_addr=CSR_ID, write_timestamp=READ_TS+LOCAL_TS, write_value=0`, where `READ_TS` is the timestamp taken from the cycle’s state permutation access, and `LOCAL_TS` is the memory access offset for that cycle. The delegation circuit chunk’s cycle issues a mirrored tuple pair where read and write are swapped (enforced via constraints except for `read_timestamp`), thus closing the permutation. 

**Lookup Arguments**: we have 3 separate lookup arguments (via the “LogUp” paper), split in order to avoid overflowing multiplicity counting. The arguments are local, they are enforced at the chunk level by the verifier.

`Generic`: used for all generic lookups, including the decoder lookup

`RangeCheck16`: used for nearly every word in the machine (split into two `u16` limbs)

`TimestampRangeCheck`: used for timestamps (split into two `u19` limbs)

# 4. Individual Proofs

**Circuit Compiler**: circuits are fixed according to families from Section 2 and profiles from Section 1. To construct a circuit, algebraic Sumcheck gates are placed manually starting from the base layer, and after a few layers we begin the process of compressing all tuples that participate in the Global memory argument or Local lookup arguments. The number of proving chunks used by each circuit is determined statically according to the best performance/compression ratio of our recursion chain (see Section 5). All circuits encode uniform constraints at the row-level during the “main” GKR layers, and then the rows get compressed during the “compression” layers (so that memory and lookup arguments may be completed by the verifier using the accumulated outputs). Each row of the circuit at the “base” GKR layer encodes all witness data required to define and constrain a RISCV execution cycle, split across multiple columns to collect the entire witness data, which can be encoded as multilinear witness polynomials over the boolean hypercube.

**IOP**: GKR, with batched Sumchecks of max gate degree 2. Gate outputs either fall into global memory argument or local logup arguments, or zerocheck constraints. the number of base layer witness polynomials ranges from ~40 for opcode family circuits to several hundred for delegation precompile circuits. Witness at the base layer are encoded into a 31-bit prime field, and at any layer which requires randomness for additional soundness values are encoded as quartic field extension. The number of layers for a given circuit is roughly `log2(chunk_size)` plus 1 to 5 layers to compose the quadratic circuit constraints. No Zero-Knowledge, Non-Interactive via Fiat-Shamir.

**PCS**: WHIR, with base layer batching, targeting 100 bits of security (with 80 bits also available) and <300kB individual chunk proof size. No Zero-Knowledge, Non-Interactive via Fiat-Shamir.

**Commitment Scheme**: Merkle Trees based on Blake2s (usually with the reduced rounds variant of the compression function, as specified in the Blake3 spec) or Keccak256.

**Memory and Permutation Arguments**: “Two Shuffles Make a RAM” for the global memory/state/delegation argument and “LogUp” for the 3 local lookup arguments. See Section 3.

# 5. Recursion Structure

**Binaries**: we use a linear chain that progresses from many unrolled to one or two unified recursion chunks (depending on security parameters)

`Base`: the first proven program which encodes its own meaningful semantics via output and accepting/rejecting final program counter

`UnrolledVerifier`: intermediate layer recursive verification program which can be configured with `PROFILE_TYPE := {UnrolledStandard, UnrolledReduced}` based on whether we are verifying recursion or base.

`UnifiedVerifier`: outer layer recursive verification program which can be configured with `PROFILE_TYPE := {UnrolledReduced, UnifiedReduced}` based on whether we want maximum recursion proving speed or size compression.

**Proof Public Inputs**:

`PROFILE_TYPE`: helps the Verifier select the appropriate circuits/constraints for verification

`TS`: the final timestamp at which execution ended

`PC`: the final program counter at which execution ended

`CAPS := (SETUP_CAPS, INITS_AND_TEARDOWNS_CAPS*)`: caps used for verification (constraints related to lookup tables) and to identify binaries. the unified verifier does not require separate caps for inits/teardowns because it does not need a separate circuit for global memory argument initialisation (see Sections 3 and 2).

`PREV_PREIMAGE := (PREV_PREV, PREV_PARAMS)`: hash-chain related information

`REGS := (BASE_OUT, PREV)`: program output placed in the registers x0..x31 at the end of execution, and used to validate the hash-chain.

**Verifier($\pi$)**:

```jsx
// verify the GKR+WHIR proof
// NB: TS, PC, REGS are all used to complete the global memory argument
pi.Verify(PROFILE_TYPE, TS, PC, CAPS, REGS)

// identify PREV_PARAMS for convenience
PREV == hash(PREV_PREIMAGE) if !BASE else 0..0

// force successful PC and binary-identifying CAPS into PARAMS
PARAMS := hash(PC, CAPS)

// force PARAMS into hash-chain
NEXT := hash(PREV, PARAMS) if (PREV_PARAMS != PARAMS or BASE) else PREV

// validate success or propagate hash-chain
REGS(x0..x31) <- (BASE_OUT, NEXT) if !FINAL else NEXT == EXPECTED_HASH_CHAIN

// base program output is used to validate state transition on L1
// NB: obviously, this primitive is absent from the rust aforementioned verifiers
//     but it clarifies the role of BASE_OUT during the verification process
if L1: L2StateTransition(BASE_OUT, L1_CALLDATA)
```