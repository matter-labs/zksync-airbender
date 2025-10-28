# Machine Configuration Documentation for Airbender

ZKsync Airbender is implemented with multiple machine configurations. These are distinct sets of RISC-V instruction support and parameters designed to optimize the proving circuit for different use cases.

Each configuration is defined in the [`cs/src/machine/machine_configurations`](../cs/src/machine/machine_configurations). Despite differences in supported features, all configurations share the same design: a 32-bit RISC-V execution model, the RV32I base with optional M extension for multiplication/division and precompiles, running in machine mode with a fixed fetch-decode-execute loop enforced every cycle.

We use a Mersenne prime field ($2^{31}$−1) for arithmetic in constraints, which influences how 32-bit values are represented and checked. As the Mersenne prime covers 31 bits, representing the 32-bit values that we use requires two separate elements.  

In the constraint system, every register read or write is represented as a RAM access with a special `is_register == 1` tag and the 5-bit register index supplied in the address field. The `is_register` tag allows register accesses participate in the global memory consistency argument alongside RAM accesses while effectively giving registers their own small address space disjoint from RAM itself. Only minimal processor state (such as the program counter) is carried explicitly between cycles.

---

## No Exceptions / Trusted Code

Every configuration here is a **no-exceptions** variant, meaning the VM does not implement trap handling. Instead, it assumes that no illegal or unsupported instructions, misaligned accesses, or other trap conditions will occur ("trusted code"). If such a condition did occur, there would be no alternative execution path; the constraints would simply become unsatisfiable, causing the proof to fail.

In practice, the bytecode is statically verified to use only supported instructions and aligned memory accesses. This design was chosen to avoid the overhead of modeling trap handling in the circuit.

All configurations set `OUTPUT_EXACT_EXCEPTIONS = false` to indicate that exceptions are not recorded in the final state. Likewise, `ASSUME_TRUSTED_CODE` is set to `true`, reflecting that the circuit does not include logic to gracefully handle invalid instructions at runtime. It assumes the instruction decoder's “invalid” flag is never raised.

Every instruction bit pattern that does not correspond to a supported operation is marked as **invalid** by the decoder, and under the trusted-code assumption, this invalid-case flag can be constrained to never be `1` during execution. In other words, all executed opcodes must fall into the defined set of instructions for the given configuration.

The decode stage uses a fixed lookup table over the 32-bit opcode space to enforce this: any combination of bits not recognized by the machine maps to an invalid-opcode flag. With "trusted code", we require this flag to be zero on every cycle.

This ensures that only legal opcodes propagate through the execution logic, and is critical for security since we don't model traps.

Memory accesses are likewise constrained to be aligned to their operand size (e.g. word-aligned for 32-bit loads/stores). Unaligned accesses are disallowed by design to simplify the circuit, relying on the compiler to only perform aligned operations.

---

## ROM and RAM Layout

All configurations use a ROM for bytecode storage (`USE_ROM_FOR_BYTECODE = true`). The program code is pre-loaded into a designated read-only memory region, and instructions are fetched from this ROM region on each cycle, rather than from the general-purpose RAM.

In the circuit, the ROM is handled via a fixed-size lookup table that maps each valid instruction address to the corresponding 32-bit instruction, with out-of-range addresses mapping to a special **UNIMP** (unimplemented) opcode. The ROM size is a power-of-two bound determined by configuration.

The choice of $2^{30}$ bytes RAM size is deliberate: it fits within the 31-bit field (since $2^{30}$ < $2^{31}$−1), allowing memory addresses to be represented as single field elements. This reduces circuit complexity compared to a full 32-bit address space, which would exceed the field size and require multi-element address representation.

Internally, addresses are 30-bit values, and the ROM address space is defined by splitting the 30 bits into two parts (16 lower bits and the rest upper bits) for table indexing. The constraint system materializes a ROM table of size equal to the maximum number of 4-byte words in the ROM and populates it with the program's instructions, padded out with `UNIMP_OPCODE` for unused entries. This ensures that every possible PC address either yields a valid instruction or an UNIMP, which would make the execution invalid if hit.

The PC is initialized to the program's entry point, typically address `0` in ROM, as part of the initial state, and each cycle the PC update logic either increments the PC by `4` or sets it to a jump/branch target.


## Configuration-Specific Details

Each machine configuration defines:

* **State struct** – each machine configuration provides its own struct that implements both `Machine::State` and `BaseMachineState`.  This struct holds only the architectural context that must persist across cycles—typically just the program counter (`pc`) and, in some variants, a couple of status bits.  The 32 general-purpose registers are **not** stored here; they reside in RAM and are accessed via `is_register` memory queries.
* **A list of supported opcodes** (`Machine::all_supported_opcodes()`) covering every instruction the machine can execute. Any instruction not in the supported list is treated as invalid by the decoder and, as mentioned, will make the proof invalid in these no-exception models.
* **Definitions of used tables and constants** that parameterize the constraint system (`Machine::define_used_tables()`). Common tables include range checks, bitwise truth tables, decoder tables, etc.
* **A state-transition function** (`Machine::describe_state_transition`) which builds the constraints for one execution step. This encapsulates the fetch-decode-execute loop and applies diffs to form the next state.

---

### Full ISA (No Exceptions) – [`full_isa_no_exceptions.rs`](../cs/src/machine/machine_configurations/full_isa_no_exceptions)

**Purpose:** This configuration implements the **Full Kernel Mode** of Airbender, supporting the complete 32-bit RISC-V instruction set –RV32I base plus the RV32M multiplication/division extension– **without** any additional custom features or exception handling logic. It is intended for proving general-purpose kernel code, for example, the zkSync OS, which requires the full range of standard RISC-V operations while assuming *trusted code* that never triggers traps.

By omitting both *delegation* instructions and exception modelling, this configuration represents the **simplest fully-featured RISC-V machine** in the Airbender suite: every canonical integer instruction is available, but the circuit trusts the program to be self-contained and deterministic.

#### Key Types & Constants

* `ASSUME_TRUSTED_CODE = true` and `OUTPUT_EXACT_EXCEPTIONS = false` – traps are not modelled, so any illegal condition simply makes constraints unsatisfiable.
* `USE_ROM_FOR_BYTECODE = true` – instructions are fetched from the fixed ROM lookup-table each step.
* **Control & Status Register (CSR) support** – for this configuration, we support `CSRRW` but not `CSRRS`, `CSRRC`, or CSR immediate variants. The system includes the CSR opcode infrastructure for potential future extensions, but currently, all CSR operations are unnecessary due to our Trusted Code Machine Mode design. Access to the custom non-determinism CSR `0x7C0` is disallowed in this configuration.

#### Supported Instructions

This configuration’s `all_supported_opcodes()` returns **every** RV32I and RV32M opcode:

* **RV32I base**
  * Loads: `LB`, `LH`, `LW`, plus unsigned variants `LBU`, `LHU`  
  * Stores: `SB`, `SH`, `SW`  
  * ALU immediates: `ADDI`, `SLTI`, `SLTIU`, `ANDI`, `ORI`, `XORI`, `SLLI`, `SRLI`, `SRAI`  
  * ALU register-register: `ADD`, `SUB`, `SLL`, `SRL`, `SRA`, `SLT`, `SLTU`, `AND`, `OR`, `XOR`  
  * Control-flow: `LUI`, `AUIPC`, unconditional `JAL`, register jump `JALR`, conditional branches `BEQ`, `BNE`, `BLT`, `BGE`, `BLTU`, `BGEU`  
  * (Optionally) system `ECALL` / `EBREAK` are marked **invalid** under the trusted-code assumption and therefore must never appear.
* **RV32M extension** – multiplication/division:
  * Multiply: `MUL`, `MULH`, `MULHU`, `MULHSU`  
  * Division / Remainder: `DIV`, `DIVU`, `REM`, `REMU`

The operations in the RV32M extension are among the most complex to encode in constraints.

#### Constraint Logic Overview

1. **Fetch** – PC must be 4-byte aligned and within ROM bounds; the instruction word is obtained via the ROM lookup table.
2. **Decode** – Boolean flags from the decoder table classify the instruction; invalid combinations are asserted to be zero (trusted code).
3. **Operand preparation** – Source register values are read from RAM using the `is_register` memory query mechanism. All operands are processed through `RegisterDecompositionWithSign::parse_reg()`, which decomposes the 32-bit value into bytes and extracts the sign bit for operations requiring signed arithmetic.
4. **Execute** – For each opcode, the dedicated `MachineOp::apply` implementation adds constraints that compute the result and, where relevant, memory diffs (loads/stores) or register diffs.
5. **State update** –
  * Apply at most one RAM diff (register write or memory store).  
  * Enforce that `x0` remains zero.  
  * Set `pc_next` according to branch/jump logic or `pc + 4` for linear execution.
6. **Global invariants** – All executed opcodes must be in the supported set; all addresses must be within the RAM range and properly aligned due to the trusted-code premise.

#### When to Use

`FullIsaNoExceptions` is the go-to configuration for proving fully-featured, deterministic RISC-V binaries that:
* **Need** the M extension. 
* **Do not** rely on delegation, syscalls, or trap handling. 

It provides a faithful model of a standard RV32IM core while keeping the constraint system lean by excluding exception paths.

---

### Full ISA with Delegation (No Exceptions) – [`full_isa_with_delegation_no_exceptions.rs`](../cs/src/machine/machine_configurations/full_isa_with_delegation_no_exceptions)

**Purpose:** This configuration extends the *Full ISA (No Exceptions)* model by enabling **delegation** through controlled CSR accesses. It targets kernel-level programs that need to invoke cryptographic gadgets or inject non-deterministic witness data during execution.

In Airbender, delegation is exposed via a **single custom CSR at address `0x7C0`**, often referred to as `Mcustom`. A CSR read/write to this address serves as a call-out to an external proof or circuit like BLAKE2s hashing and recursive proof verification. While the core VM **does not** compute those operations itself, it constrains their inputs/outputs and to prove correctness relies on a companion circuit, an external circuit that proves the correctness of a delegated operation.

#### Key Types & Constants

* Inherits the minimal `State` struct (only `pc`), with all 32 registers resident in memory.  
* `ASSUME_TRUSTED_CODE = true`, `OUTPUT_EXACT_EXCEPTIONS = false`, `USE_ROM_FOR_BYTECODE = true` – same rationale as the base Full ISA config.
* **Delegation flags**  
  * `allow_non_determinism_csr = true`  
  * `ALLOWED_DELEGATION_CSRS = [0x7C0]` (no other CSR addresses are accepted).

#### Supported Instructions

Everything from *Full ISA (No Exceptions)* **plus** the CSR instruction(s) required for delegation:

* **CSR operations**  
  * `CSRRW` when the CSR field equals `0x7C0`.  
  * Any CSR opcode targeting a different address is treated as **invalid**.
* **RV32I base & RV32M extension** – identical coverage to the previous section (loads/stores, ALU ops, branches/jumps, multiply/divide, etc.).

#### Delegation Mechanism

1. **Decode** – the instruction decoder recognizes `CSRRW` with CSR=`0x7C0` and sets the *delegation* flag. Attempts to access other CSRs raise the *invalid* flag  as it is disallowed under trusted code.
2. **Execute** – the `CSRRW` implementation:
   * Consumes the *source* register value (e.g. an opcode or pointer for the external gadget).
   * Produces an **unconstrained witness value** that will be written to the *destination* register.
3. **External proof** – outside the main circuit, a separate circuit verifies that the produced witness value indeed equals the result of the requested operation. During aggregation, the main proof checks that every row of the delegation table is covered by a valid proof.
4. **State update** – from the VM’s perspective, `CSRRW` is a single-cycle instruction: it writes the returned value to `rd`, applies normal diffs, and increments `pc` by 4.

#### Security & Invariants

* Only CSR `0x7C0` is permitted. Any access to other CSR addresses makes the execution invalid.
* Each delegated call must have a matching external proof; otherwise, the witness table relation fails, and the overall proof is unsatisfiable.
* All original invariants (aligned accesses, address bounds, `x0 = 0`, divide-by-zero forbidden, etc.) remain in force.

#### When to Use

Choose `FullIsaWithDelegationNoExceptions` for ZKsync OS or applications that both:
* Require the **full RV32IM instruction set**
* Need to invoke **precompiled cryptographic primitives** or inject non-deterministic data via the delegation interface.

---

### Full ISA with Delegation (No Exceptions, *No Signed MUL/DIV*) – [`full_isa_with_delegation_no_exceptions_no_signed_mul_div.rs`](../cs/src/machine/machine_configurations/full_isa_with_delegation_no_exceptions_no_signed_mul_div)

**Purpose:** This configuration is a **cost-reduced** variant of *Full ISA with Delegation (No Exceptions)*. It **removes all signed multiply, divide, and remainder opcodes** to shrink the constraint system while retaining delegation CSR support.

By ruling out the 64-bit signed-result operations (`MULH`, `MULHSU`, `MULHU`), and signed division/remainder (`DIV`, `REM`) we avoid the wide-word arithmetic gadgets that dominate gate count in the full machine.  The remaining opcodes are sufficient for most recursion and verifier binaries, which deal only with unsigned values or low-word products.

#### Key Types & Constants

* Inherits the minimal `State` struct with registers in memory (same as the other *Delegation* machine).
* `ASSUME_TRUSTED_CODE = true`, `OUTPUT_EXACT_EXCEPTIONS = false`, `USE_ROM_FOR_BYTECODE = true` – unchanged semantics: trusted code, no traps, ROM-backed bytecode.
* **Delegation flags** – identical to the full delegation machine:  
  * `allow_non_determinism_csr = true`  
  * `ALLOWED_DELEGATION_CSRS = [0x7C0]`.

#### Supported Instructions

* **RV32I base** – *all* byte/half-word/word loads & stores, ALU immediates, register-register ALU ops, branches/jumps, etc. (identical to previous configs).
* **RV32M extension (reduced)**  
  * **Kept** – `MUL` (low-word product), `DIVU`, `REMU`  
  * **Removed** – `MULH`, `MULHSU`, `MULHU`, `DIV`, `REM`
* **CSR delegation** – `CSRRW`/`CSRRS`/`CSRRC` to CSR `0x7C0` only.

Any attempt to execute one of the removed opcodes (or access a non-whitelisted CSR) makes the proof unsatisfiable under the trusted-code premise.

#### When to Use

`FullIsaMachineWithDelegationNoExceptionHandlingNoSignedMulDiv` is the recommended choice when:

* Your program **does not require signed high-word multiplication or signed division/rem** 
* You **still need delegation gadgets** such as BLAKE2s or BigInt arithmetic.
* You want **smaller proofs** – this config can shave 20-30 % gates compared to the full delegation machine, making it ideal for *recursive verifier* layers.

If the binary ever executes a signed `MUL`/`DIV`/`REM` instruction, the circuit will reject it, so compile-time filtering or static analysis of the bytecode is required.

---

### Minimal ISA (No Exceptions) – [`minimal_no_exceptions.rs`](../cs/src/machine/machine_configurations/minimal_no_exceptions)

**Purpose:** This is the **smallest, fastest-to-prove** RISC-V configuration in Airbender.  It strips the ISA down to the *essential 32-bit arithmetic and control-flow instructions* and enforces **word-aligned memory**.  All byte/half-word operations and the entire multiply/divide extension are removed, delivering a very light constraint system ideal for recursion layers or arithmetic-heavy programs that do not require complex opcodes.

#### Key Types & Constants

* Uses the same `MinimalStateRegistersInMemory` (`MinimalState`) that keeps only the program counter; all 32 registers live in RAM via the `is_register == 1` mechanism.
* `ASSUME_TRUSTED_CODE = true`, `OUTPUT_EXACT_EXCEPTIONS = false`, `USE_ROM_FOR_BYTECODE = true` – trusted code, no trap handling, ROM-backed bytecode.
* **No delegation** – the custom CSR `0x7C0` is *not* permitted in this configuration.

#### Supported Instructions

* **RV32I base (reduced)**  
  * Loads/Stores: **`LW`, `SW` only.** Byte (`LB/LBU`) and half-word (`LH/LHU`) operations together with their store counterparts are *not* supported – all memory accesses must be 4-byte aligned.  
  * ALU immediates: `ADDI`, `SLTI`, `SLTIU`, `ANDI`, `ORI`, `XORI`, `SLLI`, `SRLI`, `SRAI`.  
  * ALU register-register: `ADD`, `SUB`, `SLL`, `SRL`, `SRA`, `SLT`, `SLTU`, `AND`, `OR`, `XOR`.  
  * Control-flow: `LUI`, `AUIPC`, unconditional `JAL`, register jump `JALR`, conditional branches `BEQ`, `BNE`, `BLT`, `BGE`, `BLTU`, `BGEU`.
* **RV32M** – *entirely removed.* No `MUL`, `DIV`, or remainder opcodes.
* **Custom modular arithmetic (`MOP`)** – three compact R-type variants that operate on two 32-bit operands treated as little-endian 32-bit integers decomposed into 16-bit limbs:
  * `ADDMOD`, `SUBMOD`, `MULMOD`   
  These opcodes perform the operation modulo $2^{32}$ and write the low 32-bit result back to `rd`.
* **CSR operations** – limited to the *data-movement* variants (`CSRRW`/`CSRRWI`) for standard RISC-V CSRs; no delegation/non-determinism CSRs are accepted.

Any instruction outside this whitelist –including byte/half-word memory ops, `MUL`/`DIV`, or delegation CSR access– causes an *invalid opcode* flag, making the proof unsatisfiable under the trusted-code assumption.

#### Constraint Logic Highlights

1. **Aligned memory simplification** – since only word accesses exist, the memory-alignment checks are trivial (address \% 4 == 0) and byte-select multiplexers are eliminated.  
2. **No wide-word arithmetic** – removing signed/unsigned 64-bit multiply & divide slashes gate count and eliminates large range-check tables.  
3. **Modular arithmetic gadget** – `MOP` combines limb-level arithmetic with conditional modular reduction inside a single row, keeping the circuit tight.

#### When to Use

Choose `MinimalMachineNoExceptionHandling` when:

* Your program **only needs 32-bit word operations** and **does not perform multiplication/division or byte-level memory access**.  
* You **do not need delegation gadgets**.  
* You want the **fastest proving time and smallest proof size** – this config typically cuts >50 % of the gates compared to the full delegation machine.

It is frequently used as the **innermost recursive verifier** or for pure arithmetic kernels where byte granularity and wide-word math are unnecessary.

---

### Minimal ISA with Delegation (No Exceptions) – [`minimal_no_exceptions_with_delegation.rs`](../cs/src/machine/machine_configurations/minimal_no_exceptions_with_delegation)

**Purpose:** This configuration combines the **lean opcode set** of the *Minimal ISA* with the **delegation interface** used for heavy cryptographic primitives.  It keeps the constraint system light while still allowing a RISC-V program to call out to precompiled gadgets (BLAKE2, BigInt arithmetic, etc.) via the custom CSR `0x7C0`.

#### Key Types & Constants

* Same `MinimalStateRegistersInMemory` as the other minimal configs – registers in RAM, only PC in the state.  
* `ASSUME_TRUSTED_CODE = true`, `OUTPUT_EXACT_EXCEPTIONS = false`, `USE_ROM_FOR_BYTECODE = true`.
* **Delegation enabled**  
  * `allow_non_determinism_csr = true`  
  * `ALLOWED_DELEGATION_CSRS = [0x7C0]`

#### Supported Instructions

Identical to *Minimal ISA (No Exceptions)* **plus** delegation CSR ops:

* **RV32I (reduced)** – word-aligned `LW`/`SW`, full set of ALU immediates & register ops, branches/jumps.  
* **RV32M** – none, no multiplication/division/remainder.  
* **Custom `MOP` modular arithmetic** – `ADDMOD`, `SUBMOD`, `MULMOD`.  
* **CSR delegation** – `CSRRW`, `CSRRS`, `CSRRC`, and their immediate forms if compiled in, **only when CSR = `0x7C0`**. Any CSR access outside this address is invalid.

#### Delegation Mechanism

Exactly the same flow described for the full delegation machine: a `CSRRW` to `0x7C0` triggers a row in the delegation table, producing an unconstrained witness that a separate circuit later validates. Removing multiplication/division does **not** affect the delegation plumbing.

#### Constraint-System Footprint

Compared to the full delegation, machine this config remains small because it:
1. Keeps the aligned-memory simplifications of the minimal ISA.  
2. Excludes all wide-word multiply/divide logic.  
3. Adds only the lookup tables and wiring necessary for the delegation CSR.

The overall gate count is only slightly larger than the non-delegation minimal machine, yet it unlocks powerful cryptographic gadgets.

#### When to Use

Pick `MinimalMachineNoExceptionHandlingWithDelegation` when:

* Your code **does not require byte/half-word memory instructions or MUL/DIV**, but **does rely on delegation gadgets** (e.g., hashing, 256-bit arithmetic).  
* You need a **middle ground** between the ultra-small minimal machine and the larger full ISA delegation machine.  
* You are implementing **recursive proof layers** where the verifier binary uses delegation but otherwise avoids complex opcodes.

As always, executing an unsupported opcode or accessing a non-whitelisted CSR makes the proof unsatisfiable.
