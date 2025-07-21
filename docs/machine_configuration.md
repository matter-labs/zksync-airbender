# Machine Configuration Documentation for zkSync Airbender

zkSync Airbender is implemented with multiple machine configurations. This is a distinct sets of RISC-V instruction support and parameters to optimize the proving circuit for different use cases.

Each configuration is defined in the `cs/src/machine/machine_configurations`. Despite differences in supported features, all configurations share the same design: a 32-bit RISC-V execution model (RV32I base, with optional M extension for multiplication/division + precompiles) running in machine mode with a fixed fetch-decode-execute loop enforced every cycle.

We use a Mersenne prime field (2³¹−1) for arithmetic in constraints, which influences how 32-bit values are represented and checked. Its the best that can we get for u32 bit value. Mersenne prime covers 31 bits so to represent u32, you need to use two separate elements.  

All 32 general purpose registers are memory mapped. They reside in a reserved region of RAM rather than as separate circuit wires. Only minimal processor state (like the program counter) is kept as explicit state between cycles. All other state transitions (register updates, memory writes, etc.) are handled via the unified RAM consistency logic.

---

## No Exceptions / Trusted Code

Every configuration here is a **no-exceptions** variant, meaning the VM does not implement trap handling. Instead, it assumes that no illegal or unsupported instructions, misaligned accesses, or other trap conditions will occur ("trusted code"). If such a condition did occur, there is no alternate execution path, the constraints would simply become unsatisfiable, causing the proof to fail.

In practice, the bytecode is statically verified to use only supported instructions and aligned memory accesses.

This design was chosen to avoiding the overhead of modeling trap handling in the circuit.

All configurations set `OUTPUT_EXACT_EXCEPTIONS = false` to indicate that exceptions are not recorded in final state.

Likewise, `ASSUME_TRUSTED_CODE` is set to `true` for these configs, reflecting that the circuit does not include logic to gracefully handle invalid instructions at runtime. It assumes the instruction decoder’s “invalid” flag is never raised.

Every instruction bit pattern that does not correspond to a supported operation is marked **invalid** by the decoder, and under the trusted-code assumption this invalid-case flag can be constrained to never be 1 during execution. In other words, all executed opcodes must fall into the defined set of instructions for the given configuration.

The decode stage uses a fixed lookup table over the 32-bit opcode space to enforce this: any combination of bits not recognized by the machine maps to an invalid-opcode flag, and with trusted code we require this flag to be zero on every cycle.

This ensures that only legal opcodes propagate through the execution logic, and is critical for security since we don’t model traps.

Memory accesses are likewise constrained to be aligned to their operand size (e.g. word-aligned for 32-bit loads/stores). Unaligned accesses are disallowed by design to simplify the circuit, relying on the compiler to only perform aligned operations.

---

## ROM and RAM Layout

All configurations use a ROM for bytecode storage (`USE_ROM_FOR_BYTECODE = true`). The program code is pre-loaded into a designated read-only memory region, and instructions are fetched from this ROM region on each cycle, rather than from the general-purpose RAM.

In the circuit, the ROM is handled via a fixed-size lookup table that maps each valid instruction address to the corresponding 32-bit instruction, with out-of-range addresses mapping to a special **UNIMP** (unimplemented) opcode. The ROM size is a power-of-two bound determined by configuration.

The choice of 2^30 bytes RAM size is deliberate: it fits within the 31-bit field (since 2^30 < 2^31−1), allowing memory addresses to be represented as single field elements. This reduces circuit complexity compared to a full 32-bit address space, which would exceed the field size and require multi-element address representation.

Internally, addresses are 30-bit values, and the ROM address space is defined by splitting the 30 bits into two parts (16 lower bits and the rest upper bits) for table indexing. The constraint system materializes a ROM table of size equal to the maximum number of 4-byte words in the ROM and populates it with the program’s instructions, padded out with `UNIMP_OPCODE` for unused entries. This ensures that every possible PC address either yields a valid instruction or an UNIMP (which would make the execution invalid if hit).

The PC is initialized to the program’s entry point (typically address 0 in ROM) as part of the initial state, and each cycle the PC update logic either increments the PC by 4 or sets it to a jump/branch target.


## Configuration-Specific Details

Each machine configuration defines:

* **A specific `State` type** (implementing `Machine::State` and `BaseMachineState`) which encapsulates the machine’s architectural state (program counter, etc.). In these configurations, the state typically includes only the PC and perhaps a minimal set of status flags, since general registers are externalized to RAM.
* **A list of supported opcodes** (`Machine::all_supported_opcodes()`) covering every instruction the machine can execute. Any instruction not in the supported list is treated as invalid by the decoder and, as mentioned, will make the proof invalid in these no-exception models.
* **Definitions of used tables and constants** that parameterize the constraint system (`Machine::define_used_tables()`). Common tables include range checks, bitwise truth tables, decoder tables, etc.
* **A state-transition function** (`Machine::describe_state_transition`) which builds the constraints for one execution step. This encapsulates the fetch-decode-execute loop and applies diffs to form the next state.

### Full ISA (No Exceptions) – `full_isa_no_exceptions.rs`

Purpose: This configuration implements the **Full Kernel Mode** of Airbender, supporting the complete 32-bit RISC-V instruction set (RV32I base plus the RV32M multiplication/division extension) **without** any additional custom features or exception handling logic. It is intended for proving general-purpose kernel code (for example, the zkSync OS) that requires the full range of standard RISC-V operations while assuming *trusted* code that never triggers traps.

By omitting both *delegation* instructions and exception modelling, this configuration represents the **simplest fully-featured RISC-V machine** in the Airbender suite: every canonical integer instruction is available, but the circuit trusts the program to be self-contained and deterministic.

---

#### Key Types & Constants

* **State type** – a minimal struct that only keeps the program counter (`pc`). All 32 architectural registers live in memory, reads/writes are performed via memory diffs each cycle.
* `ASSUME_TRUSTED_CODE = true` and `OUTPUT_EXACT_EXCEPTIONS = false` – traps are not modelled, so any illegal condition simply makes constraints unsatisfiable.
* `USE_ROM_FOR_BYTECODE = true` – instructions are fetched from the fixed ROM lookup-table each step.
* No CSR usage: standard CSR opcodes (`CSRRW`, `CSRRS`, etc.) are *not* in the supported list. Access to the custom non-determinism CSR `0x7C0` is disallowed.

---

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
The last one operations are among the more complex ones to encode in constraints.
---

#### Constraint Logic Overview

1. **Fetch** – PC must be 4-byte aligned and within ROM bounds; the instruction word is obtained via the ROM lookup table.
2. **Decode** – Boolean flags from the decoder table classify the instruction; invalid combinations are asserted to be zero (trusted code).
3. **Operand preparation** – Source register values are read from RAM; when signed semantics are required, the `RegisterDecompositionWithSign` helper provides sign bits.
4. **Execute** – The dedicated `MachineOp::apply` implementation for each opcode adds constraints that compute the result and, where relevant, memory diffs (loads/stores) or register diffs.
5. **State update** –
   * Apply at most one RAM diff (register write or memory store).  
   * Enforce that `x0` remains zero.  
   * Set `pc_next` according to branch/jump logic or `pc + 4` for linear execution.
6. **Global invariants** – All executed opcodes must be in the supported set; all addresses must be within the RAM range and properly aligned, divide-by-zero is disallowed by the trusted-code premise.

---

#### When to Use

`FullIsaNoExceptions` is the go-to configuration for proving fully-featured, deterministic RISC-V binaries that **need** the M extension but **do not** rely on delegation, syscalls, or trap handling. It provides a faithful model of a standard RV32IM core while keeping the constraint system lean by excluding exception paths.

---

### Full ISA with Delegation (No Exceptions) – `full_isa_with_delegation_no_exceptions.rs`

Purpose: This configuration extends the *Full ISA (No Exceptions)* model by enabling **delegation** through controlled CSR (Control & Status Register) accesses. It targets kernel-level programs that need to invoke pre-compiled cryptographic gadgets or inject non-deterministic witness data during execution.

In Airbender, delegation is exposed via a **single custom CSR at address `0x7C0`** (often referred to as `Mcustom`). A CSR read/write to this address serves as a call-out to an external proof or circuit (e.g. Blake2s hashing, recursive proof verification). While the core VM does **not** compute those operations itself, it constrains their inputs/outputs and relies on a companion circuit to prove correctness.

---

#### Key Types & Constants

* Inherits the minimal `State` struct (only `pc`), with all 32 registers resident in memory.  
* `ASSUME_TRUSTED_CODE = true`, `OUTPUT_EXACT_EXCEPTIONS = false`, `USE_ROM_FOR_BYTECODE = true` – same rationale as the base Full ISA config.
* **Delegation flags**  
  * `allow_non_determinism_csr = true`  
  * `ALLOWED_DELEGATION_CSRS = [0x7C0]` (no other CSR addresses are accepted).

---

#### Supported Instructions

Everything from *Full ISA (No Exceptions)* **plus** the CSR instruction(s) required for delegation:

* **CSR operations**  
  * `CSRRW` (and optionally `CSRRS` / `CSRRC`) when the CSR field equals `0x7C0`.  
  * Any CSR opcode targeting a different address is treated as **invalid**.
* **RV32I base & RV32M extension** – identical coverage to the previous section (loads/stores, ALU ops, branches/jumps, multiply/divide, etc.).

---

#### Delegation Mechanism

1. **Decode** – The instruction decoder recognises `CSRRW` with CSR=`0x7C0` and sets the *delegation* flag. Attempts to access other CSRs raise the *invalid* flag (disallowed under trusted code).
2. **Execute** – The `CSRRW` implementation:
   * Consumes the *source* register value (e.g. an opcode or pointer for the external gadget).
   * Produces an **unconstrained witness value** that will be written to the *destination* register.
3. **External proof** – Outside the core VM, a separate circuit verifies that the produced witness value indeed equals the result of the requested operation. During aggregation, the main proof checks that every row of the delegation table is covered by a valid proof.
4. **State update** – From the VM’s perspective `CSRRW` is a single-cycle instruction: it writes the returned value to `rd`, applies normal diffs, and increments `pc` by 4.

---

#### Security & Invariants

* Only CSR `0x7C0` is permitted. Any access to other CSR addresses makes the execution invalid.
* Each delegated call must have a matching external proof; otherwise the witness table relation fails and the overall proof is unsatisfiable.
* All original invariants (aligned accesses, address bounds, `x0 = 0`, divide-by-zero forbidden, etc.) remain in force.

---

#### When to Use

Choose `FullIsaWithDelegationNoExceptions` for zkSync OS or applications that:
* Require the **full RV32IM instruction set**, **and**
* Need to invoke **pre-compiled cryptographic primitives** or inject non-deterministic data via the delegation interface.


