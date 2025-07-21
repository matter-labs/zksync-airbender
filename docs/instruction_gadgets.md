# Instruction Gadget Circuits

*ZK-Sync Airbender – Core circuits *

**every RISC-V instruction circuit** found under `cs/src/machine/ops`.  .
---

## Reading Conventions

* **Gadget** – synonym for “instruction circuit implementation”.  A gadget consumes decoded operand variables and produces *state diffs* (changes to registers, memory, CSR, …).
* **Lookup Table (LUT)** – a pre-computed table proved via a lookup constraint.  We rely on different tables for byte-wise Boolean ops, multiplication, division, etc.
* **`OptimizationContext`** – a helper passed into every gadget that deduplicates identical lookups and merges per-byte relations, thus decreasing total constraint count.

Every gadget follows roughly the same shape:

1. Validate pre-conditions (range checks, architectural invariants).
2. Append lookup relations or algebraic constraints that implement the instruction.
3. Selectively emit traps/exceptions.
4. Return a `CommonDiffs` struct describing the effect on the architectural state.

---

## Gadget Catalogue

### 1. `add_sub.rs` – Add / Subtract Family

Handles `ADD`, `ADDI`, `SUB`, plus sign/zero-extended variants used by the RV32I subset.

Highlights:

* Uses one 32-bit adder gadget shared between addition and subtraction (negating the second operand for SUB).
* Detects arithmetic overflow and raises the appropriate trap when **M-mode** compatibility is enabled.
* Constant folding path: immediate additions with constant zero are optimised away at compile time to save constraints.

### 2. `binops.rs` – Boolean Binary Ops

Implements `AND`, `OR`, `XOR` (and immediate forms).

* Each byte pair of the operands is looked up in the `TableType::{And, Or, Xor}` LUTs.
* The lookup itself enforces that the bytes are in `[0,255]`, hence earlier decomposition can skip explicit range checks.
* Four byte results are recombined into two 16-bit limbs to form the resulting register value.

### 3. `shift.rs` – Logical & Arithmetic Shifts

Covers `SLL`, `SRL`, `SRA` (plus immediates `SLLI`, `SRLI`, `SRAI`).

* Shifts > 31 are masked to 5 bits as per the spec.
* Logical shifts are routed to a generic barrel-shifter implemented with conditional rotations, incurring *O(log n)* constraints.
* Arithmetic right shift re-uses logical shifter then conditionally ORs the vacated bits with the sign mask.

### 4. `mul_div.rs` – Multiply / Divide / Remainder

The largest gadget in the folder – implements the complete RV32M extension: `MUL`, `MULH`, `MULHSU`, `MULHU`, `DIV`, `DIVU`, `REM`, `REMU`.

* 16×16-bit partial products reduced via Karatsuba for efficient constraint utilisation.
* Division / remainder proven through a **reciprocal-based equality**: `quot * divisor + rem = dividend` plus range and sign conditions.
* Over-flow cases like division by zero return the architecturally-defined results and optionally raise traps when `OUTPUT_EXACT_EXCEPTIONS` is enabled.

### 5. `load.rs` – Memory Loads

Handles all variants (`LB`, `LBU`, `LH`, `LHU`, `LW`).

* Computes effective address with adder gadget, then feeds it into the MMU sub-system.
* Byte/half-word loads rely on gadget-level selector logic to pick the requested offset from the fetched 32-bit word.
* Sign extension for `LB` / `LH` is done per byte via Boolean logic without introducing extra range checks.

### 6. `store.rs` – Memory Stores

Analogous to `load.rs` but writes back to memory.

* Implements byte-enable mask logic to update only the requested bytes of the 32-bit word.
* Uses `RD_STORE_LOCAL_TIMESTAMP` to coordinate with the MMU and avoid timestamp collisions.

### 7. `conditional.rs` – Conditional Branches

Includes `BEQ`, `BNE`, `BLT`, `BLTU`, `BGE`, `BGEU`.

* Compares operands with either equality or signed/unsigned less-than gadget.
* Branch taken/not-taken flag is ANDed with the gadget’s `exec_flag` so that subsequent state updates are skipped when the instruction is not executed.
* PC update logic returns a `NextPcValue::Jump(offset)` diff when the branch is taken.

### 8. `jump.rs` – Jumps & Links

`JAL` and `JALR`.

* Computes return address (`pc + 4`) and writes it to `rd`.
* For `JALR`, enforces that the least-significant bit of the target address is zero as required by the spec.

### 9. `lui_auipc.rs` – Upper-Immediate Constructors

Implements `LUI` and `AUIPC`.

* `LUI` simply shifts the 20-bit immediate left by 12.
* `AUIPC` adds that value to the current `pc`.

### 10. `csr.rs` – Control-and-Status Registers

Implements `CSRRW`, `CSRRS`, `CSRRC` and their immediate forms.

* Reads/Writes go through the CSR device; side-effects (e.g. privilege escalation) are encoded as traps.
* Immediate zero optimisation avoids unnecessary CSR reads when the mask is zero.

### 11. `mop.rs` – Memory Ordering Primitives

Currently covers `FENCE` and `FENCE_I` with placeholders for future atomics.

* Proves that all in-flight memory ops are completed before continuing (modelled via a timestamp monotonicity constraint).

### 12. `common_impls/`

Shared helper gadgets used by multiple instruction families, e.g. sign extension logic or optimised byte decomposition.

