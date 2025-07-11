## Instructions supported by the RISC-V Simulator

### RV32I (Base)

| **Instruction** | **Description** |
| --- | --- |
| `LUI` | Load upper immediate |
| `AUIPC` | Add upper immediate to PC |
| `JAL` | Jump and link |
| `JALR` | Jump and link register |
| `BEQ`, `BNE`, `BLT`, `BGE`, `BLTU`, `BGEU` | All branch types |
| `LB`, `LH`, `LW`, `LBU`, `LHU` | Byte/Half/Word loads (signed/unsigned) |
| `SB`, `SH`, `SW` | Byte/Half/Word stores |
| `ADDI`, `SLTI`, `SLTIU`, `XORI`, `ORI`, `ANDI` | Immediate ALU ops |
| `SLLI`, `SRLI`, `SRAI` | Immediate shift ops |
| `ADD`, `SUB`, `SLL`, `SRL`, `SRA`, `SLT`, `SLTU`, `XOR`, `OR`, `AND` | Register-register ALU ops |

### RV32M (Multiplication/Division Extension)

| **Instruction** | **Description** |
| --- | --- |
| `MUL`, `MULH`, `MULHSU`, `MULHU` | Multiplication (signed/unsigned variants) |
| `DIV`, `DIVU`, `REM`, `REMU` | Division and remainder (signed/unsigned) |

### CSR Instructions (Zicsr)

| **Instruction** | **Description** |
| --- | --- |
| `CSRRW`, `CSRRS`, `CSRRC`, `CSRRWI`, `CSRRSI`, `CSRRCI` | Full CSR access set |

### Delegation pre-compiles encoded via `CSRRW`

| **Delegation ID** | **Delegation Name** |
| --- | --- |
| 1985 `(0x7C1)` | blake2s |
| 1986 `(0x7C2)` | blake round function |
| 1987 `(0x7C3)` | blake round function with final xor |
| 1988 `(0x7C4)` | blake round function with state registers |
| 1989 `(0x7C5)` | mersenne ext4 fma |
| 1990 `(0x7C6)` | poseidon2 |
| 1991 `(0x7C7)` | blake2 round function with compression |
| 1992 `(0x7C8)` | mersenne ext fma indirect |
| 1993 `(0x7C9)` | u256_bigint |
| 1994 `(0x7CA)` | u256 with control |

### Explicitly Unsupported / Disabled

| **Opcode** | **Instruction / Reason** |
| --- | --- |
| `FENCE`, `FENCE.I` (0x0F) | Commented out: "nothing to do in fence, our memory is linear" |
| `SYSTEM` (funct3 = 000) | MRET, ECALL, EBREAK, WFI — code exists but commented out |
| `RV32A` (0x2F) | Atomic ops not supported: explicitly returns `IllegalInstruction` |
| `MOP` (funct7 starts with `0b1000001`) | Supported only if `Config::SUPPORT_MOPS` is enabled |

---

## Control and Status Registers (CSRs)

CSRs are special-purpose registers that control privileged state such as interrupt masks, trap vectors, and memory translation. They are accessed exclusively through the Zicsr instruction family listed above.

### Implemented Machine-Level CSRs

| **CSR Name** | **Address** | **Read** | **Write** | **Description** |
| --- | --- | --- | --- | --- |
| `mstatus` | `0x300` | ✅ | ✅ | Stored in `machine_mode_trap_data.state.status` |
| `mie` | `0x304` | ✅ | ✅ | Interrupt Enable |
| `mtvec` | `0x305` | ✅ | ✅ | Trap handler base address |
| `mscratch` | `0x340` | ✅ | ✅ | Scratch register |
| `mepc` | `0x341` | ✅ | ✅ | Exception PC |
| `mcause` | `0x342` | ✅ | ✅ | Trap cause |
| `mtval` | `0x343` | ✅ | ✅ | Trap value (faulting address/instruction) |
| `mip` | `0x344` | ✅ | ✅ | Interrupt pending |
| `satp` | `0x180` | ✅ | ✅ | Managed via `mmu.read_sapt()` / `mmu.write_sapt()` |
| `NON_DETERMINISM_CSR` | `0x7C0` | ✅ | ✅ | Custom CSR handled via `NonDeterminismCSRSource` |

### Mentioned but *Not* Implemented

| **CSR Name** | **Address** | **Status** | **Comment** |
| --- | --- | --- | --- |
| `misa` | `0x301` | ❌ | Placeholder only |
| `cycle` | `0xC00` | ❌ | Commented out (`//0xc00 => self.cycle_counter as u32`) |
| `minstret` | `0xC02` | ❌ | Not handled |
| `mvendorid`, `marchid`, `mimpid`, `mhartid` | `0xF11–0xF14` | ❌ | Not implemented | 