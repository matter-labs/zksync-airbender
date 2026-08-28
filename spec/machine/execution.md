# MACH: Machine Execution

> Draft extraction. Reconcile against the current implementation and move inline
> provenance into a metadata appendix before treating this module as current.

- spec-revision: `2026-08-28.5`
- implementation: `matter-labs/zksync-airbender@0aa0d393bc98fa46a2b0365d2636a98a0409b606+dirty`
- profile: `airbender-v3-gkr-2026-08-11; applicability=matched-with-nonsemantic-delta`
- scope: `active machine profiles, initial state, and cross-cycle state`

## Symbols

- `u32 = [0, 2^32)`
- `Reg : [0, 32) -> u32`
- `rts : [0, 32) -> [0, 2^38)` — last register-access timestamps
- `Mem : u32 -> [0, 256)` — byte-addressed memory
- `B : [0,n) -> u32` — authenticated program words
- `N : integer >= 0` — trace-row count
- `pc : u32` — program counter
- `ts : [0, 2^38)` — global timestamp
- `S = (pc, ts, Reg, Mem)` — machine state
- `P_base` — full-unsigned base-program profile
- `P_red` — reduced recursion profile
- `execute_i : {0,1}` — cycle-`i` execution selector
- `op_i` — cycle-`i` decoded operation
- `I_base = {LUI, AUIPC, ADDI, ADD, SUB, SLTI, SLTIU, SLT, SLTU, XORI, ORI, ANDI, SLLI, SRLI, SRAI, XOR, OR, AND, SLL, SRL, SRA, JAL, JALR, BEQ, BNE, BLT, BLTU, BGE, BGEU, LB, LBU, LH, LHU, LW, SB, SH, SW}`
- `M_u = {MUL, MULHU, DIVU, REMU}`
- `M_s = {MULH, MULHSU, DIV, REM}`
- `D_base = {BLAKE2S, BLAKE2S_G, BIGINT, KECCAK}`
- `D_red = {BLAKE2S, BLAKE2S_G}`
- `support(P, X) : {0,1}` — profile `P` admits every operation in set `X`
- `decode_P(w)` — profile-`P` preprocessed decode of word `w`
- `absent` — no row exists in the active decoder table
- `subword_mem, mop, special_rotation, xor_rot_tri_add : {0,1}` — profile feature flags

## Inputs

### IN-MACH-001
- status: `provisional`
- statement: `P in {P_base, P_red}`
- source: `profile:airbender-v3-gkr-2026-08-11#Machine profiles used by the proving flow`

### IN-MACH-002
- status: `provisional`
- statement: `B : [0,n) -> u32 && 4*n <= 2^22`
- source: `repo:common_constants/src/lib.rs#ROM_BYTE_SIZE@0aa0d393bc98fa46a2b0365d2636a98a0409b606`

### IN-MACH-003
- status: `provisional`
- statement: `trace = (S_i, execute_i, op_i) for i in [0,N)`
- source: `profile:airbender-v3-gkr-2026-08-11#Initialization, output, and termination`

## Assumptions

### ASM-MACH-001
- status: `provisional`
- statement: `execute_i => op_i = decode_P(B[pc_i / 4])`
- discharged-by: `external:DEC`

### ASM-MACH-002
- status: `provisional`
- statement: `all register, RAM, PC, and delegation tuples satisfy their global consistency relations`
- discharged-by: `external:GARG`

### ASM-MACH-003
- status: `provisional`
- statement: `execute_i => (S_i, op_i, S_{i+1}) satisfies the selected instruction-family relation`
- discharged-by: `external:ISA`

## Decision tree

> Experimental navigation view for cycle `i`. Leaf IDs name canonical statements.

- **`execute_i = 0`.** Inactive-row behavior is outside this draft's
  active-transition scope.
- **`execute_i = 1`.**
  - **`pc_i mod 4 != 0`.** No accepting proof. `REJ-MACH-002`.
  - **`pc_i mod 4 = 0`.**
    - **Decoder row absent.** No accepting proof. `REJ-MACH-001`.
    - **Decoder row present.** Apply the decoded instruction-family transition
      (`ASM-MACH-001`, `ASM-MACH-003`), advance `ts` by four (`REQ-MACH-006`), and
      preserve the global state relations (`ASM-MACH-002`).

Initialization precedes the tree with `pc_0 = 0`, `ts_0 = 4`, and the initial
register state specified by `REQ-MACH-005` and `REQ-MACH-008`. Profile selection fixes
the admitted operation and feature sets through `REQ-MACH-001..004`.

## Requirements

### REQ-MACH-001
- status: `provisional`
- statement: `P = P_base => (support(P, I_base) && support(P, M_u) && !support(P, M_s) && support(P, D_base))`
- depends: `IN-MACH-001`
- source: `profile:airbender-v3-gkr-2026-08-11#Machine profiles used by the proving flow; repo:riscv_transpiler/src/cycle/mod.rs#IMStandardIsaConfigUnsignedMulDivOnly@0aa0d393bc98fa46a2b0365d2636a98a0409b606`

### REQ-MACH-002
- status: `provisional`
- statement: `P = P_red => (!support(P, M_u) && !support(P, M_s) && support(P, D_red))`
- depends: `IN-MACH-001`
- source: `profile:airbender-v3-gkr-2026-08-11#Machine profiles used by the proving flow; repo:riscv_transpiler/src/cycle/mod.rs#ReducedMachineWithDelegation@0aa0d393bc98fa46a2b0365d2636a98a0409b606`

### REQ-MACH-003
- status: `provisional`
- statement: `P = P_base => (subword_mem=1 && mop=1 && special_rotation=1 && xor_rot_tri_add=0)`
- depends: `IN-MACH-001`
- source: `repo:riscv_transpiler/src/ir/mod.rs#FullUnsignedMachineDecoderConfig@0aa0d393bc98fa46a2b0365d2636a98a0409b606`

### REQ-MACH-004
- status: `provisional`
- statement: `P = P_red => (subword_mem=0 && mop=1 && special_rotation=0 && xor_rot_tri_add=1)`
- depends: `IN-MACH-001`
- source: `repo:riscv_transpiler/src/ir/mod.rs#ReducedMachineDecoderConfig@0aa0d393bc98fa46a2b0365d2636a98a0409b606`

### REQ-MACH-005
- status: `provisional`
- statement: `pc_0 = 0 && ts_0 = 4`
- depends: `IN-MACH-003`
- source: `profile:airbender-v3-gkr-2026-08-11#Initialization, output, and termination; repo:common_constants/src/lib.rs#INITIAL_PC@0aa0d393bc98fa46a2b0365d2636a98a0409b606; repo:common_constants/src/timestamps.rs#INITIAL_TIMESTAMP@0aa0d393bc98fa46a2b0365d2636a98a0409b606`

### REQ-MACH-006
- status: `provisional`
- statement: `forall i in [0,N): execute_i => ts_{i+1} = ts_i + 4`
- depends: `IN-MACH-003`, `REQ-MACH-005`
- source: `profile:airbender-v3-gkr-2026-08-11#Initialization, output, and termination; repo:common_constants/src/timestamps.rs#TIMESTAMP_STEP@0aa0d393bc98fa46a2b0365d2636a98a0409b606`

### REQ-MACH-007
- status: `provisional`
- statement: `forall i in [0,N): execute_i => pc_i mod 4 = 0`
- depends: `ASM-MACH-001`, `ASM-MACH-003`
- source: `profile:airbender-v3-gkr-2026-08-11#Alignment and memory policy`

### REQ-MACH-008
- status: `provisional`
- statement: `forall r in [0,32): Reg_0[r] = 0 && rts_0[r] = 0`
- depends: `IN-MACH-003`, `ASM-MACH-002`
- source: `repo:prover/src/definitions/mod.rs#produce_initial_permutation_product_separate_contributions@0aa0d393bc98fa46a2b0365d2636a98a0409b606`

## Preserved invariants

### INV-MACH-001
- status: `normative`
- statement: `Reg_0[0] = 0 && forall i in [0,N): Reg_i[0] = 0 => Reg_{i+1}[0] = 0`
- depends: `ASM-MACH-003`
- source: `standard:RISC-V-Unprivileged-ISA@20260120#RV32I-registers; profile:airbender-v3-gkr-2026-08-11#Normative ISA baseline`

### INV-MACH-002
- status: `provisional`
- statement: `forall i in [0,N): execute_i => pc_i mod 4 = 0`
- depends: `REQ-MACH-007`
- source: `derived:REQ-MACH-007`

## Rejections

### REJ-MACH-001
- status: `provisional`
- statement: `exists i in [0,N): execute_i && decode_P(B[pc_i / 4]) = absent => no accepting proof`
- depends: `ASM-MACH-001`
- source: `profile:airbender-v3-gkr-2026-08-11#Unsupported system and instruction behavior`

### REJ-MACH-002
- status: `provisional`
- statement: `exists i in [0,N): execute_i && pc_i mod 4 != 0 => no accepting proof`
- depends: `REQ-MACH-007`
- source: `profile:airbender-v3-gkr-2026-08-11#Alignment and memory policy`

## Outputs

### OUT-MACH-001
- status: `provisional`
- statement: `S_N is reachable from S_0 by N active transitions satisfying ASM-MACH-001..003 and REQ-MACH-001..008`
- depends: `ASM-MACH-001`, `ASM-MACH-002`, `ASM-MACH-003`, `REQ-MACH-001`, `REQ-MACH-002`, `REQ-MACH-003`, `REQ-MACH-004`, `REQ-MACH-005`, `REQ-MACH-006`, `REQ-MACH-007`, `REQ-MACH-008`
- source: `derived:MACH`

## Gaps

### GAP-MACH-001
- status: `open`
- question: `Is P_base the only normative base-program profile, or is the signed-M FullMachine profile also supported?`
- affects: `REQ-MACH-001`, `IN-MACH-001`
- evidence: `repo:riscv_transpiler/src/cycle/mod.rs#IMStandardIsaConfig@0aa0d393bc98fa46a2b0365d2636a98a0409b606; profile marks it outside the primary CLI path`
- owner: `human`

### GAP-MACH-002
- status: `open`
- question: `Is full-profile MOP-I Ror supported, or must every reachable Ror row be rejected?`
- affects: `REQ-MACH-003`, `REJ-MACH-001`
- evidence: `profile:airbender-v3-gkr-2026-08-11#Custom rotation profiles; preprocessing and unrolled decoder reachability differ`
- owner: `human`

### GAP-MACH-003
- status: `open`
- question: `Must every unsupported encoding have one rejection mode, or may preprocessing rejection, panic, and unprovable execution remain distinct?`
- affects: `REJ-MACH-001`
- evidence: `profile:airbender-v3-gkr-2026-08-11#Unsupported system and instruction behavior`
- owner: `human`

### GAP-MACH-004
- status: `open`
- question: `Is all-zero register initialization at timestamp 0 normative or only current implementation behavior?`
- affects: `REQ-MACH-008`, `OUT-MACH-001`
- evidence: `repo:prover/src/definitions/mod.rs#produce_initial_permutation_product_separate_contributions@0aa0d393bc98fa46a2b0365d2636a98a0409b606; profile requires tracing initialization before assuming zero`
- owner: `human`
