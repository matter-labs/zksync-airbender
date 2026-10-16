import Human.Delegations

/-! # RV32IM as Airbender runs it — our own spec, meant to be read

One instruction = at most one register or memory write, plus the PC update.
No next state (`step = none`, i.e. unprovable in Airbender) for: anything outside Airbender's RV32IM subset
(signed MULH/MULHSU/DIV/REM, FENCE, ECALL, CSRs other than the input read below, …), misaligned or out-of-range
loads/stores, misaligned jump targets, fetch outside ROM.
Non-determinism (Airbender's CSR `0x7c0`): `input` is the list of answers the prover's oracle will give, in order;
the theorems hold for every such list. `csrrw rd, 0x7c0, x0` (rd ≠ x0) reads the next answer; `csrrw x0, 0x7c0, rs1`
(rs1 ≠ x0) is a no-op (Airbender's write, a hint for witness generation). A read with no answers left has no next
state. Delegations (precompiles): `csrrw x0, <csr>, x0` for the CSRs of `Human/Delegations.lean`. These are the
CSR rows of Airbender's ISA table, and the only ones: other CSRs, other forms (csrrs, csrrc, immediates; the
transpiler is more lenient) and other shapes have no next state.
Differences from standard RV32IM follow Airbender's ISA table (spec/top-down/00 master.md, "Supported
instruction set"); each is marked `-- Airbender:` below. -/

namespace RV

/-- The ALU operations (of OP and OP-IMM instructions). -/
inductive Op | add | sub | sll | slt | sltu | xor | srl | sra | or | and
             | mul | mulhu | divu | remu    -- Airbender: no signed MULH, MULHSU, DIV, REM

def alu : Op → Word → Word → Word
  | .add,    a, b => a + b
  | .sub,    a, b => a - b
  | .sll,    a, b => a <<< (b.setWidth 5).toNat
  | .slt,    a, b => if a.slt b then 1 else 0
  | .sltu,   a, b => if a.ult b then 1 else 0
  | .xor,    a, b => a ^^^ b
  | .srl,    a, b => a >>> (b.setWidth 5).toNat
  | .sra,    a, b => a.sshiftRight (b.setWidth 5).toNat
  | .or,     a, b => a ||| b
  | .and,    a, b => a &&& b
  | .mul,    a, b => a * b
  | .mulhu,  a, b => (a.zeroExtend 64 * b.zeroExtend 64).extractLsb' 32 32
  | .divu,   a, b => if b = 0 then -1 else a / b   -- division by zero: all ones / the dividend
  | .remu,   a, b => if b = 0 then a else a % b    --   (as the ISA specifies; no trap)

/-- Airbender: field operations as custom Zimop instructions `mop.rr.N rd, rs1, rs2` (N = 0 … 4), on the
BabyBear prime `BabyBearP` (semantics as Airbender's VM, riscv_transpiler
`vm/instructions/add_sub_family/mop.rs`). Register values are first reduced mod `BabyBearP`; results are
`< BabyBearP` (except `triAdd`, a plain 32-bit sum). `fma` and `triAdd` also read `rd`. -/
inductive FieldOp | add | sub | mul | fma | triAdd

def BabyBearP : Nat := 0x78000001        -- BabyBear: 2^31 - 2^27 + 1

/-- `2^-32 mod BabyBearP`: field values are kept in Montgomery form (`x` held as `x · 2^32 mod BabyBearP`). -/
def RINV : Nat := 0x38400000
theorem RINV_spec : RINV * 2 ^ 32 % BabyBearP = 1 := by decide

/-- `mul` is the Montgomery product: if `a`, `b` hold `x · 2^32`, `y · 2^32` (mod `BabyBearP`), the result holds
`x · y · 2^32`. -/
def mopVal : FieldOp → (a b old : Word) → Word
  | .add,    a, b, _   => BitVec.ofNat 32 ((a.toNat % BabyBearP + b.toNat % BabyBearP) % BabyBearP)
  | .sub,    a, b, _   => BitVec.ofNat 32 ((a.toNat % BabyBearP + BabyBearP - b.toNat % BabyBearP) % BabyBearP)
  | .mul,    a, b, _   => BitVec.ofNat 32 (a.toNat % BabyBearP * (b.toNat % BabyBearP) * RINV % BabyBearP)
  | .fma,    a, b, old =>
      BitVec.ofNat 32 ((a.toNat % BabyBearP * (b.toNat % BabyBearP) * RINV + old.toNat % BabyBearP) % BabyBearP)
  | .triAdd, a, b, old => a + b + old

/-- The branch conditions. -/
inductive Cond | eq | ne | lt | ge | ltu | geu

def Cond.holds : Cond → Word → Word → Bool
  | .eq,  a, b => a == b
  | .ne,  a, b => a != b
  | .lt,  a, b => a.slt b
  | .ge,  a, b => !a.slt b
  | .ltu, a, b => a.ult b
  | .geu, a, b => !a.ult b

/-- Immediates and offsets are stored already decoded (sign-extended / shifted). -/
inductive Instr
  | lui    (rd : Reg) (imm : Word)
  | auipc  (rd : Reg) (imm : Word)
  | jal    (rd : Reg) (offset : Word)
  | jalr   (rd rs1 : Reg) (offset : Word)
  | branch (cond : Cond) (rs1 rs2 : Reg) (offset : Word)
  | load   (numBytes : Nat) (signed : Bool) (rd rs1 : Reg) (offset : Word)
  | store  (numBytes : Nat) (rs2 rs1 : Reg) (offset : Word)
  | opImm  (op : Op) (rd rs1 : Reg) (imm : Word)
  | op     (op : Op) (rd rs1 rs2 : Reg)
  | mop    (op : FieldOp) (rd rs1 rs2 : Reg)   -- Airbender: field operations (`mop.rr.N`)
  | inputRead (rd : Reg)                      -- Airbender: `csrrw rd, 0x7c0, x0`: `rd` := the next input word
  | inputWrite (src : Reg)                    -- Airbender: `csrrw x0, 0x7c0, rs1`: no effect
  | delegate (k : DelegationKind)             -- Airbender: `csrrw x0, <csr>, x0`: a delegation call

/-- Whether an instruction reads an input word. -/
def Instr.readsInput : Instr → Bool
  | .inputRead _ => true
  | _ => false

/-- What one instruction does to the state (`none`: Airbender cannot run it). -/
def exec (s : State) : Instr → Option State
  | .lui rd imm            => some (s.setReg rd imm).nextInstr
  | .auipc rd imm          => some (s.setReg rd (s.pc + imm)).nextInstr
  | .jal rd offset         => (s.jumpAligned (s.pc + offset)).map (·.setReg rd (s.pc + 4))
  | .jalr rd rs1 offset    =>                       -- `&&& ~~~1`: JALR clears bit 0 of the target
      (s.jumpAligned ((s.getReg rs1 + offset) &&& ~~~1)).map (·.setReg rd (s.pc + 4))
  | .branch cond rs1 rs2 offset =>
      if cond.holds (s.getReg rs1) (s.getReg rs2) then s.jumpAligned (s.pc + offset) else some s.nextInstr
  | .load numBytes signed rd rs1 offset =>
      let addr := s.getReg rs1 + offset
      let bytes := read s.mem addr numBytes
      let value := if signed then (bytes.setWidth (8 * numBytes)).signExtend 32 else bytes
      if rd = 0 then some s.nextInstr                 -- Airbender: a load into x0 only advances the PC
      else if aligned addr numBytes ∧ readable addr numBytes then some (s.setReg rd value).nextInstr else none
  | .store numBytes rs2 rs1 offset =>
      let addr := s.getReg rs1 + offset
      if aligned addr numBytes ∧ writable addr numBytes then some (s.store addr (s.getReg rs2) numBytes).nextInstr
      else none
  | .opImm op rd rs1 imm   => some (s.setReg rd (alu op (s.getReg rs1) imm)).nextInstr
  | .op op rd rs1 rs2      => some (s.setReg rd (alu op (s.getReg rs1) (s.getReg rs2))).nextInstr
  | .mop op rd rs1 rs2     =>                       -- Airbender: `rd = x0` is not allowed (the circuit requires it)
      if rd = 0 then none else some (s.setReg rd (mopVal op (s.getReg rs1) (s.getReg rs2) (s.getReg rd))).nextInstr
  | .inputRead rd          =>
      match s.input with
      | w :: rest => some { (s.setReg rd w).nextInstr with input := rest }
      | []        => none
  | .inputWrite _          => some s.nextInstr
  | .delegate k            =>                       -- Airbender: `Human/Delegations.lean`
      (Delegation.effect k (s.getReg 10) (s.getReg 11) (s.getReg 12) s.mem).bind s.applyEffect

/-- Airbender: `csrrw rd, csr, rs1`: the non-determinism read (`0x7c0`, rs1 = x0, rd ≠ x0) or write (`0x7c0`,
rd = x0, rs1 ≠ x0), or a delegation call (rs1 = rd = x0). -/
def decodeCsr (csr : BitVec 12) (rs1 rd : Reg) : Option Instr :=
  if csr = 0x7c0 then
    (if rs1 = 0 ∧ rd ≠ 0 then some (.inputRead rd) else if rs1 ≠ 0 ∧ rd = 0 then some (.inputWrite rs1) else none)
  else if rs1 = 0 ∧ rd = 0 then (DelegationKind.ofCsr csr).map .delegate
  else none

/-- Standard RV32IM encodings (unprivileged spec, ch. 2 and 13). -/
def decode (word : Word) : Option Instr :=
  let opcode := (word.extractLsb' 0 7).toNat
  let funct3 := (word.extractLsb' 12 3).toNat
  let funct7 := (word.extractLsb' 25 7).toNat
  let rd  : Reg := word.extractLsb' 7 5
  let rs1 : Reg := word.extractLsb' 15 5
  let rs2 : Reg := word.extractLsb' 20 5
  let csr : BitVec 12 := word.extractLsb' 20 12
  let immI : Word := (word.extractLsb' 20 12).signExtend 32
  let immS : Word := (word.extractLsb' 25 7 ++ word.extractLsb' 7 5).signExtend 32
  let immB : Word := (word.extractLsb' 31 1 ++ word.extractLsb' 7 1 ++ word.extractLsb' 25 6 ++ word.extractLsb' 8 4
                      ++ (0 : BitVec 1)).signExtend 32
  let immU : Word := word.extractLsb' 12 20 ++ (0 : BitVec 12)
  let immJ : Word := (word.extractLsb' 31 1 ++ word.extractLsb' 12 8 ++ word.extractLsb' 20 1 ++ word.extractLsb' 21 10
                      ++ (0 : BitVec 1)).signExtend 32
  let shamt : Word := rs2.zeroExtend 32
  match opcode, funct3, funct7 with
  | 0x37, _, _    => some (.lui rd immU)
  | 0x17, _, _    => some (.auipc rd immU)
  | 0x6f, _, _    => some (.jal rd immJ)
  | 0x67, _, _    => some (.jalr rd rs1 immI)          -- Airbender: any funct3
  | 0x63, 0, _    => some (.branch .eq  rs1 rs2 immB)
  | 0x63, 1, _    => some (.branch .ne  rs1 rs2 immB)
  | 0x63, 4, _    => some (.branch .lt  rs1 rs2 immB)
  | 0x63, 5, _    => some (.branch .ge  rs1 rs2 immB)
  | 0x63, 6, _    => some (.branch .ltu rs1 rs2 immB)
  | 0x63, 7, _    => some (.branch .geu rs1 rs2 immB)
  | 0x03, 0, _    => some (.load 1 true  rd rs1 immI)    -- lb
  | 0x03, 1, _    => some (.load 2 true  rd rs1 immI)    -- lh
  | 0x03, 2, _    => some (.load 4 true  rd rs1 immI)    -- lw
  | 0x03, 4, _    => some (.load 1 false rd rs1 immI)    -- lbu
  | 0x03, 5, _    => some (.load 2 false rd rs1 immI)    -- lhu
  | 0x23, 0, _    => some (.store 1 rs2 rs1 immS)        -- sb
  | 0x23, 1, _    => some (.store 2 rs2 rs1 immS)        -- sh
  | 0x23, 2, _    => some (.store 4 rs2 rs1 immS)        -- sw
  | 0x13, 0, _    => some (.opImm .add  rd rs1 immI)
  | 0x13, 2, _    => some (.opImm .slt  rd rs1 immI)
  | 0x13, 3, _    => some (.opImm .sltu rd rs1 immI)
  | 0x13, 4, _    => some (.opImm .xor  rd rs1 immI)
  | 0x13, 6, _    => some (.opImm .or   rd rs1 immI)
  | 0x13, 7, _    => some (.opImm .and  rd rs1 immI)
  | 0x13, 1, 0x00 => some (.opImm .sll  rd rs1 shamt)
  | 0x13, 5, 0x00 => some (.opImm .srl  rd rs1 shamt)
  | 0x13, 5, 0x20 => some (.opImm .sra  rd rs1 shamt)
  | 0x33, 0, 0x00 => some (.op .add    rd rs1 rs2)
  | 0x33, 0, 0x20 => some (.op .sub    rd rs1 rs2)
  | 0x33, 0, 0x01 => some (.op .mul    rd rs1 rs2)
  | 0x33, 1, 0x00 => some (.op .sll    rd rs1 rs2)
  | 0x33, 3, 0x01 => some (.op .mulhu  rd rs1 rs2)
  | 0x33, 5, 0x00 => some (.op .srl    rd rs1 rs2)
  | 0x33, 5, 0x20 => some (.op .sra    rd rs1 rs2)
  | 0x33, 5, 0x01 => some (.op .divu   rd rs1 rs2)
  | 0x33, 7, 0x01 => some (.op .remu   rd rs1 rs2)
  | 0x33, _, 0x01 => none                               -- Airbender: no MULH, MULHSU, DIV, REM
  | 0x33, 2, _    => some (.op .slt    rd rs1 rs2)      -- Airbender: SLT, SLTU, XOR, OR, AND accept any funct7
  | 0x33, 3, _    => some (.op .sltu   rd rs1 rs2)
  | 0x33, 4, _    => some (.op .xor    rd rs1 rs2)
  | 0x33, 6, _    => some (.op .or     rd rs1 rs2)
  | 0x33, 7, _    => some (.op .and    rd rs1 rs2)
  | 0x73, 4, 0x41 => some (.mop .add    rd rs1 rs2)      -- Airbender: mop.rr.0 … mop.rr.4 (Zimop encodings)
  | 0x73, 4, 0x43 => some (.mop .sub    rd rs1 rs2)
  | 0x73, 4, 0x45 => some (.mop .mul    rd rs1 rs2)
  | 0x73, 4, 0x47 => some (.mop .fma    rd rs1 rs2)
  | 0x73, 4, 0x61 => some (.mop .triAdd rd rs1 rs2)
  | 0x73, 1, _    => decodeCsr csr rs1 rd               -- Zicsr: csrrw
  | _, _, _       => none

/-- One step: fetch from ROM at an aligned PC, decode, execute. -/
def step (s : State) : Option State :=
  if s.pc.toNat % 4 = 0 ∧ s.pc.toNat + 4 ≤ ROM_END then (decode (read s.mem s.pc 4)).bind (exec s) else none

/-- `numSteps` steps (`none` if any step has no next state). -/
def run : (numSteps : Nat) → State → Option State
  | 0,     s => some s
  | n + 1, s => (step s).bind (run n)

end RV
