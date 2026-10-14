/-! # RV32IM as Airbender runs it — our own spec, meant to be read

One instruction = at most one register or memory write, plus the PC update.
No next state (`step = none`, i.e. unprovable in Airbender) for: anything outside Airbender's RV32IM subset
(signed MULH/MULHSU/DIV/REM, FENCE, ECALL, CSRs, …), misaligned or out-of-range loads/stores, misaligned jump
targets, fetch outside ROM.
Differences from standard RV32IM follow Airbender's ISA table (spec/top-down/00 master.md, "Supported
instruction set"); each is marked `-- Airbender:` below. -/

namespace RV

abbrev Word := BitVec 32
abbrev Reg  := BitVec 5

/-- Airbender memory map: ROM `[0, 4 MiB)` (code + constants, read-only), RAM `[4 MiB, 1 GiB)`. -/
def ROM_END : Nat := 0x400000
def RAM_END : Nat := 0x40000000

/-- Accessing `numBytes` bytes starting at address `addr`: allowed to read (ROM or RAM), allowed to write (RAM only),
aligned (the address is a multiple of the access size). -/
abbrev readable (addr : Word) (numBytes : Nat) : Prop := addr.toNat + numBytes ≤ RAM_END
abbrev writable (addr : Word) (numBytes : Nat) : Prop := ROM_END ≤ addr.toNat ∧ addr.toNat + numBytes ≤ RAM_END
abbrev aligned  (addr : Word) (numBytes : Nat) : Prop := addr.toNat % numBytes = 0

structure State where
  pc      : Word
  regFile : Reg → Word      -- stored values; read registers with `getReg` (x0 always reads as 0)
  mem     : Word → BitVec 8 -- byte-addressed, little-endian

namespace State
/-- The value an instruction sees in register `i`: x0 is always 0. -/
def getReg (s : State) (i : Reg) : Word := if i = 0 then 0 else s.regFile i
def setReg (s : State) (rd : Reg) (v : Word) : State :=
  { s with regFile := fun i => if i = rd then v else s.regFile i }
def next (s : State) : State := { s with pc := s.pc + 4 }
def jump (s : State) (t : Word) : State := { s with pc := t }
/-- Jump; the target must be 4-byte aligned (no compressed instructions). -/
def goto (s : State) (t : Word) : Option State := if t.toNat % 4 = 0 then some (s.jump t) else none
end State

/-- `n` bytes at `a`, little-endian. -/
def read (m : Word → BitVec 8) (a : Word) : Nat → Word
  | 0     => 0
  | n + 1 => (m a).zeroExtend 32 ||| (read m (a + 1) n <<< 8)

/-- The low `n` bytes of `v` written at `a`, little-endian. -/
def write (m : Word → BitVec 8) (a : Word) (v : Word) : Nat → (Word → BitVec 8)
  | 0     => m
  | n + 1 => write (fun b => if b = a then v.setWidth 8 else m b) (a + 1) (v >>> 8) n

/-- Store the low `n` bytes of `v` at `a`. -/
def State.store (s : State) (a v : Word) (n : Nat) : State := { s with mem := write s.mem a v n }

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
  | .divu,   a, b => if b = 0 then -1 else a / b
  | .remu,   a, b => if b = 0 then a else a % b

inductive Cond | eq | ne | lt | ge | ltu | geu

def Cond.holds : Cond → Word → Word → Bool
  | .eq,  a, b => a == b
  | .ne,  a, b => a != b
  | .lt,  a, b => a.slt b
  | .ge,  a, b => !a.slt b
  | .ltu, a, b => a.ult b
  | .geu, a, b => !a.ult b

/-- Immediates are stored already decoded (sign-extended / shifted). -/
inductive Instr
  | lui    (rd : Reg) (imm : Word)
  | auipc  (rd : Reg) (imm : Word)
  | jal    (rd : Reg) (off : Word)
  | jalr   (rd rs1 : Reg) (off : Word)
  | branch (c : Cond) (rs1 rs2 : Reg) (off : Word)
  | load   (n : Nat) (signed : Bool) (rd rs1 : Reg) (off : Word)
  | store  (n : Nat) (rs2 rs1 : Reg) (off : Word)
  | opImm  (op : Op) (rd rs1 : Reg) (imm : Word)
  | op     (op : Op) (rd rs1 rs2 : Reg)

def exec (s : State) : Instr → Option State
  | .lui rd imm         => some (s.setReg rd imm).next
  | .auipc rd imm       => some (s.setReg rd (s.pc + imm)).next
  | .jal rd off         => (s.goto (s.pc + off)).map (·.setReg rd (s.pc + 4))
  | .jalr rd rs1 off    => (s.goto ((s.getReg rs1 + off) &&& ~~~1)).map (·.setReg rd (s.pc + 4))
  | .branch c rs1 rs2 off =>
      if c.holds (s.getReg rs1) (s.getReg rs2) then s.goto (s.pc + off) else some s.next
  | .load n sg rd rs1 off =>
      let a := s.getReg rs1 + off
      let v := read s.mem a n
      let v := if sg then (v.setWidth (8 * n)).signExtend 32 else v
      if rd = 0 then some s.next                      -- Airbender: a load into x0 only advances the PC
      else if aligned a n ∧ readable a n then some (s.setReg rd v).next else none
  | .store n rs2 rs1 off =>
      let a := s.getReg rs1 + off
      if aligned a n ∧ writable a n then some (s.store a (s.getReg rs2) n).next else none
  | .opImm op rd rs1 imm => some (s.setReg rd (alu op (s.getReg rs1) imm)).next
  | .op op rd rs1 rs2    => some (s.setReg rd (alu op (s.getReg rs1) (s.getReg rs2))).next

/-- Standard RV32IM encodings (unprivileged spec, ch. 2 and 13). -/
def decode (w : Word) : Option Instr :=
  let opc := (w.extractLsb' 0 7).toNat
  let f3  := (w.extractLsb' 12 3).toNat
  let f7  := (w.extractLsb' 25 7).toNat
  let rd  : Reg := w.extractLsb' 7 5
  let rs1 : Reg := w.extractLsb' 15 5
  let rs2 : Reg := w.extractLsb' 20 5
  let immI : Word := (w.extractLsb' 20 12).signExtend 32
  let immS : Word := (w.extractLsb' 25 7 ++ w.extractLsb' 7 5).signExtend 32
  let immB : Word := (w.extractLsb' 31 1 ++ w.extractLsb' 7 1 ++ w.extractLsb' 25 6 ++ w.extractLsb' 8 4
                      ++ (0 : BitVec 1)).signExtend 32
  let immU : Word := w.extractLsb' 12 20 ++ (0 : BitVec 12)
  let immJ : Word := (w.extractLsb' 31 1 ++ w.extractLsb' 12 8 ++ w.extractLsb' 20 1 ++ w.extractLsb' 21 10
                      ++ (0 : BitVec 1)).signExtend 32
  let shamt : Word := rs2.zeroExtend 32
  match opc, f3, f7 with
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
  | _, _, _       => none

/-- One step: fetch from ROM at an aligned PC, decode, execute. -/
def step (s : State) : Option State :=
  if s.pc.toNat % 4 = 0 ∧ s.pc.toNat + 4 ≤ ROM_END then (decode (read s.mem s.pc 4)).bind (exec s) else none

/-- `n` steps. -/
def run : Nat → State → Option State
  | 0,     s => some s
  | n + 1, s => (step s).bind (run n)

end RV
