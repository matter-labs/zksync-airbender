/-! # The machine state of Airbender: registers, PC, byte memory, the non-determinism input -/

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
  input   : List Word := []  -- the non-determinism input (CSR 0x7c0): the words not yet read

namespace State
/-- The value an instruction sees in register `i`: x0 is always 0. -/
def getReg (s : State) (i : Reg) : Word := if i = 0 then 0 else s.regFile i
def setReg (s : State) (rd : Reg) (value : Word) : State :=
  { s with regFile := fun i => if i = rd then value else s.regFile i }
/-- Go on to the following instruction. -/
def nextInstr (s : State) : State := { s with pc := s.pc + 4 }
def setPC (s : State) (target : Word) : State := { s with pc := target }
/-- Jump to `target`; no next state unless it is 4-byte aligned (no compressed instructions). -/
def jumpAligned (s : State) (target : Word) : Option State :=
  if target.toNat % 4 = 0 then some (s.setPC target) else none
end State

/-- The `numBytes` bytes at `addr`, little-endian (lowest address = lowest byte). -/
def read (mem : Word → BitVec 8) (addr : Word) : (numBytes : Nat) → Word
  | 0     => 0
  | n + 1 => (mem addr).zeroExtend 32 ||| (read mem (addr + 1) n <<< 8)

/-- Memory after writing the low `numBytes` bytes of `value` at `addr`, little-endian. -/
def write (mem : Word → BitVec 8) (addr : Word) (value : Word) : (numBytes : Nat) → (Word → BitVec 8)
  | 0     => mem
  | n + 1 => write (fun b => if b = addr then value.setWidth 8 else mem b) (addr + 1) (value >>> 8) n

/-- Store the low `numBytes` bytes of `value` at `addr`. -/
def State.store (s : State) (addr value : Word) (numBytes : Nat) : State :=
  { s with mem := write s.mem addr value numBytes }

/-- What a delegation call does: the words it writes (address, value) and the new value of one register. -/
structure Effect where
  writes : List (Word × Word)
  reg    : Reg
  val    : Word

/-- Store the words of `ws` (address, value). -/
def State.storeAll (s : State) : List (Word × Word) → State
  | []           => s
  | (a, w) :: ws => (s.store a w 4).storeAll ws

/-- A delegation call's effect, then the next instruction; no next state unless every write is an aligned word in
RAM. -/
def State.applyEffect (s : State) (e : Effect) : Option State :=
  if e.writes.all fun aw => decide (writable aw.1 4 ∧ aligned aw.1 4) then
    some ((s.storeAll e.writes).setReg e.reg e.val).nextInstr
  else none

end RV
