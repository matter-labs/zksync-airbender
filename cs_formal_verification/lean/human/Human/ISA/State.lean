module

@[expose] public section
/-! # The machine state of Airbender: registers, PC, ROM image, RAM, the non-determinism input

Below `ROM_END` there are two different things. ROM proper: the immutable setup image; instruction fetch and every
LOAD below `ROM_END` read it, and nothing writes it (a STORE there has no next state). Shadow RAM: the RAM cells at
those same low addresses; only delegations (precompiles) reach them, and what they hold never changes what a LOAD
returns. So the state has `rom` (the image) and `mem` (RAM at every address, the shadow region included).

Airbender's starting memory: all of RAM is 0, THE SHADOW RAM BELOW `ROM_END` INCLUDED; the ROM image (`rom`) holds the
program. In Airbender the initial RAM values enter the memory argument only through the initialisation circuits (the
standalone inits-and-teardowns circuit and UnifiedReduced's inline sets), whose `Init` tokens carry no value (address
from setup, timestamp 0, value 0). The claims do not assume it: for the tracked RAM it is derived from those circuits,
`Airbender.Trace.BootRamZeroClaim` (`Human/Trace/RVSoundness.lean`) and `Airbender.UnifiedReduced.BootRamZeroClaim`
(`Human/Trace/UnifiedReduced/RVTheorems.lean`): every tracked RAM cell of the starting state reads 0 when the trace's
RAM seeds are those circuits' `Init` tokens under the verifier's top-bits check. Residual items, not derived from a
circuit: the register seeds (the chunk's public state, zero for the first chunk); RAM coverage (only the cells of
initialised windows are tracked, so only they are reachable); cross-chunk clock chaining (that no other circuit writes
at timestamp 0: delegation writes are at invocation + 2; CPU rows write at their start clock, which follows the clock
chain from 4). -/

namespace RV

abbrev Word := BitVec 32
abbrev Reg  := BitVec 5

/-- Airbender memory map: ROM `[0, 2^22)` (code + constants, read-only), RAM `[2^22, 2^32)` (the rest of the address
space) for LOAD/STORE. Loads are allowed anywhere; stores only in RAM. Delegations act on RAM at any address (below
`ROM_END`: shadow RAM). -/
def ROM_END : Nat := 0x400000
def RAM_END : Nat := 0x100000000

/-- Accessing `numBytes` bytes starting at address `addr`: allowed to read (ROM or RAM), allowed to write (RAM only),
aligned (the address is a multiple of the access size). -/
abbrev readable (addr : Word) (numBytes : Nat) : Prop := addr.toNat + numBytes ≤ RAM_END
abbrev writable (addr : Word) (numBytes : Nat) : Prop := ROM_END ≤ addr.toNat ∧ addr.toNat + numBytes ≤ RAM_END
abbrev aligned  (addr : Word) (numBytes : Nat) : Prop := addr.toNat % numBytes = 0

structure State where
  pc      : Word
  regFile : Reg → Word      -- stored values; read registers with `getReg` (x0 always reads as 0)
  rom     : Word → BitVec 8 -- the setup image: fetch and LOADs below `ROM_END` read it; nothing writes it
  mem     : Word → BitVec 8 -- RAM, byte-addressed, little-endian, every address: STOREs write it at `ROM_END` and
                            --   above, delegations anywhere (below `ROM_END`: shadow RAM, which no LOAD reads)
  input   : List Word := []  -- the non-determinism input (CSR 0x7c0): the words not yet read

namespace State
/-- The value an instruction sees in register `i`: x0 is always 0. -/
def getReg (s : State) (i : Reg) : Word := if i = 0 then 0 else s.regFile i
def setReg (s : State) (rd : Reg) (value : Word) : State :=
  { s with regFile := fun i => if i = rd then value else s.regFile i }
/-- Go on to the following instruction. -/
def nextInstr (s : State) : State := { s with pc := s.pc + 4 }
def setPC (s : State) (target : Word) : State := { s with pc := target }
/-- The bytes a LOAD sees: the ROM image below `ROM_END`, RAM above. -/
def loadView (s : State) (addr : Word) : BitVec 8 := if addr.toNat < ROM_END then s.rom addr else s.mem addr
/-- The memory a delegation call reads and writes: RAM at every address, INCLUDING READ-WRITE ACCESS TO THE SHADOW
RAM BELOW `ROM_END` (RAM cells that no LOAD or fetch reads; the ROM image `rom` is never touched). -/
def delegationRAM (s : State) : Word → BitVec 8 := s.mem
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

/-- A delegation call's effect on RAM (`delegationRAM`: shadow RAM below `ROM_END` included, read-write), then the
next instruction; no next state unless every write is an aligned word. -/
def State.applyEffect (s : State) (e : Effect) : Option State :=
  if e.writes.all fun aw => decide (aligned aw.1 4) then
    some ((s.storeAll e.writes).setReg e.reg e.val).nextInstr
  else none

end RV

namespace RV
/-- `s` and `t` agree on everything a program can see (x0's stored value is not visible). -/
def Same (s t : State) : Prop :=
  s.pc = t.pc ∧ (∀ i, s.getReg i = t.getReg i) ∧ s.rom = t.rom ∧ s.mem = t.mem ∧ s.input = t.input
end RV
