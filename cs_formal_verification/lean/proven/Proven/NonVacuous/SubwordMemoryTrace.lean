module
public import Proven.SubwordMemory.WitnessCheck
public import Proven.Constraints
public import Proven.KernelRfl
public import Proven.NonVacuous.Basic
public import Proven.NonVacuous.SingleRow
public import Human.Trace.Families.SubwordMemory.RVTheorems

@[expose] public section

/-! A one-row subword-memory trace meeting the assumptions of `SubwordMemory.RVRamTraceSoundnessClaim`
    (`Human/Trace/Families/SubwordMemory/RVTheorems.lean`): `LBU x2, 0(x1)` at PC 0 (ROM bytes `03 C1 00 00`) and
    clock four, with x1 = `0x00400001` and the RAM word `0x56781234` at `0x00400000` (the first RAM word). The row is
    that of `Tests.SubwordMemoryTimestamp` (ordinary clocks); its constraints close by one kernel evaluation. -/

namespace Airbender.NonVacuous.SubwordMemoryTrace
open Trace Arithmetic

/-- Columns: 0-3 PC and clock, 4 execute, 5/7 rs1/rd, 11 the LBU flag, 13-16 the next PC and clock, 19-20 x1, 21-22
    the word address, 25-26 the word, 27 the destination, 33 the loaded byte, 62-64 the clock-comparison borrows,
    the rest the byte-selection and subword-table queries. -/
def assignment : Nat → ZMod babyBearModulus
  | 2 | 13 => 4
  | 15 => 8
  | 4 | 5 | 11 | 19 | 35 | 47 | 60 | 62 | 63 | 64 => 1
  | 7 | 27 => 2
  | 20 | 22 => 64
  | 25 => 4660
  | 26 => 22136
  | 33 | 53 | 54 | 55 => 18
  | 44 => 65536
  | 49 => 20971520
  | 50 | 52 => 135732
  | 51 => 70196
  | 59 | 61 => 43
  | _ => 0

def row : Row babyBearModulus SubwordMemory.TraceKind := ⟨.subwordMemory, assignment⟩

def setup : Table (ZMod babyBearModulus) (fields 9) := Verification.subwordTable fun _ => 0

theorem satisfies : FlatOperation.ConstraintsHoldFlat (Verification.environment assignment)
    (SubwordMemory.clockConstraints setup) :=
  Verification.holds_append
    (SubwordMemory.holds_of_check (SubwordMemory.subwordChecked _) rfl (by kernel_rfl))
    (SubwordMemory.timestamps_of_check (by kernel_rfl))

/-- `LBU x2, 0(x1)` (`0x0000C103`) at ROM address 0; x1 points into the RAM word `0x56781234`. -/
def initial : RV.State where
  pc := 0
  regFile i := if i = 1 then 0x00400001 else 0
  rom a := if a = 0 then 0x03 else if a = 1 then 0xC1 else 0
  mem a := if a = 0x400000 then 0x34 else if a = 0x400001 then 0x12 else if a = 0x400002 then 0x78
    else if a = 0x400003 then 0x56 else 0

def cells : List Cell := [.register 1, .ram 0x400000, .register 2]

def program : List SubwordMemory.RVProgramEntry := [⟨0, 0x0000C103#32, ⟨(), 1, 0, 2, ⟨0, 0⟩, 2, 0⟩⟩]

def trace : SubwordMemory.NativeTrace babyBearModulus where
  rows := [row]
  rom := setup
  initial := PCState.boundary 0 (4, 0)
  terminal := row.finish
  initialMemory :=
    [cellToken (.register 1) 0 1 64, cellToken (.ram 0x400000) 0 4660 22136, cellToken (.register 2) 0 0 0]
  terminalMemory :=
    [cellToken (.register 1) 4 1 64, cellToken (.ram 0x400000) 5 4660 22136, cellToken (.register 2) 6 18 0]

theorem accepted : Accepted trace :=
  accepted_of_row rfl satisfies rfl (by kernel_rfl) rfl (by decide +kernel)

theorem inputs : SubwordMemory.RVRAMInputs trace initial cells program where
  distinct := by decide
  aligned := by decide
  image := by kernel_rfl
  initialPC := ⟨(4, 0), rfl⟩
  programImage := ⟨[0], by kernel_rfl⟩
  clocks := ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩
  ramDomain address member := by
    simp only [cells, List.mem_cons, List.not_mem_nil, or_false, reduceCtorEq, false_or, Cell.ram.injEq] at member
    subst member
    decide
  setup := ⟨_, rfl⟩

theorem decoded : SubwordMemory.RVDecoded trace program := by
  intro current member
  simp only [trace, List.mem_singleton] at member
  subst current
  exact ⟨⟨0, by decide +kernel⟩, by kernel_rfl⟩

end Airbender.NonVacuous.SubwordMemoryTrace
