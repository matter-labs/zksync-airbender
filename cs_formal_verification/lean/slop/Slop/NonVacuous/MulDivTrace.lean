module
public import Slop.MulDiv.WitnessCheck
public import Slop.KernelRfl
public import Slop.NonVacuous.Basic
public import Slop.NonVacuous.SingleRow
public import Human.Trace.Families.MulDiv.RVTheorems

@[expose] public section

/-! A one-row MUL/DIV trace meeting the assumptions of `MulDiv.RVTraceSoundnessClaim`
    (`Human/Trace/Families/MulDiv/RVTheorems.lean`): `MUL x3, x1, x2` at PC 0 (ROM bytes `B3 81 20 02`) and clock four
    on zero registers. Its constraints close by one kernel evaluation. -/

namespace Airbender.NonVacuous.MulDivTrace
open Trace Arithmetic

/-- Columns: 0-3 PC and clock, 4 execute, 5-7 rs1/rs2/rd, 10 the MUL flag, 14-17 the next PC and clock, 32 the
    divisor's zero flag, 65-67 the clock-comparison borrows; every value and product column is zero. -/
def assignment (v : Nat) : ZMod babyBearModulus :=
  if v = 2 ∨ v = 14 then 4
  else if v = 16 then 8
  else if v = 4 ∨ v = 5 ∨ v = 10 ∨ v = 32 ∨ v = 65 ∨ v = 66 ∨ v = 67 then 1
  else if v = 6 then 2
  else if v = 7 then 3
  else 0

def row : Row babyBearModulus MulDiv.TraceKind := ⟨.mulDiv, assignment⟩

theorem satisfies : FlatOperation.ConstraintsHoldFlat (Verification.environment assignment) MulDiv.clockConstraints :=
  MulDiv.holds_of_check (by kernel_rfl)

/-- `MUL x3, x1, x2` (`0x022081B3`) at ROM address 0, zero registers and RAM. -/
def initial : RV.State where
  pc := 0
  regFile _ := 0
  rom a := if a = 0 then 0xB3 else if a = 1 then 0x81 else if a = 2 then 0x20 else if a = 3 then 0x02 else 0
  mem _ := 0

def cells : List Cell := [.register 1, .register 2, .register 3]

def program : List MulDiv.RVProgramEntry := [⟨0, 0x022081B3#32, ⟨(), 1, 2, 3, ⟨0, 0⟩, 1, 0⟩⟩]

def trace : MulDiv.NativeTrace babyBearModulus where
  rows := [row]
  rom := ROM.table [] []
  initial := PCState.boundary 0 (4, 0)
  terminal := row.finish
  initialMemory := [cellToken (.register 1) 0 0 0, cellToken (.register 2) 0 0 0, cellToken (.register 3) 0 0 0]
  terminalMemory := [cellToken (.register 1) 4 0 0, cellToken (.register 2) 5 0 0, cellToken (.register 3) 6 0 0]

theorem accepted : Accepted trace :=
  accepted_of_row rfl satisfies rfl (by kernel_rfl) rfl (by decide +kernel)

theorem inputs : MulDiv.RVExecutionInputs trace initial cells program where
  distinct := by decide
  aligned := by decide
  image := by kernel_rfl
  initialPC := ⟨(4, 0), rfl⟩
  programImage := ⟨[0], by kernel_rfl⟩
  clocks := ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem decoded : MulDiv.RVDecoded trace program := by
  intro current member
  simp only [trace, List.mem_singleton] at member
  subst current
  exact ⟨⟨0, by decide +kernel⟩, by kernel_rfl⟩

end Airbender.NonVacuous.MulDivTrace
