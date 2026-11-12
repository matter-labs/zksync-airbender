module
public import Slop.JumpBranchSlt.WitnessCheck
public import Slop.KernelRfl
public import Slop.NonVacuous.Basic
public import Slop.NonVacuous.SingleRow
public import Human.Trace.Families.JumpBranchSlt.RVTheorems

@[expose] public section

/-! A one-row jump/branch/comparison trace meeting the assumptions of `JumpBranchSlt.RVTraceSoundnessClaim`
    (`Human/Trace/Families/JumpBranchSlt/RVTheorems.lean`): `JAL x1, 4` at PC 0 (ROM bytes `EF 00 40 00`) and clock
    four on zero registers. The row is that of `Tests.JumpHistory` (ordinary clocks) with offset 4 for -4; its
    constraints close by one kernel evaluation. -/

namespace Airbender.NonVacuous.JumpBranchSltTrace
open Trace Arithmetic

/-- Columns: 0-3 PC and clock, 4 execute, 7 rd, 8-9 the offset, 11 the JAL flag, 16-19 the next PC and clock, 24 the
    second x0 read's prior clock (the first read's refresh), 30 the link value's low limb, 34/36/47 the link and target
    sums, 49-51 the clock-comparison borrows. -/
def assignment : Nat → ZMod babyBearModulus
  | 2 | 8 | 16 | 24 | 30 | 34 | 36 | 47 => 4
  | 18 => 8
  | 4 | 7 | 11 | 49 | 50 | 51 => 1
  | _ => 0

def row : Row babyBearModulus JumpBranchSlt.TraceKind := ⟨.jumpBranchSlt, assignment⟩

theorem satisfies :
    FlatOperation.ConstraintsHoldFlat (Verification.environment assignment) JumpBranchSlt.clockConstraints :=
  JumpBranchSlt.holds_of_check (by kernel_rfl) (by kernel_rfl)

/-- `JAL x1, 4` (`0x004000EF`) at ROM address 0, zero registers and RAM. -/
def initial : RV.State where
  pc := 0
  regFile _ := 0
  rom a := if a = 0 then 0xEF else if a = 2 then 0x40 else 0
  mem _ := 0

def cells : List Cell := [.register 0, .register 1]

def program : List JumpBranchSlt.RVProgramEntry := [⟨0, 0x004000EF#32, ⟨(), 0, 0, 1, ⟨4, 0⟩, 1, 0⟩⟩]

def trace : JumpBranchSlt.NativeTrace babyBearModulus where
  rows := [row]
  rom := ROM.table [] []
  initial := PCState.boundary 0 (4, 0)
  terminal := row.finish
  initialMemory := [cellToken (.register 0) 0 0 0, cellToken (.register 1) 0 0 0]
  terminalMemory := [cellToken (.register 0) 5 0 0, cellToken (.register 1) 6 4 0]

theorem accepted : Accepted trace :=
  accepted_of_row rfl satisfies rfl (by kernel_rfl) rfl (by decide +kernel)

theorem inputs : JumpBranchSlt.RVExecutionInputs trace initial cells program where
  distinct := by decide
  aligned := by decide
  image := by kernel_rfl
  initialPC := ⟨(4, 0), rfl⟩
  programImage := ⟨[0], by kernel_rfl⟩
  clocks := ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩
  terminalCanonical := by decide +kernel

theorem decoded : JumpBranchSlt.RVDecoded trace program := by
  intro current member
  simp only [trace, List.mem_singleton] at member
  subst current
  exact ⟨⟨0, by decide +kernel⟩, by kernel_rfl⟩

end Airbender.NonVacuous.JumpBranchSltTrace
