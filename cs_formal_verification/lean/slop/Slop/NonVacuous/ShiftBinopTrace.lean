module
public import Slop.ShiftBinop.WitnessCheck
public import Slop.KernelRfl
public import Slop.NonVacuous.Basic
public import Slop.NonVacuous.SingleRow
public import Human.Trace.Families.ShiftBinop.RVTheorems

@[expose] public section

/-! A one-row shift/binop trace meeting the assumptions of `ShiftBinop.RVTraceSoundnessClaim`
    (`Human/Trace/Families/ShiftBinop/RVTheorems.lean`): `XOR x1, x0, x0` at PC 0 (ROM bytes `B3 40 00 00`) and clock
    four on zero registers. The row is that of `Tests.ShiftBinopTimestamp` (ordinary clocks) moved to PC 0; its
    constraints close by one kernel evaluation. -/

namespace Airbender.NonVacuous.ShiftBinopTrace
open Trace Arithmetic

/-- Columns: 0-3 PC and clock, 4 execute, 7 rd, 10 the XOR tag, 12 the binop flag, 13-16 the next PC and clock, 23
    the second x0 read's prior clock (the first read's refresh), 55/64/73/82/91 the byte-query tags, 92-94 the
    clock-comparison borrows; every value column is zero. -/
def assignment : Nat → ZMod babyBearModulus
  | 2 | 10 | 13 | 23 | 64 | 73 | 82 | 91 => 4
  | 15 => 8
  | 4 | 7 | 12 | 92 | 93 | 94 => 1
  | 55 => 3
  | _ => 0

def row : Row babyBearModulus ShiftBinop.TraceKind := ⟨.shiftBinop, assignment⟩

theorem satisfies :
    FlatOperation.ConstraintsHoldFlat (Verification.environment assignment) ShiftBinop.clockConstraints :=
  ShiftBinop.holds_of_check (by kernel_rfl)

/-- `XOR x1, x0, x0` (`0x000040B3`) at ROM address 0, zero registers and RAM. -/
def initial : RV.State where
  pc := 0
  regFile _ := 0
  rom a := if a = 0 then 0xB3 else if a = 1 then 0x40 else 0
  mem _ := 0

def cells : List Cell := [.register 0, .register 1]

def program : List ShiftBinop.RVProgramEntry := [⟨0, 0x000040B3#32, ⟨(), 0, 0, 1, ⟨0, 0⟩, 2, 4⟩⟩]

def trace : ShiftBinop.NativeTrace babyBearModulus where
  rows := [row]
  rom := ROM.table [] []
  initial := PCState.boundary 0 (4, 0)
  terminal := row.finish
  initialMemory := [cellToken (.register 0) 0 0 0, cellToken (.register 1) 0 0 0]
  terminalMemory := [cellToken (.register 0) 5 0 0, cellToken (.register 1) 6 0 0]

theorem accepted : Accepted trace :=
  accepted_of_row rfl satisfies rfl (by kernel_rfl) rfl (by decide +kernel)

theorem inputs : ShiftBinop.RVExecutionInputs trace initial cells program where
  distinct := by decide
  aligned := by decide
  image := by kernel_rfl
  initialPC := ⟨(4, 0), rfl⟩
  programImage := ⟨[0], by kernel_rfl⟩
  clocks := ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem decoded : ShiftBinop.RVDecoded trace program := by
  intro current member
  simp only [trace, List.mem_singleton] at member
  subst current
  exact ⟨⟨0, by decide +kernel⟩, by kernel_rfl⟩

end Airbender.NonVacuous.ShiftBinopTrace
