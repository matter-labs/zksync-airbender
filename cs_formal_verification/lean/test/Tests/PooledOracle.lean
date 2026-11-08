module
public import Slop.Trace.PooledOracleConsumption
public import Tests.ShiftBinopTimestamp
public import Tests.TraceExecution
public import Slop.AddSub.Completeness.Row
public import Human.Circuits.JumpBranchSlt.Jump
public import Human.Circuits.SubwordMemory.Output
public import Human.Circuits.WordMemory.Output
public import Human.Helpers.Memory.Native
public import Slop.JumpBranchSlt.Branch
public import Slop.JumpBranchSlt.Jump
public import Slop.JumpBranchSlt.PortReads
public import Slop.MulDiv.PortReads
public import Slop.MulDiv.Soundness
public import Slop.MulDiv.Values
public import Slop.ShiftBinop.PortReads
public import Slop.ShiftBinop.Ports
public import Slop.SubwordMemory.PortReads
public import Slop.Trace.CompositionCore
public import Slop.Trace.Family.Values
public import Slop.Trace.OracleConsumption

@[expose] public section

namespace Tests.PooledOracle
open Airbender Arithmetic Trace
open Trace.Proofs
set_option warningAsError true
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

-- CSRRW x1 oracle reads at clocks 4 and 12, with PC 0 and 8.
private def readInput (second : Bool) : AddSub.Completeness.Row where
  frame := ⟨if second then 8 else 0, 0, if second then 12 else 4, 0, if second then 9 else 0, 0,
    if second then 12 else 4, 0, if second then 10 else 0, 0⟩
  op := .oracle
  active := 1
  rd := 1
  respLo := if second then 0xbeef else 0x5678
  respHi := if second then 0 else 0x1234

private def readAssignment (second : Bool) : Nat → ZMod babyBearModulus := (readInput second).honest

private def shiftAssignment : Nat → ZMod babyBearModulus
  | 0 => 4
  | 2 | 13 | 23 => 8
  | 15 => 12
  | 17 => 5
  | 29 => 0x5678
  | 30 => 0x1234
  | 33 => 6
  | i => if i = 14 then 0 else Tests.ShiftBinopTimestamp.assignment false i

private theorem read_constraints (second : Bool) : FlatOperation.ConstraintsHoldFlat
    (Verification.environment (readAssignment second)) AddSub.clockConstraints := by
  apply AddSub.Completeness.Row.complete <;> cases second
  all_goals first | addsub_row_valid | addsub_frame_valid

private theorem shift_constraints : FlatOperation.ConstraintsHoldFlat
    (Verification.environment shiftAssignment) ShiftBinop.clockConstraints := by
  apply Verification.holds_append (left := ShiftBinop.importedConstraints)
    (right := ShiftBinop.importedConstraintsTimestampLookups)
  · have core := Tests.ShiftBinop.satisfies
    simp [ShiftBinop.importedConstraints, FlatOperation.ConstraintsHoldFlat,
      Lookup.Contains, Vector.map, Expression.eval, Verification.environment, shiftAssignment,
      Tests.ShiftBinopTimestamp.assignment, Tests.ShiftBinop.row,
      Verification.range16, Verification.shiftBinopLookup,
      show (4 : ZMod babyBearModulus) + 4 + -8 = 0 by decide,
      show (8 : ZMod babyBearModulus) + 4 + -12 = 0 by decide] at core ⊢
    refine ⟨?_, ?_, core.2.2.2.2⟩
    · have bound := Verification.range16_contains
        (entry := Expression.const (8 : ZMod babyBearModulus))
        (env := Verification.environment shiftAssignment) (by decide)
      simpa [Verification.range16, Lookup.Contains, Vector.map, Expression.eval,
        Verification.environment] using bound
    · have bound := Verification.range16_contains
        (entry := Expression.const (0 : ZMod babyBearModulus))
        (env := Verification.environment shiftAssignment) (by decide)
      simpa [Verification.range16, Lookup.Contains, Vector.map, Expression.eval,
        Verification.environment] using bound
  · simp [ShiftBinop.importedConstraintsTimestampLookups, FlatOperation.ConstraintsHoldFlat]
    repeat' apply And.intro
    all_goals apply Trace.Proofs.range_contains
    all_goals simp [Expression.eval, Verification.environment, shiftAssignment,
      Tests.ShiftBinopTimestamp.assignment]
    all_goals decide

theorem foreign_selector_ignored (family : PooledFamily) (other : family ≠ .addSub) :
    NonDeterminism.Pooled.isRead (⟨family, fun _ => 1⟩ : Row babyBearModulus PooledFamily) = false := by
  cases family <;> simp_all [NonDeterminism.Pooled.isRead]

end Tests.PooledOracle
