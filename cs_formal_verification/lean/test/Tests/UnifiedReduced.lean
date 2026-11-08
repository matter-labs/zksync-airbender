module
public import Slop.UnifiedReduced.Claims
public import Slop.UnifiedReduced.Completeness.Arith
import all Init.Data.Array.DecidableEq -- until Lean 4.35 exposes Array/Vector ofFn/DecidableEq (lean4#14989, #14988, #14270)
import all Init.Data.Vector.Basic -- until Lean 4.35 exposes Array/Vector ofFn/DecidableEq (lean4#14989, #14988, #14270)

@[expose] public section

namespace Tests.UnifiedReduced
open Airbender Airbender.Arithmetic

-- A row using only the setup's disabled-query entry.
def zeroSetup : Table (ZMod babyBearModulus) (fields 10) := .fromStatic {
  name := "UnifiedDisabledQueries"
  length := 1
  row _ := #v[0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  index _ := 0
  Spec x := ∃ i : Fin 1, x = (fun (_ : Fin 1) => #v[0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) i
  contains_iff _ := Iff.rfl
}

private theorem zeroSetup_zero : UnifiedReduced.Completeness.ZeroRow zeroSetup := by
  intro env entry h
  change ∃ i : Fin 1, entry.map (Expression.eval env) = #v[0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  exact ⟨0, h.trans (by decide)⟩

def rowWitness : UnifiedReduced.Completeness.Arith :=
  ⟨⟨65532, 2, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩
def row : Nat → ZMod babyBearModulus := rowWitness.honest

theorem satisfies :
    FlatOperation.ConstraintsHoldFlat (Verification.environment row)
      (UnifiedReduced.importedConstraints zeroSetup) :=
  UnifiedReduced.Completeness.Arith.complete_core _
    (by refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide) _ zeroSetup_zero

example : (Word.mk (row 30).val (row 31).val).toBitVec = (Word.mk 65532 2).toBitVec + 4 := by
  have result := UnifiedReduced.Proofs.pc_successor (p := babyBearModulus)
    (initial := ⟨65532, 2⟩) (final := ⟨(row 30).val, (row 31).val⟩)
    (by decide) satisfies rfl ⟨rfl, rfl, rfl, rfl⟩
    ⟨rfl, rfl, rfl, rfl⟩ ⟨by decide, by decide⟩
  exact result.2.2

example : (∑ i : Fin 18, (row UnifiedReduced.Variables.dispatchColumns[i]).val) ≤ 1 :=
  UnifiedReduced.Proofs.dispatch_count (by decide) satisfies rfl

open Airbender.Reference.RiscV

def aliasedWitness : UnifiedReduced.Completeness.Arith :=
  { rowWitness with rs1 := 1, rs2 := 1, rd := 1, aLo := 123, bLo := 123 }
def aliasedRow : Nat → ZMod babyBearModulus := aliasedWitness.honest

private theorem aliased_satisfies :
    FlatOperation.ConstraintsHoldFlat (Verification.environment aliasedRow)
      (UnifiedReduced.importedConstraints zeroSetup) :=
  UnifiedReduced.Completeness.Arith.complete_core _
    (by refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide) _ zeroSetup_zero

example : ¬ FlatOperation.ConstraintsHoldFlat
    (Verification.environment (fun i => if i = 12 then 1 else aliasedRow i))
    (UnifiedReduced.importedConstraints zeroSetup) := by
  intro h
  have excluded := UnifiedReduced.Proofs.dispatch_exclusive (by decide) h rfl 0 rfl 1 (by decide)
  change (1 : ZMod babyBearModulus) = 0 at excluded
  exact one_ne_zero excluded

private def triWitness : UnifiedReduced.Completeness.Arith :=
  ⟨rowWitness.frame, 3, 1, 1, 1, 65535, 65535, 65535, 65535, 0, 0, 65535, 65535⟩
private def triRow : Nat → ZMod babyBearModulus := triWitness.honest

private theorem tri_satisfies :
    FlatOperation.ConstraintsHoldFlat (Verification.environment triRow)
      (UnifiedReduced.importedConstraints zeroSetup) :=
  UnifiedReduced.Completeness.Arith.complete_core _
    (by refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide) _ zeroSetup_zero

open Trace
set_option warningAsError true
set_option maxRecDepth 16384

def nativeWitness (rollover : Bool) : UnifiedReduced.Completeness.Arith :=
  { aliasedWitness with
    frame := ⟨65532, 2, if rollover then 524284 else 4, if rollover then 7 else 0, 0, 0,
      if rollover then 524284 else 4, if rollover then 7 else 0,
      if rollover then 524285 else 5, if rollover then 7 else 0⟩
    oldLo := 123 }
def nativeAssignment (rollover : Bool) : Nat → ZMod babyBearModulus :=
  (nativeWitness rollover).honest

private theorem native_constraints (rollover : Bool) : FlatOperation.ConstraintsHoldFlat
    (Verification.environment (nativeAssignment rollover))
    (Airbender.UnifiedReduced.clockConstraints zeroSetup) := by
  cases rollover <;>
    exact UnifiedReduced.Completeness.Arith.complete _
      (by refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide)
      (by refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide) _ zeroSetup_zero

def nativeToken (timeLo timeHi value : Nat) : MemoryToken babyBearModulus :=
  ⟨(Cell.register 1).addressCode, (timeLo, timeHi), Nat.pair value 0⟩

def nativeTrace (rollover : Bool) : UnifiedTrace babyBearModulus where
  rows := [⟨.machine, nativeAssignment rollover⟩]
  rom := zeroSetup
  initial := ⟨(65532, 2), (if rollover then 524284 else 4, if rollover then 7 else 0)⟩
  terminal := ⟨(0, 3), (if rollover then 0 else 8, if rollover then 8 else 0)⟩
  initialMemory := [nativeToken 0 0 123]
  terminalMemory := [nativeToken (if rollover then 524286 else 6) (if rollover then 7 else 0) 246]

private theorem native_accepted (rollover : Bool) : Accepted (nativeTrace rollover) := by
  constructor
  · intro current member
    simp only [nativeTrace, List.mem_singleton] at member
    subst current
    exact native_constraints rollover
  · intro current member
    simp only [nativeTrace, List.mem_singleton] at member
    subst current
    rfl
  · cases rollover <;> exact List.Perm.swap _ _ []
  · cases rollover <;> decide

private theorem native_boundary (rollover : Bool) : ClockBoundary (nativeTrace rollover) := by
  constructor
  · cases rollover <;> constructor <;> decide
  · cases rollover <;> decide
  · intro token member
    simp only [nativeTrace, List.mem_singleton] at member
    subst token
    constructor <;> decide

theorem native_clock_effects (rollover : Bool) :
    ∀ current ∈ (nativeTrace rollover).rows, ClockEffects current.columns current.assignment :=
  Airbender.UnifiedReduced.native_clocks (by decide) (by decide)
    (native_accepted rollover) (native_boundary rollover)

def fabricatedWitness : UnifiedReduced.Completeness.Arith :=
  { nativeWitness false with bLo := 124 }
def fabricatedAssignment : Nat → ZMod babyBearModulus := fabricatedWitness.honest

def fabricatedTrace : UnifiedTrace babyBearModulus :=
  { (nativeTrace false) with
    rows := [⟨.machine, fabricatedAssignment⟩]
    terminalMemory := [nativeToken 6 0 247] }

theorem fabricated_constraints : FlatOperation.ConstraintsHoldFlat
    (Verification.environment fabricatedAssignment)
    (Airbender.UnifiedReduced.clockConstraints zeroSetup) :=
  UnifiedReduced.Completeness.Arith.complete _
    (by refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide)
    (by refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide) _ zeroSetup_zero

theorem fabricated_read_rejected : ¬ Accepted fabricatedTrace := by
  intro accepted
  have impossible : ¬ (fabricatedTrace.initialMemory ++ fabricatedTrace.rows.flatMap Row.writes).Perm
      (fabricatedTrace.terminalMemory ++ fabricatedTrace.rows.flatMap Row.reads) := by decide
  exact impossible accepted.memory

end Tests.UnifiedReduced
