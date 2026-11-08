import Slop.UnifiedReduced.Claims
import Slop.UnifiedReduced.Completeness.Memory

namespace Tests.UnifiedMemory
open Airbender Arithmetic Trace Reference.RiscV
set_option warningAsError true
set_option maxRecDepth 16384

private def zeroSetup : Table (ZMod babyBearModulus) (fields 10) := .fromStatic {
  name := "UnifiedRamDisabledQueries"
  length := 1
  row _ := Vector.replicate 10 0
  index _ := 0
  Spec x := ∃ i : Fin 1, x = (fun (_ : Fin 1) => Vector.replicate 10 0) i
  contains_iff _ := Iff.rfl
}

private theorem zeroSetup_zero : UnifiedReduced.Completeness.ZeroRow zeroSetup := by
  intro env entry h
  change ∃ i : Fin 1, entry.map (Expression.eval env) = Vector.replicate 10 0
  exact ⟨0, h⟩

/-- LW x2, 0(x1) / SW x2, 0(x1) with x1 = 0x400000 and the word 0xbeef1234. -/
private def witness (store : Bool) : UnifiedReduced.Completeness.Memory :=
  ⟨⟨0, 0, 4, 0, 0, 0, 0, 0, 0, 0⟩, store, 1, 2, 0, 64, 0, 0, 0x1234, 0xbeef, 0, 0⟩
private def assignment (store : Bool) : Nat → ZMod babyBearModulus := (witness store).honest

private def row (store : Bool) : Row babyBearModulus UnifiedFamily := ⟨.machine, assignment store⟩

private theorem constraints (store : Bool) : FlatOperation.ConstraintsHoldFlat
    (Verification.environment (assignment store)) (UnifiedReduced.clockConstraints zeroSetup) := by
  cases store <;>
    exact UnifiedReduced.Completeness.Memory.complete _
      (by refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide)
      (by refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide) _ zeroSetup_zero

private def trace (store : Bool) : UnifiedTrace babyBearModulus where
  rows := [row store]
  rom := zeroSetup
  initial := (row store).start
  terminal := (row store).finish
  initialMemory := (row store).ports.toList.map (readToken (assignment store))
  terminalMemory := (row store).ports.toList.map (writeToken (row store).columns (assignment store))

private theorem accepted (store : Bool) : Accepted (trace store) := by
  constructor
  · intro current member
    simp only [trace, List.mem_singleton] at member
    subst current
    exact constraints store
  · intro current member
    simp only [trace, List.mem_singleton] at member
    subst current
    rfl
  · exact List.Perm.swap _ _ []
  · have exchange : ((row store).reads ++ (row store).writes).Perm
        ((row store).writes ++ (row store).reads) := List.perm_append_comm
    simpa [trace, Row.reads, Row.writes, row] using exchange

private theorem boundary (store : Bool) : ClockBoundary (trace store) := by
  constructor
  · cases store <;> constructor <;> decide
  · cases store <;> decide
  · intro token member
    cases store <;>
      simp [trace, row, Row.ports, CircuitLayout.ports,
        UnifiedReduced.importedConstraintsMemoryPorts] at member
    all_goals rcases member with rfl | rfl | rfl
    all_goals constructor <;> decide

end Tests.UnifiedMemory
