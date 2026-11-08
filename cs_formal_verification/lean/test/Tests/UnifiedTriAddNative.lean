import Slop.UnifiedReduced.Claims
import Slop.UnifiedReduced.Completeness.Arith

namespace Tests.UnifiedTriAddNative
open Airbender Arithmetic UnifiedReduced Trace
set_option warningAsError true
set_option maxRecDepth 16384

private def setup : Table (ZMod babyBearModulus) (fields 10) := .fromStatic {
  name := "UnifiedDisabledQueries"
  length := 1
  row _ := #v[0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  index _ := 0
  Spec x := ∃ i : Fin 1, x = (fun (_ : Fin 1) => #v[0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) i
  contains_iff _ := Iff.rfl
}

private theorem setup_zero : Completeness.ZeroRow setup := by
  intro env entry h
  change ∃ i : Fin 1, entry.map (Expression.eval env) = #v[0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  exact ⟨0, h.trans (by decide)⟩
/-- TRIADD x1 (= x1 + x1 + old x1) at PC 0, clock 4. -/
private def witness : Completeness.Arith :=
  ⟨⟨0, 0, 4, 0, 0, 0, 4, 0, 5, 0⟩, 3, 1, 1, 1, 123, 0, 123, 0, 0, 0, 123, 0⟩
private def assignment : Nat → ZMod babyBearModulus := witness.honest

private def row : Row babyBearModulus UnifiedFamily := ⟨.machine, assignment⟩
private def trace : UnifiedTrace babyBearModulus where
  rows := [row]
  rom := setup
  initial := PCState.boundary 0 (4, 0)
  terminal := PCState.boundary 4 (8, 0)
  initialMemory := [Cell.initialToken (.register 1) 123]
  terminalMemory := [⟨(Cell.register 1).addressCode, (6, 0), Nat.pair 369 0⟩]
private theorem constraints : FlatOperation.ConstraintsHoldFlat
    (Verification.environment assignment) (clockConstraints setup) :=
  Completeness.Arith.complete _
    (by refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide)
    (by refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide) _ setup_zero

private theorem accepted : Accepted trace := by
  constructor
  · intro actual member
    have same := List.mem_singleton.mp member
    subst actual
    exact constraints
  · intro actual member
    have same := List.mem_singleton.mp member
    subst actual
    rfl
  · exact List.Perm.swap _ _ []
  · decide

end Tests.UnifiedTriAddNative
