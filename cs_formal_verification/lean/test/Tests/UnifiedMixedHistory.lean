module
public import Slop.UnifiedReduced.Claims
public import Slop.UnifiedReduced.Completeness.Arith
import all Init.Data.Array.DecidableEq -- until Lean 4.35 exposes Array/Vector ofFn/DecidableEq (lean4#14989, #14988, #14270)
import all Init.Data.Vector.Basic -- until Lean 4.35 exposes Array/Vector ofFn/DecidableEq (lean4#14989, #14988, #14270)

@[expose] public section

namespace Tests.UnifiedMixedHistory
open Airbender Arithmetic UnifiedReduced Trace
set_option warningAsError true
set_option maxRecDepth 32768

def setup : Table (ZMod babyBearModulus) (fields 10) := .fromStatic {
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
/-- ADDI x1, x1, 1 at PC 0. -/
def arithmeticWitness : Completeness.Arith :=
  ⟨⟨0, 0, 4, 0, 0, 0, 0, 0, 4, 0⟩, 0, 1, 0, 1, 123, 0, 0, 0, 1, 0, 123, 0⟩
/-- TRIADD x1 (= x1 + x1 + old x1) at PC 4. -/
def triaddWitness (value : Nat) : Completeness.Arith :=
  ⟨⟨4, 0, 8, 0, 6, 0, 8, 0, 9, 0⟩, 3, 1, 1, 1, value, 0, value, 0, 0, 0, value, 0⟩
def arithmetic : Nat → ZMod babyBearModulus := arithmeticWitness.honest
def triadd (value : Nat) : Nat → ZMod babyBearModulus := (triaddWitness value).honest
def standardRow : Row babyBearModulus UnifiedFamily := ⟨.machine, arithmetic⟩
def customRow (value : Nat) : Row babyBearModulus UnifiedFamily := ⟨.machine, triadd value⟩
def trace (value : Nat) : UnifiedTrace babyBearModulus where
  rows := [customRow value, standardRow]
  rom := setup
  initial := PCState.boundary 0 (4, 0)
  terminal := PCState.boundary 8 (12, 0)
  initialMemory := [(.register 1 : Cell).initialToken 123, (.register 0 : Cell).initialToken 0]
  terminalMemory := [⟨(Cell.register 1).addressCode, (10, 0), Nat.pair (3 * value) 0⟩,
    ⟨(Cell.register 0).addressCode, (5, 0), 0⟩]

private theorem constraints (value : Fin 3) : FlatOperation.ConstraintsHoldFlat
    (Verification.environment (if value = 0 then arithmetic else triadd (if value = 1 then 124 else 125))) (clockConstraints setup) := by
  fin_cases value <;>
    exact Completeness.Arith.complete _
      (by refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide)
      (by refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide) _ setup_zero

private theorem accepted : Accepted (trace 124) := by
  constructor
  · intro actual member
    simp only [trace, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact constraints 1
    · exact constraints 0
  · intro actual member
    simp only [trace, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> rfl
  · exact (List.Perm.swap _ _ _).trans (List.Perm.cons _ (List.Perm.swap _ _ []))
  · decide +kernel

theorem fabricated_read_locally_satisfies : FlatOperation.ConstraintsHoldFlat
    (Verification.environment (triadd 125)) (clockConstraints setup) := constraints 2

theorem fabricated_custom_read_breaks_matching :
    ¬((trace 125).initialMemory ++ (trace 125).memorySteps.map Prod.snd).Perm
      ((trace 125).terminalMemory ++ (trace 125).memorySteps.map Prod.fst) := by decide +kernel

end Tests.UnifiedMixedHistory
