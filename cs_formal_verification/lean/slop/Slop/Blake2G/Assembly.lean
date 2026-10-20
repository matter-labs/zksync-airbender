import Slop.Blake2G.SecondHalf
import Slop.Blake2G.OpIndex

namespace Airbender.Blake2G.Proofs

set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

/-- Supply the eight output limbs from the G fragment's existing intermediates.
    This is witness wiring, not another constraint or reference semantics. -/
def assemble {p : Nat} (base : Nat → ZMod p) (column : Nat) : ZMod p :=
  match column with
  | 17 => secondAlo base | 18 => secondAhi base
  | 21 => base 80 + 512 * base 81 | 22 => base 82 + 512 * base 79
  | 25 => secondClo base | 26 => secondChi base
  | 29 => base 72 + 256 * base 73 | 30 => base 74 + 256 * base 71
  | n => base n

/-- A native G fragment follows from its twelve carries and eighteen queries.
    Its output-assembly equations are checked once for every embedding. -/
theorem assembled_holds {p : Nat} [Fact p.Prime]
    (base : Nat → ZMod p) (setup : Table (ZMod p) (fields 9))
    (flags : ∀ k : Fin 12,
      base Variables.booleanColumns[1 + k.val] = 0 ∨
        base Variables.booleanColumns[1 + k.val] = 1)
    (queries : ∀ i : Fin 18,
      ((FlatOperation.lookups (mixingConstraints setup)).get
        ⟨i.val, by rw [mixing_lookup_count]; exact i.isLt⟩).Contains
          (Verification.environment (assemble base))) :
    FlatOperation.ConstraintsHoldFlat (Verification.environment (assemble base))
      (mixingConstraints setup) := by
  apply FlatOperation.constraintsHoldFlat_iff_forall_mem.mpr
  constructor
  · intro e present
    obtain ⟨i, rfl⟩ := List.mem_iff_get.mp present
    have outputs (j : Fin 8) :
        ((FlatOperation.constraints (mixingConstraints setup)).get
          ⟨j.val, by rw [mixing_constraint_count]; have size := j.isLt; omega⟩).eval
          (Verification.environment (assemble base)) = 0 := by
      fin_cases j <;> op_index <;> simp [Expression.eval, Verification.environment,
        assemble, secondAlo, secondAhi, secondClo, secondChi,
        firstAlo, firstAhi, firstClo, firstChi] <;> ring
    have carries (k : Fin 12) :
        ((FlatOperation.constraints (mixingConstraints setup)).get
          ⟨8 + k.val, by rw [mixing_constraint_count]; have size := k.isLt; omega⟩).eval
          (Verification.environment (assemble base)) = 0 := by
      have flag := flags k
      fin_cases k <;> simp [Variables.booleanColumns] at flag
      all_goals rcases flag with flag | flag
      all_goals op_index
      all_goals simp [Expression.eval, Verification.environment, assemble, flag]
    change Fin 20 at i
    by_cases early : i.val < 8
    · exact outputs ⟨i.val, early⟩
    · have equation := carries ⟨i.val - 8, by have size := i.isLt; omega⟩
      have index : 8 + (i.val - 8) = i.val := by omega
      simp only [index] at equation
      exact equation
  · intro query present
    obtain ⟨i, rfl⟩ := List.mem_iff_get.mp present
    change Fin 18 at i
    exact queries i

end Airbender.Blake2G.Proofs
