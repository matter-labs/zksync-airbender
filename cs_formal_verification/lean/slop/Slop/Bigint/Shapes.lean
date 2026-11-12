module
public import Slop.Bigint.OpIndex
public import Slop.Templates
public import Mathlib.Tactic.FinCases
public import Slop.CleanCore.Circuit.Operations

@[expose] public section

/-!
The repeated imported constraints and queries of the bigint circuit, as templates. Each `*_shape`
lemma checks one family against its template, one closed fact per index (`op_index` + `rfl`); the
proofs then evaluate the template once, for every index, instead of unfolding the constraint list
per index (lean-strategies §2.1).
-/

namespace Airbender.Bigint.Shapes
open Templates
set_option warningAsError true

/-- Column of left limb `j` (`Variables.leftLimbs`). -/
def leftColumn (j : Nat) : Nat := 5 + 4 * (j / 2) + j % 2

/-- Column of written limb `j` (`Variables.writtenLimbs`). -/
def writtenColumn (j : Nat) : Nat := 7 + 4 * (j / 2) + j % 2

/-- Constraint `3 + i`: the additive step of limb `i`, selected by the opcode bits. The carry into
    limb 0 is the selected input carry (column 65); limb `i + 1` takes carry `82 + i + 1`. -/
def stepExpr {p : Nat} (i : Nat) : Expression (ZMod p) :=
  let left := leftColumn i
  let right := 39 + i
  let result := 67 + i
  let base := sumFrom (constant (Int.ofNat 0)) [pair left 59, pair result 60, pair left 61,
    pair result 64, pair right 59, pair right 60, pair result 61, pair right 64, pair right 66,
    product (constant (Int.negSucc 0)) (sumFrom (constant (Int.ofNat 0)) [pair result 59,
      pair left 60, pair right 61, pair left 64, pair result 66])]
  let carried := if i = 0 then sumFrom base [pair 65 59, pair 65 60, pair 65 61, pair 65 66]
    else base.add (cell (82 + i))
  carried.add (product (constant (Int.negSucc 65535)) (cell (83 + i)))

/-- Constraint `51 + i`: result limb `194 + i` is the selected additive or product limb. -/
def definitionExpr {p : Nat} (i : Nat) : Expression (ZMod p) :=
  (cell (194 + i)).add ((constant (Int.negSucc 0)).mul (sumFrom (constant (Int.ofNat 0))
    [pair (67 + i) 59, pair (67 + i) 60, pair (67 + i) 61, pair (67 + i) 64, pair (67 + i) 66,
      pair (131 + i) 62, pair (131 + i) 63]))

/-- Constraint `67 + i`: written limb `i` is the selected result. -/
def writeExpr {p : Nat} (i : Nat) : Expression (ZMod p) :=
  sumFrom (constant (Int.ofNat 0)) [pair (67 + i) 59, pair (67 + i) 60, pair (67 + i) 61,
    pair (leftColumn i) 64, pair (131 + i) 62, pair (147 + i) 63, pair (67 + i) 66,
    product (constant (Int.negSucc 0)) (cell (writtenColumn i))]

theorem left_column (j : Fin 16) : Variables.leftLimbs[j] = leftColumn j.val := by
  simp only [Variables.leftLimbs, leftColumn, Fin.getElem_fin, Vector.getElem_ofFn]

theorem written_column (j : Fin 16) : Variables.writtenLimbs[j] = writtenColumn j.val := by
  simp only [Variables.writtenLimbs, writtenColumn, Fin.getElem_fin, Vector.getElem_ofFn]

theorem right_column (j : Fin 16) : Variables.rightLimbs[j] = 39 + j.val := by
  simp only [Variables.rightLimbs, Fin.getElem_fin, Vector.getElem_ofFn]

variable {p : Nat} [Fact p.Prime]

theorem step_eval (w : Nat → ZMod p) (i : Nat) :
    (stepExpr i : Expression (ZMod p)).eval (Verification.environment w) =
      w (leftColumn i) * w 59 + w (67 + i) * w 60 + w (leftColumn i) * w 61 + w (67 + i) * w 64 +
        w (39 + i) * w 59 + w (39 + i) * w 60 + w (67 + i) * w 61 + w (39 + i) * w 64 +
        w (39 + i) * w 66 -
        (w (67 + i) * w 59 + w (leftColumn i) * w 60 + w (39 + i) * w 61 +
          w (leftColumn i) * w 64 + w (67 + i) * w 66) +
        (if i = 0 then w 65 * (w 59 + w 60 + w 61 + w 66) else w (82 + i)) -
        65536 * w (83 + i) := by
  unfold stepExpr
  dsimp only
  split_ifs <;> simp only [List.foldl, Expression.eval, Verification.environment] <;> push_cast <;>
    ring

theorem definition_eval (w : Nat → ZMod p) (i : Nat) :
    (definitionExpr i : Expression (ZMod p)).eval (Verification.environment w) =
      w (194 + i) - (w (67 + i) * (w 59 + w 60 + w 61 + w 64 + w 66) +
        w (131 + i) * (w 62 + w 63)) := by
  simp only [definitionExpr, List.foldl, Expression.eval, Verification.environment]
  push_cast
  ring

theorem write_eval (w : Nat → ZMod p) (i : Nat) :
    (writeExpr i : Expression (ZMod p)).eval (Verification.environment w) =
      w (67 + i) * (w 59 + w 60 + w 61 + w 66) + w (leftColumn i) * w 64 +
        w (131 + i) * w 62 + w (147 + i) * w 63 - w (writtenColumn i) := by
  simp only [writeExpr, List.foldl, Expression.eval, Verification.environment]
  push_cast
  ring

/-- Constraints `3 + i`, `51 + i` and `67 + i` of every limb `i`. -/
theorem limb_shapes (setup : Table (ZMod p) (fields 3)) (i : Fin 16) :
    (FlatOperation.constraints (importedConstraints setup)).get
        ⟨3 + i.val, by rw [constraint_count]; omega⟩ = stepExpr i.val ∧
      (FlatOperation.constraints (importedConstraints setup)).get
        ⟨51 + i.val, by rw [constraint_count]; omega⟩ = definitionExpr i.val ∧
      (FlatOperation.constraints (importedConstraints setup)).get
        ⟨67 + i.val, by rw [constraint_count]; omega⟩ = writeExpr i.val := by
  fin_cases i <;> op_index <;> exact ⟨rfl, rfl, rfl⟩

/-- Constraint `3 + i`, evaluated. -/
theorem step_holds {setup : Table (ZMod p) (fields 3)} {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup))
    (i : Fin 16) :
    (stepExpr i.val : Expression (ZMod p)).eval (Verification.environment w) = 0 := by
  have gate := Verification.assertion_of_holds h ⟨3 + i.val, by rw [constraint_count]; omega⟩
  rwa [(limb_shapes setup i).1] at gate

/-- Constraint `51 + i`, evaluated. -/
theorem definition_holds {setup : Table (ZMod p) (fields 3)} {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup))
    (i : Fin 16) :
    w (194 + i.val) = w (67 + i.val) * (w 59 + w 60 + w 61 + w 64 + w 66) +
      w (131 + i.val) * (w 62 + w 63) := by
  have gate := Verification.assertion_of_holds h ⟨51 + i.val, by rw [constraint_count]; omega⟩
  rw [(limb_shapes setup i).2.1, definition_eval] at gate
  linear_combination gate

/-- Constraint `67 + i`, evaluated. -/
theorem write_holds {setup : Table (ZMod p) (fields 3)} {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup))
    (i : Fin 16) :
    w Variables.writtenLimbs[i] = w (67 + i.val) * (w 59 + w 60 + w 61 + w 66) +
      w Variables.leftLimbs[i] * w 64 + w (131 + i.val) * w 62 + w (147 + i.val) * w 63 := by
  have gate := Verification.assertion_of_holds h ⟨67 + i.val, by rw [constraint_count]; omega⟩
  rw [(limb_shapes setup i).2.2, write_eval] at gate
  rw [written_column, left_column]
  linear_combination -gate

/-- Constraints `91 + i`: the eight control bits. -/
theorem control_shape (setup : Table (ZMod p) (fields 3)) (i : Fin 8) :
    (FlatOperation.constraints (importedConstraints setup)).get
      ⟨91 + i.val, by rw [constraint_count]; omega⟩ = flag (59 + i.val) := by
  fin_cases i <;> op_index

/-- Constraints `99 + i`: the sixteen carries of the additive gates. -/
theorem carry_shape (setup : Table (ZMod p) (fields 3)) (i : Fin 16) :
    (FlatOperation.constraints (importedConstraints setup)).get
      ⟨99 + i.val, by rw [constraint_count]; omega⟩ = flag (83 + i.val) := by
  fin_cases i <;> op_index

/-- Lookups `i` and `16 + i`: the sixteen-bit ranges of the high product limbs and of the
    results. -/
theorem range_shape (setup : Table (ZMod p) (fields 3)) (i : Fin 16) :
    (FlatOperation.lookups (importedConstraints setup)).get
        ⟨i.val, by rw [lookup_count]; omega⟩ = Verification.range16 (entry (147 + i.val)) ∧
      (FlatOperation.lookups (importedConstraints setup)).get
        ⟨16 + i.val, by rw [lookup_count]; omega⟩ =
          Verification.range16 (entry (194 + i.val)) := by
  refine ⟨?_, ?_⟩ <;> fin_cases i <;> op_index

/-- Lookups `34 + i` and `50 + i`: each source limb with its low byte (tag 41). -/
theorem low_byte_shape (setup : Table (ZMod p) (fields 3)) (i : Fin 16) :
    (FlatOperation.lookups (importedConstraints setup)).get
        ⟨34 + i.val, by rw [lookup_count]; omega⟩ = Lookup.mk setup.toRaw
          #v[entry (leftColumn i.val), entry (99 + i.val),
            tagEntry 41] ∧
      (FlatOperation.lookups (importedConstraints setup)).get
        ⟨50 + i.val, by rw [lookup_count]; omega⟩ = Lookup.mk setup.toRaw
          #v[entry (39 + i.val), entry (115 + i.val),
            tagEntry 41] := by
  refine ⟨?_, ?_⟩ <;> fin_cases i <;> op_index <;> rfl

end Airbender.Bigint.Shapes
