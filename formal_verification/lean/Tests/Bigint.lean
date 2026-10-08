import Airbender.Review.Bigint.Theorems

namespace Tests.Bigint
open Airbender

/-- Simultaneous ADD and SUB requests cannot satisfy the imported row, regardless
    of operands or supplied fixed-table rows. The carry bit is not an opcode. -/
theorem twoOperationsRejected (setup : Table (ZMod babyBearModulus) (fields 3))
    (input register : Arithmetic.Word) (w : Nat → ZMod babyBearModulus) :
    let output : Bigint.Control.Output := ⟨register, #v[true, true, false, false, false, false, false, false]⟩
    ¬ (Bigint.Control.circuitModel setup).relation input output w := by
  intro output row
  have valid := Bigint.Control.babyBear_soundness setup input output w row
  have count := valid.2.2.1
  norm_num [Bigint.Control.operationCount, output, Fin.sum_univ_succ] at count

/-- Incoming control is a byte enforced by native equations, not a range premise. -/
theorem oversizedControlRejected (setup : Table (ZMod babyBearModulus) (fields 3))
    (input : Arithmetic.Word) (output : Bigint.Control.Output) (w : Nat → ZMod babyBearModulus)
    (oversized : 256 ≤ input.lo) :
    ¬ (Bigint.Control.circuitModel setup).relation input output w := by
  intro row
  have valid := Bigint.Control.babyBear_soundness setup input output w row
  have bound := valid.2.1
  omega

private def zeroSetup : Table (ZMod babyBearModulus) (fields 3) := .fromStatic {
  name := "BigintZeroEntries"
  length := 6
  row i := #v[0, 0, (#v[41, 26, 25, 24, 22, 23] : Vector (ZMod babyBearModulus) 6)[i]]
  index _ := 0
  Spec x := ∃ i : Fin 6, x = #v[0, 0, (#v[41, 26, 25, 24, 22, 23] : Vector (ZMod babyBearModulus) 6)[i]]
  contains_iff _ := Iff.rfl
}

namespace Additive
open Airbender.Bigint.Additive

private def zero : Vector Nat 16 := Vector.replicate 16 0
private def maximum : Vector Nat 16 := Vector.replicate 16 65535
private def one : Vector Nat 16 := Vector.ofFn fun i => if i.val = 0 then 1 else 0

-- A concrete all-zero ADD row checks that the full imported relation is
-- satisfiable. The six fixed rows are only this test's queried zero entries,
-- not a claimed extraction of the production setup.
private def zeroAddRow : Nat → ZMod babyBearModulus
  | 0 | 55 | 59 | 212 | 214 | 215 => 1
  | _ => 0

set_option maxRecDepth 16384 in
theorem zeroAddSatisfies :
    FlatOperation.ConstraintsHoldFlat (Verification.environment zeroAddRow)
      (Bigint.importedConstraints zeroSetup) := by
  simp [Bigint.importedConstraints, FlatOperation.ConstraintsHoldFlat,
    Verification.environment, Expression.eval, zeroAddRow, Lookup.Contains, Table.toRaw, fromElements]
  repeat' apply And.intro
  all_goals solve
    | decide
    | (apply Verification.range16_contains; decide)
    | (exact ⟨⟨0, by decide⟩, rfl⟩)
    | (exact ⟨⟨1, by decide⟩, rfl⟩)
    | (exact ⟨⟨2, by decide⟩, rfl⟩)
    | (exact ⟨⟨3, by decide⟩, rfl⟩)
    | (exact ⟨⟨4, by decide⟩, rfl⟩)
    | (exact ⟨⟨5, by decide⟩, rfl⟩)

/-- A full native witness is observed through the same mapping and shared
    soundness property used by the public theorem. -/
theorem zeroAddSoundness : spec ⟨.add, zero, zero, false⟩ ⟨zero, ⟨0, 0⟩⟩ := by
  apply babyBear_soundness zeroSetup _ _ zeroAddRow
  refine ⟨?_, zeroAddSatisfies, ?_⟩
  · constructor <;> intro i <;> simp [zero, Arithmetic.limbBase]
  · constructor
    · rfl
    · rfl
    · intro i; fin_cases i <;> rfl
    · intro i; fin_cases i <;> rfl
    · intro i; fin_cases i <;> rfl
    · rfl

-- Boundary cases of the project's pure custom arithmetic reference.
example : spec ⟨.add, maximum, maximum, true⟩ ⟨maximum, ⟨1, 0⟩⟩ := by unfold spec; decide
example : spec ⟨.sub, zero, one, false⟩ ⟨maximum, ⟨1, 0⟩⟩ := by unfold spec; decide
example : spec ⟨.reverseSub, one, zero, false⟩ ⟨maximum, ⟨1, 0⟩⟩ := by unfold spec; decide
example : spec ⟨.copy, zero, maximum, true⟩ ⟨zero, ⟨1, 0⟩⟩ := by unfold spec; decide

/-- A wrapped result cannot silently drop the returned carry, in any native
    witness or supplied fixed setup. This uses the imported-circuit theorem. -/
theorem missingCarryRejected (setup : Table (ZMod babyBearModulus) (fields 3))
    (w : Nat → ZMod babyBearModulus) :
    ¬ (circuitModel setup).relation ⟨.add, maximum, zero, true⟩ ⟨zero, ⟨0, 0⟩⟩ w := by
  intro row
  have bounds : InterfaceAssumptions ⟨.add, maximum, zero, true⟩ ⟨zero, ⟨0, 0⟩⟩ w := by
    constructor <;> intro i <;> simp [maximum, zero, Arithmetic.limbBase]
  have valid := babyBear_soundness setup _ _ w ⟨bounds, row⟩
  have impossible : ¬ spec ⟨.add, maximum, zero, true⟩ ⟨zero, ⟨0, 0⟩⟩ := by unfold spec; decide
  exact impossible valid

/-- Underflow must return a borrow even when all destination limbs are correct. -/
theorem missingBorrowRejected (setup : Table (ZMod babyBearModulus) (fields 3))
    (w : Nat → ZMod babyBearModulus) :
    ¬ (circuitModel setup).relation ⟨.sub, zero, one, false⟩ ⟨maximum, ⟨0, 0⟩⟩ w := by
  intro row
  have bounds : InterfaceAssumptions ⟨.sub, zero, one, false⟩ ⟨maximum, ⟨0, 0⟩⟩ w := by
    constructor <;> intro i <;> simp [one, zero, Arithmetic.limbBase]
    split <;> decide
  have valid := babyBear_soundness setup _ _ w ⟨bounds, row⟩
  have impossible : ¬ spec ⟨.sub, zero, one, false⟩ ⟨maximum, ⟨0, 0⟩⟩ := by unfold spec; decide
  exact impossible valid

end Additive
namespace Equality
open Airbender.Bigint.Equality

private def zero : Vector Nat 16 := Vector.replicate 16 0

-- Incoming carry is set, but EQ must ignore it and still report equality.
private def equalRow : Nat → ZMod babyBearModulus
  | 55 => 96
  | 0 | 57 | 64 | 65 | 212 | 214 | 215 | 216 => 1
  | _ => 0

set_option maxRecDepth 16384 in
theorem equalSatisfies :
    FlatOperation.ConstraintsHoldFlat (Verification.environment equalRow)
      (Bigint.importedConstraints zeroSetup) := by
  simp [Bigint.importedConstraints, FlatOperation.ConstraintsHoldFlat,
    Verification.environment, Expression.eval, equalRow, Lookup.Contains, Table.toRaw, fromElements]
  repeat' apply And.intro
  all_goals solve
    | decide
    | (apply Verification.range16_contains; decide)
    | (exact ⟨⟨0, by decide⟩, rfl⟩)
    | (exact ⟨⟨1, by decide⟩, rfl⟩)
    | (exact ⟨⟨2, by decide⟩, rfl⟩)
    | (exact ⟨⟨3, by decide⟩, rfl⟩)
    | (exact ⟨⟨4, by decide⟩, rfl⟩)
    | (exact ⟨⟨5, by decide⟩, rfl⟩)

theorem equalSoundness : spec ⟨zero, zero⟩ ⟨zero, ⟨1, 0⟩⟩ := by
  apply babyBear_soundness zeroSetup _ _ equalRow
  refine ⟨?_, equalSatisfies, ?_⟩
  · constructor <;> intro i <;> simp [zero, Arithmetic.limbBase]
  · constructor
    · rfl
    · intro i; fin_cases i <;> rfl
    · intro i; fin_cases i <;> rfl
    · intro i; fin_cases i <;> rfl
    · rfl

/-- No native witness can falsely report that two zero operands differ. -/
theorem falseInequalityRejected (setup : Table (ZMod babyBearModulus) (fields 3))
    (w : Nat → ZMod babyBearModulus) :
    ¬ (circuitModel setup).relation ⟨zero, zero⟩ ⟨zero, ⟨0, 0⟩⟩ w := by
  intro row
  have bounds : InterfaceAssumptions ⟨zero, zero⟩ ⟨zero, ⟨0, 0⟩⟩ w := by
    constructor <;> intro i <;> simp [zero, Arithmetic.limbBase]
  have valid := babyBear_soundness setup _ _ w ⟨bounds, row⟩
  have impossible : ¬ spec ⟨zero, zero⟩ ⟨zero, ⟨0, 0⟩⟩ := by unfold spec; decide
  exact impossible valid

end Equality
end Tests.Bigint
