import Airbender.Proofs.UnifiedReduced
import Airbender.Proofs.BabyBear

namespace Tests.UnifiedReduced
open Airbender Airbender.Arithmetic

-- A row using only the setup's disabled-query entry.
private def zeroSetup : Table (ZMod babyBearModulus) (fields 10) := .fromStatic {
  name := "UnifiedDisabledQueries"
  length := 1
  row _ := #v[0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  index _ := 0
  Spec x := ∃ i : Fin 1, x = (fun (_ : Fin 1) => #v[0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) i
  contains_iff _ := Iff.rfl
}

private def row : Nat → ZMod babyBearModulus
  | 0 => 65534
  | 1 | 30 => 2
  | 4 | 11 | 128 | 129 | 130 => 1
  | 31 => 3
  | 32 => 4
  | _ => 0

set_option maxRecDepth 8192 in
private theorem satisfies :
    FlatOperation.ConstraintsHoldFlat (Verification.environment row)
      (UnifiedReduced.importedConstraints zeroSetup) := by
  simp [UnifiedReduced.importedConstraints, FlatOperation.ConstraintsHoldFlat,
    Verification.environment, Expression.eval, row, Lookup.Contains, Table.toRaw, fromElements]
  repeat' apply And.intro
  all_goals solve
    | decide
    | (apply Verification.range16_contains; decide)
    | (exact ⟨⟨0, by decide⟩, rfl⟩)

example : (Word.mk (row 30).val (row 31).val).toBitVec = (Word.mk 65534 2).toBitVec + 4 := by
  have result := UnifiedReduced.Proofs.pc_successor (p := babyBearModulus)
    (initial := ⟨65534, 2⟩) (final := ⟨(row 30).val, (row 31).val⟩)
    (by decide) satisfies rfl ⟨rfl, rfl, rfl, rfl⟩
    ⟨rfl, rfl, rfl, rfl⟩ ⟨by decide, by decide⟩
  exact result.2.2

example : (∑ i : Fin 18, (row UnifiedReduced.Variables.dispatchColumns[i]).val) ≤ 1 :=
  UnifiedReduced.Proofs.dispatch_count (by decide) satisfies rfl

end Tests.UnifiedReduced
