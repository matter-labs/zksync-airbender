import Airbender.Review.WordMemory.Theorems
import Airbender.Proofs.BabyBear
import Mathlib.Tactic.IntervalCases

namespace Tests.WordMemory
open Airbender
open Airbender.Arithmetic

-- RAM-only rows use the real setup's disabled-ROM zero query. This small fixture
-- supplies that row; it makes no assertion about a ROM image or global memory.
private def zeroTable : Table (ZMod babyBearModulus) (fields 9) := .fromStatic {
  name := "DisabledROMFixture"
  length := 1
  row _ := Vector.replicate 9 0
  index _ := 0
  Spec x := ∃ i : Fin 1, x = (fun (_ : Fin 1) => Vector.replicate 9 0) i
  contains_iff _ := Iff.rfl
}

private def row (store : Bool) : Nat → ZMod babyBearModulus
  | 0 | 17 => 65532
  | 4 | 5 | 12 | 33 | 36 | 44 => 1
  | 6 => if store then 2 else 0
  | 7 | 25 => if store then 0 else 1
  | 8 | 13 => 4
  | 10 => if store then 1 else 0
  | 18 => 64
  | 19 => if store then 2 else 0
  | 20 => if store then 0 else 65
  | 23 | 31 => 1234
  | 24 | 32 => 5678
  | 26 => if store then 65 else 0
  | 38 => 4259840
  | _ => 0

set_option maxRecDepth 4096 in
private theorem satisfies (store : Bool) :
    FlatOperation.ConstraintsHoldFlat (Verification.environment (row store))
      (WordMemory.importedConstraints zeroTable) := by
  cases store <;>
    simp [WordMemory.importedConstraints, FlatOperation.ConstraintsHoldFlat,
      Verification.environment, Expression.eval, row, Lookup.Contains,
      zeroTable, Table.fromStatic, Table.toRaw]
  all_goals repeat' apply And.intro
  all_goals first
    | decide
    | (apply Verification.range16_contains; decide)
    | exact ⟨0, rfl⟩

-- Both actual load/store rows cross a limb boundary in address and PC arithmetic.
example (store : Bool) :
    (Word.mk 0 65).toBitVec = (Word.mk 65532 64).toBitVec + (Word.mk 4 0).toBitVec := by
  apply WordMemory.effective_address (p := babyBearModulus) (by decide) (by decide)
    store (satisfies store)
  · cases store <;> rfl
  · cases store <;> norm_num [row]
  all_goals exact ⟨by decide, by decide⟩

example (store : Bool) :
    (Word.mk 0 1).value = (Word.mk 65532 0).value + 4 := by
  exact (WordMemory.pc_successor (p := babyBearModulus) (by decide) (by decide)
    (satisfies store) ⟨rfl, rfl, rfl, rfl⟩ ⟨by decide, by decide⟩).1

end Tests.WordMemory
