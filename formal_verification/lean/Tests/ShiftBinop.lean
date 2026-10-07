import Airbender.Review.ShiftBinop.Theorems
import Airbender.Proofs.BabyBear
import Mathlib.Tactic.IntervalCases

namespace Tests.ShiftBinop
open Airbender

-- XOR x0,x0, with a PC limb carry or a noncanonical final low limb.
-- The destination register index is nonzero; every real byte query retains its tag.
private def row (badPC : Bool) : Nat → ZMod babyBearModulus
  | 0 => 65532
  | 4 | 7 | 12 => 1
  | 10 | 15 | 64 | 73 | 82 | 91 => 4
  | 13 => if badPC then 65536 else 0
  | 14 => if badPC then 0 else 1
  | 55 => 3
  | _ => 0

private theorem satisfies :
    FlatOperation.ConstraintsHoldFlat (Verification.environment (row false))
      Airbender.ShiftBinop.importedConstraints := by
  simp [Airbender.ShiftBinop.importedConstraints, FlatOperation.ConstraintsHoldFlat,
      Expression.eval, Verification.environment, row]
  repeat' apply And.intro
  all_goals solve
    | (apply Verification.range16_contains; decide)
    | (with_unfolding_all change ∃ i : Fin 524545,
         (#v[0, 0, 0, 0, 0, 0, 0, 0, 0, 3] : Vector (ZMod babyBearModulus) 10) =
           (Verification.shiftBinopRow i).map (fun (n : Nat) => (n : ZMod babyBearModulus))
       refine ⟨⟨1, by decide⟩, ?_⟩
       apply Vector.ext
       intro i bound
       rw [Vector.getElem_map]
       interval_cases i <;> norm_num [Verification.shiftBinopRow])
    | (with_unfolding_all change ∃ i : Fin 524545,
         (#v[0, 0, 0, 0, 0, 0, 0, 0, 0, 4] : Vector (ZMod babyBearModulus) 10) =
           (Verification.shiftBinopRow i).map (fun (n : Nat) => (n : ZMod babyBearModulus))
       refine ⟨⟨257, by decide⟩, ?_⟩
       have zeroRow : Verification.shiftBinopRow ⟨257, by decide⟩ =
           (#v[0, 0, 0, 0, 0, 0, 0, 0, 0, 4] : Vector Nat 10) := by decide
       rw [zeroRow]
       apply Vector.ext
       intro i bound
       rw [Vector.getElem_map]
       interval_cases i <;> norm_num)
    | decide

-- Nonzero table rows: complementary bytes, the sign boundary, maximum shift
-- truncation and signed high-byte contribution. These are table tests, not ISA claims.
example (operation : Fin 3) :
    Verification.shiftBinopRow ⟨([257, 65793, 131329].get operation) + 90 * 256 + 165,
      by fin_cases operation <;> decide⟩ =
      #v[90, 165, if operation = 2 then 0 else 255, 0, 0, 0, 0, 0, 0,
        [4, 6, 7].get operation] := by
  fin_cases operation <;> decide

example : Verification.shiftBinopRow ⟨128, by decide⟩ =
    #v[127, 0, 0, 0, 0, 0, 0, 0, 0, 3] := by decide

example : Verification.shiftBinopRow ⟨129, by decide⟩ =
    #v[128, 255, 0, 0, 0, 0, 0, 0, 0, 3] := by decide

example : Verification.shiftBinopRow ⟨262400, by decide⟩ =
    #v[255, 255, 31, 0, 0, 0, 0, 0, 0, 8] := by decide

example : Verification.shiftBinopRow ⟨492028, by decide⟩ =
    #v[3, 128, 31, 3, 255, 255, 255, 255, 0, 9] := by decide

example : (⟨0, 1⟩ : Arithmetic.Word).toBitVec =
    (⟨65532, 0⟩ : Arithmetic.Word).toBitVec + 4 := by
  exact (Airbender.ShiftBinop.pc_successor (initial := ⟨65532, 0⟩) (final := ⟨0, 1⟩)
    (by decide) (by decide) satisfies ⟨rfl, rfl, by decide, by decide⟩
    ⟨by decide, by decide⟩).2.2

-- The range lookup rejects a noncanonical low limb that the field-valued
-- PC equations alone would admit (carry zero and final low limb 65536).
example : ¬ FlatOperation.ConstraintsHoldFlat (Verification.environment (row true))
    Airbender.ShiftBinop.importedConstraints := by
  intro h
  have bound := (Airbender.ShiftBinop.local_ranges h).1
  have impossible : ¬ (row true 13).val < Arithmetic.limbBase := by decide
  exact impossible bound

end Tests.ShiftBinop
