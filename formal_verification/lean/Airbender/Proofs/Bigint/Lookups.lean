import Airbender.Review.Helpers.Core.FieldCapacity
import Airbender.Proofs.Bigint.ImportedSetup
import Airbender.Proofs.Bigint.ArtifactChecks
import Airbender.Review.Circuits.Bigint.Tables.Setup
import Airbender.Review.Circuits.Bigint.Artifact
import Airbender.Proofs.Lookups
import Airbender.Proofs.Constraints
import Airbender.Proofs.Arithmetic.Lemmas
import Airbender.Review.Helpers.Properties

namespace Airbender.Bigint.Proofs
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

private theorem low_byte_rows (index : Fin 1390592) (selected : (setupRow index).2.2 = 41) :
    (setupRow index).1 < 65536 ∧ (setupRow index).2.1 = (setupRow index).1 % 256 := by
  have size := index.isLt
  rw [setup_row_characterization] at selected ⊢
  split_ifs at selected ⊢ <;> simp at selected ⊢
  omega

/-- Decode a native membership witness into its natural setup row. -/
theorem fixed_row_values {p tag : Nat} [Fact p.Prime] (hp : FieldCapacity.AtLeast p 65536) (tagBound : tag < p)
    {entry : Vector (Expression (ZMod p)) 3} {env : Environment (ZMod p)}
    (h : (Lookup.mk setupTable.toRaw entry).Contains env)
    (selected : entry[(2 : Nat)].eval env = (tag : ZMod p)) :
    ∃ i : Fin 1390592, entry[0].eval env = ((setupRow i).1 : ZMod p) ∧
      entry[1].eval env = ((setupRow i).2.1 : ZMod p) ∧ (setupRow i).2.2 = tag := by
  change ∃ i : Fin 1390592, entry.map (Expression.eval env) =
    #v[((setupRow i).1 : ZMod p), ((setupRow i).2.1 : ZMod p), ((setupRow i).2.2 : ZMod p)] at h
  obtain ⟨i, row⟩ := h
  have key : entry[0].eval env = ((setupRow i).1 : ZMod p) := by
    have eq := congrArg (fun v : Vector (ZMod p) 3 => v[(0 : Nat)]) row
    simpa only [Vector.getElem_map, Vector.getElem_mk, List.getElem_toArray,
      List.getElem_cons_zero] using eq
  have low : entry[1].eval env = ((setupRow i).2.1 : ZMod p) := by
    have eq := congrArg (fun v : Vector (ZMod p) 3 => v[(1 : Nat)]) row
    simpa only [Vector.getElem_map, Vector.getElem_mk, List.getElem_toArray,
      List.getElem_cons_succ, List.getElem_cons_zero] using eq
  have tagField : entry[2].eval env = ((setupRow i).2.2 : ZMod p) := by
    have eq := congrArg (fun v : Vector (ZMod p) 3 => v[(2 : Nat)]) row
    simpa only [Vector.getElem_map, Vector.getElem_mk, List.getElem_toArray,
      List.getElem_cons_succ, List.getElem_cons_zero] using eq
  have rowTagBound : (setupRow i).2.2 < p := by
    rw [setup_row_characterization]
    split_ifs <;> simp <;> omega
  have tagEq : (setupRow i).2.2 = tag := by
    have eq := congrArg ZMod.val (tagField.symm.trans selected)
    have literal : (tag : ZMod p).val = tag := by
      exact ZMod.val_natCast_of_lt tagBound
    rw [ZMod.val_natCast_of_lt rowTagBound, literal] at eq
    exact eq
  exact ⟨i, key, low, tagEq⟩

/-- Project tag 41 into U16GetLowByte rows and reuse the shared row-value
    theorem for its range and low byte. Clean supplies native membership. -/
theorem low_byte_value {p : Nat} [Fact p.Prime] (hp : FieldCapacity.AtLeast p 65536)
    {entry : Vector (Expression (ZMod p)) 3} {env : Environment (ZMod p)}
    (h : (Lookup.mk setupTable.toRaw entry).Contains env)
    (selected : entry[(2 : Nat)].eval env = 41) :
    (entry[(0 : Nat)].eval env).val < 65536 ∧
      entry[(1 : Nat)].eval env = (((entry[(0 : Nat)].eval env).val % 256 : Nat) : ZMod p) := by
  obtain ⟨i, key, low, tag⟩ := fixed_row_values hp (tag := 41) (by omega) h selected
  obtain ⟨keyBound, lowValue⟩ := low_byte_rows i tag
  apply Verification.pair_value_of_row (value := fun n => n % 256) hp
  refine ⟨⟨(setupRow i).1, keyBound⟩, Prod.ext key ?_⟩
  simpa only [lowValue] using low

theorem source_ranges {p : Nat} [Fact p.Prime] (hp : FieldCapacity.AtLeast p 65536) {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints setupTable)) :
    ∀ i : Fin 16, (w Variables.leftLimbs[i]).val < Arithmetic.limbBase ∧
      (w Variables.rightLimbs[i]).val < Arithmetic.limbBase := by
  intro i
  have left := Verification.lookup_of_holds h ⟨34 + i.val,
    by rw [lookup_count]; have := i.isLt; omega⟩
  have right := Verification.lookup_of_holds h ⟨50 + i.val,
    by rw [lookup_count]; have := i.isLt; omega⟩
  fin_cases i
  all_goals have leftPair := low_byte_value hp left (by
    simp [Expression.eval, Verification.environment])
  all_goals have rightPair := low_byte_value hp right (by
    simp [Expression.eval, Verification.environment])
  all_goals have leftRange := leftPair.1
  all_goals have rightRange := rightPair.1
  all_goals constructor
  all_goals first
    | simpa [importedConstraints, FlatOperation.lookups, Expression.eval,
        Verification.environment, Variables.leftLimbs, Arithmetic.limbBase] using leftRange
    | simpa [importedConstraints, FlatOperation.lookups, Expression.eval,
        Verification.environment, Variables.rightLimbs, Arithmetic.limbBase] using rightRange

end Airbender.Bigint.Proofs
