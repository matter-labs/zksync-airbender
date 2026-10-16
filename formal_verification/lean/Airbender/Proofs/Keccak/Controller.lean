import Airbender.Proofs.Keccak.Tables
import Airbender.Proofs.Keccak.Controls

namespace Airbender.Keccak.Proofs
open Arithmetic
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 1200000

private theorem row_tag (tag index : Nat) : (byteRow tag index)[7] = tag := rfl
private theorem rotation_tag (key : Nat) : (rotationRow key)[7] = 40 := rfl

private theorem controller_region {control : Fin 4096 → Vector Nat 6}
    (index : Fin 1249281) (selected : (referenceSetupRow control index)[7] = 37) :
    ∃ key : Fin 4096, referenceSetupRow control index =
      #v[key.val, (control key)[0], (control key)[1], (control key)[2],
        (control key)[3], (control key)[4], (control key)[5], 37] := by
  have bound := index.isLt
  unfold referenceSetupRow at selected ⊢
  dsimp only at selected ⊢
  split_ifs at selected ⊢
  all_goals simp only [row_tag, rotation_tag, Vector.getElem_replicate,
    Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_succ,
    List.getElem_cons_zero] at selected
  all_goals norm_num at selected
  exact ⟨⟨index.val - 65537, by omega⟩, rfl⟩

/-- Native membership selects one supplied controller row. No schedule, honest
    witness generation or desired lane indices are premises. -/
theorem controller_lookup {p : Nat} [Fact p.Prime] (hp : 4096 ≤ p)
    {control : Fin 4096 → Vector Nat 6} {entry : Vector (Expression (ZMod p)) 8}
    {env : Environment (ZMod p)}
    (h : (Lookup.mk (setupTable control).toRaw entry).Contains env)
    (selected : entry[7].eval env = 37) :
    ∃ key : Fin 4096, entry[0].eval env = (key.val : ZMod p) ∧
      ∀ j : Fin 6, entry[j.val + 1].eval env = ((control key)[j] : ZMod p) := by
  have member := (Lookup.mk (setupTable control).toRaw entry).table.imply_soundness _ _ h
  change ∃ index : Fin 1249281, entry.map (Expression.eval env) =
    (setupRow control index).map (fun (n : Nat) => (n : ZMod p)) at member
  simp only [setup_row_characterization] at member
  obtain ⟨index, row⟩ := member
  have column (j : Nat) (hj : j < 8) : entry[j].eval env =
      ((referenceSetupRow control index)[j] : ZMod p) := by
    have equation := congrArg (fun (v : Vector (ZMod p) 8) => v[j]) row
    simpa only [Vector.getElem_map] using equation
  have tagBound : (referenceSetupRow control index)[7] < p := by
    unfold referenceSetupRow
    dsimp only
    split_ifs <;> simp only [row_tag, rotation_tag, Vector.getElem_replicate,
      Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_succ,
      List.getElem_cons_zero] <;> omega
  have tag : (referenceSetupRow control index)[7] = 37 := by
    have equation := congrArg ZMod.val ((column 7 (by decide)).symm.trans selected)
    rw [ZMod.val_natCast_of_lt tagBound] at equation
    have literal : (37 : ZMod p).val = 37 := by
      simpa only [Nat.cast_ofNat] using ZMod.val_natCast_of_lt (n := p) (a := 37) (by omega)
    rwa [literal] at equation
  obtain ⟨key, physicalRow⟩ := controller_region index tag
  refine ⟨key, ?_, ?_⟩
  · simpa [physicalRow] using column 0 (by decide)
  · intro j
    have equation := column (j.val + 1) (by omega)
    fin_cases j <;> simpa [physicalRow] using equation

/-- The exact packed input and six offset columns come from the controller
    query in the original artifact. Setup correspondence with Rust is separate. -/
theorem controller_columns {p : Nat} [Fact p.Prime] (hp : 4096 ≤ p)
    {control : Fin 4096 → Vector Nat 6} {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints (setupTable control))) :
    ∃ key : Fin 4096, w 3 + 2048 * w 0 = (key.val : ZMod p) ∧
      ∀ i : Fin 6, w (7 + i.val) = ((control key)[i] : ZMod p) := by
  have member := Verification.lookup_of_holds h ⟨1, by rw [lookup_count]; decide⟩
  obtain ⟨key, input, outputs⟩ := controller_lookup hp member
    (by simp [Expression.eval, Verification.environment])
  refine ⟨key, ?_, ?_⟩
  · simpa [importedConstraints, FlatOperation.lookups, Expression.eval,
      Verification.environment, add_comm, mul_comm] using input
  · intro i
    have equation := outputs i
    fin_cases i <;> simpa [importedConstraints, FlatOperation.lookups,
      Expression.eval, Verification.environment] using equation

/-- Row-domain bounds supply the setup's range guarantees; they are not an
    assumption on the witness's six indices. The packed key is also decoded. -/
theorem controller_indices {p : Nat} [Fact p.Prime] (hp : 4096 ≤ p)
    {control : Fin 4096 → Vector Nat 6} {w : Nat → ZMod p}
    (rowsBounded : ∀ key : Fin 4096, ∀ i : Fin 6, (control key)[i] < 31)
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints (setupTable control))) :
    ∃ key : Fin 4096, key.val = (w 3).val + 2048 * (w 0).val ∧
      ∀ i : Fin 6, (w (7 + i.val)).val = (control key)[i] := by
  obtain ⟨key, input, outputs⟩ := controller_columns hp h
  have low := control_read_bound (by omega) h
  have active := boolean_val (control_bits h).1
  have small : (w 3).val + 2048 * (w 0).val < p := by omega
  have encoded : (((w 3).val + 2048 * (w 0).val : Nat) : ZMod p) = (key.val : ZMod p) := by
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, ZMod.natCast_zmod_val] using input
  have natural := congrArg ZMod.val encoded
  rw [ZMod.val_natCast_of_lt small, ZMod.val_natCast_of_lt (by have := key.isLt; omega)] at natural
  refine ⟨key, natural.symm, ?_⟩
  intro i
  rw [outputs i]
  exact ZMod.val_natCast_of_lt (by have := rowsBounded key i; omega)

end Airbender.Keccak.Proofs
