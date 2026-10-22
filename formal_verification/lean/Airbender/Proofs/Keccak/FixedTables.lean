import Airbender.Review.Helpers.Core.FieldCapacity
import Airbender.Proofs.Keccak.Tables

namespace Airbender.Keccak.Proofs
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 1200000

private theorem byte_tag (tag index : Nat) : (byteRow tag index)[7] = tag := rfl
private theorem rotation_tag (key : Nat) : (rotationRow key)[7] = 40 := rfl

private theorem byte_facts (tag index : Nat) (size : index < 65536)
    (known : tag = 4 ∨ tag = 38 ∨ tag = 39) :
    ByteOperationFacts tag (byteRow tag index)[0] (byteRow tag index)[1]
      (byteRow tag index)[2] := by
  have a : index % 256 < 256 := Nat.mod_lt _ (by decide)
  have b : index / 256 < 256 := by omega
  have constant : iotaByte (index / 256) < 256 := Nat.mod_lt _ (by decide)
  rcases known with rfl | rfl | rfl
  · change index / 256 < 256 ∧ index % 256 < 256 ∧
      index / 256 ^^^ index % 256 < 256 ∧ _
    exact ⟨b, a, Nat.xor_lt_two_pow (n := 8) b a, rfl⟩
  · change index % 256 < 256 ∧ index / 256 < 256 ∧
      index % 256 ^^^ iotaByte (index / 256) < 256 ∧ _
    exact ⟨a, b, Nat.xor_lt_two_pow (n := 8) a constant, rfl⟩
  · change index % 256 < 256 ∧ index / 256 < 256 ∧
      (index % 256 ^^^ 255) &&& (index / 256) < 256 ∧ _
    exact ⟨a, b, lt_of_le_of_lt Nat.and_le_right b, rfl⟩

private theorem rotation_facts (key : Nat) (size : key < 1048576) :
    ByteOperationFacts 40 (rotationRow key)[0] (rotationRow key)[1]
      (rotationRow key)[2] := by
  have word : key % 65536 < 65536 := Nat.mod_lt _ (by decide)
  have quotient := Nat.div_le_self (key % 65536) (2 ^ (16 - key / 65536))
  change key < 1048576 ∧ (key % 65536) / 2 ^ (16 - key / 65536) < 65536 ∧
    ((key % 65536) * 2 ^ (key / 65536)) % 65536 < 65536 ∧ _
  exact ⟨size, by omega, Nat.mod_lt _ (by decide), rfl, rfl⟩

private theorem fixed_rows {control : Fin 4096 → Vector Nat 6}
    (index : Fin 1249281) (notController : (referenceSetupRow control index)[7] ≠ 37) :
    ByteOperationFacts (referenceSetupRow control index)[7] (referenceSetupRow control index)[0]
      (referenceSetupRow control index)[1] (referenceSetupRow control index)[2] := by
  have size := index.isLt
  unfold referenceSetupRow at notController ⊢
  dsimp only at notController ⊢
  split_ifs at notController ⊢
  · simp [ByteOperationFacts]
  · exact byte_facts 4 _ (by omega) (Or.inl rfl)
  · simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_succ,
      List.getElem_cons_zero] at notController
    exact (notController rfl).elim
  · exact byte_facts 38 _ (by omega) (Or.inr (Or.inl rfl))
  · exact byte_facts 39 _ (by omega) (Or.inr (Or.inr rfl))
  · exact rotation_facts _ (by omega)

/-- All non-controller regions have bounded, exact outputs. This includes the
    actual round constants from Clean and both pieces of every rotation query. -/
theorem fixed_lookup {p : Nat} [Fact p.Prime] (hp : FieldCapacity.AtLeast p 1048576)
    {control : Fin 4096 → Vector Nat 6} {entry : Vector (Expression (ZMod p)) 8}
    {env : Environment (ZMod p)}
    (h : (Lookup.mk (setupTable control).toRaw entry).Contains env)
    (notController : (entry[7].eval env).val ≠ 37) :
    ByteOperationFacts (entry[7].eval env).val (entry[0].eval env).val
      (entry[1].eval env).val (entry[2].eval env).val := by
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
    split_ifs <;> simp only [byte_tag, rotation_tag, Vector.getElem_replicate,
      Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_succ,
      List.getElem_cons_zero] <;> omega
  have tagged : (entry[7].eval env).val = (referenceSetupRow control index)[7] := by
    rw [column 7 (by decide), ZMod.val_natCast_of_lt tagBound]
  have facts := fixed_rows index (by rwa [← tagged])
  have bounded : (referenceSetupRow control index)[0] < 1048576 ∧
      (referenceSetupRow control index)[1] < 1048576 ∧ (referenceSetupRow control index)[2] < 1048576 := by
    unfold ByteOperationFacts at facts
    split_ifs at facts <;> omega
  have value (j : Nat) (hj : j < 8) (bound : (referenceSetupRow control index)[j] < 1048576) :
      (entry[j].eval env).val = (referenceSetupRow control index)[j] := by
    rw [column j hj]
    exact ZMod.val_natCast_of_lt (by omega)
  rw [tagged, value 0 (by decide) bounded.1, value 1 (by decide) bounded.2.1,
    value 2 (by decide) bounded.2.2]
  exact facts

end Airbender.Keccak.Proofs
