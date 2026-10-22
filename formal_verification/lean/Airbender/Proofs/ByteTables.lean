import Airbender.Review.Helpers.Core.FieldCapacity
import Airbender.Proofs.Tables.ShiftCharacterization
import Airbender.Review.Helpers.Tables.Bytes

namespace Airbender.Verification

-- Mathematical helpers for the modeled tagged table; no replacement ISA spec.
def byteOperation {n : Nat} (tag : Nat) (a b : BitVec n) : BitVec n :=
  if tag = 4 then a ^^^ b else if tag = 6 then a ||| b else a &&& b

/-- Read a native Clean membership witness with a canonical, selected table tag. -/
theorem tagged_lookup_row {p : Nat} [Fact p.Prime] (hp : FieldCapacity.NoWrap p 256)
    {entry : Vector (Expression (ZMod p)) 10} {env : Environment (ZMod p)}
    (h : (shiftBinopLookup entry).Contains env) (tag : Nat) (small : tag < 256)
    (selected : entry[9].eval env = (tag : ZMod p)) :
    ∃ i : Fin 524545, (shiftBinopRow i)[9] = tag ∧
      ∀ j : Nat, ∀ hj : j < 10, entry[j].eval env = ((shiftBinopRow i)[j] : ZMod p) := by
  have hs := (shiftBinopLookup entry).table.imply_soundness _ _ h
  change ∃ i : Fin 524545, entry.map (Expression.eval env) =
    (shiftBinopRow i).map (fun (n : Nat) => (n : ZMod p)) at hs
  obtain ⟨i, rows⟩ := hs
  have column (j : Nat) (hj : j < 10) :
      entry[j].eval env = ((shiftBinopRow i)[j] : ZMod p) := by
    have eq := congrArg (fun (v : Vector (ZMod p) 10) => v[j]) rows
    simpa only [Vector.getElem_map] using eq
  have tagBound : (shiftBinopRow i)[9] < p := by
    simp only [shiftBinopRow_eq_reference]
    unfold referenceShiftBinopRow referenceShiftNatRow
    dsimp only
    split_ifs <;> simp [binaryByteRow] <;> omega
  refine ⟨i, ?_, column⟩
  have eq := (column 9 (by decide)).symm.trans selected
  have value := congrArg ZMod.val eq
  simpa [ZMod.val_natCast, Nat.mod_eq_of_lt tagBound,
    Nat.mod_eq_of_lt (show tag < p by omega)] using value

private theorem binary_pair (tag index : Nat) (ht : tag = 4 ∨ tag = 6 ∨ tag = 7) :
    (binaryByteRow tag index)[0] < 256 ∧ (binaryByteRow tag index)[1] < 256 ∧
      (binaryByteRow tag index)[2] = (byteOperation tag
        (BitVec.ofNat 8 (binaryByteRow tag index)[0])
        (BitVec.ofNat 8 (binaryByteRow tag index)[1])).toNat := by
  let pair := ByteUtils.splitTwoBytes ⟨index % 65536, Nat.mod_lt _ (by decide)⟩
  have a := pair.1.isLt
  have b := pair.2.isLt
  rcases ht with rfl | rfl | rfl
  all_goals
    simp [binaryByteRow, byteOperation, ← show pair = ByteUtils.splitTwoBytes
      ⟨index % 65536, Nat.mod_lt _ (by decide)⟩ from rfl,
      show 256 = 2 ^ 8 by decide, a, b]

theorem binary_row_shape (index : Fin 524545) (tag : Nat)
    (valid : tag = 4 ∨ tag = 6 ∨ tag = 7)
    (selected : (shiftBinopRow index)[9] = tag) :
    ∃ key, shiftBinopRow index = binaryByteRow tag key := by
  simp only [shiftBinopRow_eq_reference] at selected ⊢
  unfold referenceShiftBinopRow referenceShiftNatRow at selected ⊢
  dsimp only at selected ⊢
  split_ifs at selected ⊢ <;> try dsimp only at selected ⊢
  all_goals simp [binaryByteRow] at selected
  all_goals solve
    | (rcases valid with rfl | rfl | rfl <;> omega)
    | (change 4 = tag at selected; subst tag; exact ⟨_, rfl⟩)
    | (change 6 = tag at selected; subst tag; exact ⟨_, rfl⟩)
    | (change 7 = tag at selected; subst tag; exact ⟨_, rfl⟩)

private theorem binary_rows (index : Fin 524545) (tag : Nat)
    (ht : tag = 4 ∨ tag = 6 ∨ tag = 7)
    (selected : (shiftBinopRow index)[9] = tag) :
    (shiftBinopRow index)[0] < 256 ∧ (shiftBinopRow index)[1] < 256 ∧
      (shiftBinopRow index)[2] =
        (byteOperation tag (BitVec.ofNat 8 (shiftBinopRow index)[0])
          (BitVec.ofNat 8 (shiftBinopRow index)[1])).toNat := by
  obtain ⟨key, shape⟩ := binary_row_shape index tag ht selected
  rw [shape]
  exact binary_pair tag key ht

/-- A selected binary tag in the native Clean table forces two bytes and their
    exact bitwise result. Other tagged regions cannot satisfy this query. -/
theorem binary_lookup {p : Nat} [Fact p.Prime] (hp : FieldCapacity.NoWrap p 256)
    {entry : Vector (Expression (ZMod p)) 10} {env : Environment (ZMod p)}
    (h : (shiftBinopLookup entry).Contains env) (tag : Nat)
    (ht : tag = 4 ∨ tag = 6 ∨ tag = 7)
    (selected : (entry[9].eval env) = (tag : ZMod p)) :
    (entry[0].eval env).val < 256 ∧ (entry[1].eval env).val < 256 ∧
      (entry[2].eval env).val < 256 ∧
      BitVec.ofNat 8 (entry[2].eval env).val = byteOperation tag
        (BitVec.ofNat 8 (entry[0].eval env).val) (BitVec.ofNat 8 (entry[1].eval env).val) := by
  obtain ⟨i, tagged, column⟩ := tagged_lookup_row hp h tag
    (by rcases ht with rfl | rfl | rfl <;> decide) selected
  obtain ⟨a, b, c⟩ := binary_rows i tag ht tagged
  have cb : (shiftBinopRow i)[2] < 256 := by
    rw [c]
    exact (byteOperation tag _ _).isLt
  have values (j : Nat) (hj : j < 10) (bound : (shiftBinopRow i)[j] < 256) :
      (entry[j].eval env).val = (shiftBinopRow i)[j] := by
    rw [column j hj, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
  rw [values 0 (by decide) a, values 1 (by decide) b, values 2 (by decide) cb]
  refine ⟨a, b, cb, ?_⟩
  simp only [c, BitVec.ofNat_toNat, BitVec.setWidth_eq]

end Airbender.Verification
