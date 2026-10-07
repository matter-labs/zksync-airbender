import Airbender.Review.ByteTables

namespace Airbender.Verification

-- Mathematical helpers for the modeled tagged table; no replacement ISA spec.
def byteOperation {n : Nat} (tag : Nat) (a b : BitVec n) : BitVec n :=
  if tag = 4 then a ^^^ b else if tag = 6 then a ||| b else a &&& b

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

private theorem binary_rows (index : Fin 524545) (tag : Nat)
    (ht : tag = 4 ∨ tag = 6 ∨ tag = 7)
    (selected : (shiftBinopRow index)[9] = tag) :
    (shiftBinopRow index)[0] < 256 ∧ (shiftBinopRow index)[1] < 256 ∧
      (shiftBinopRow index)[2] =
        (byteOperation tag (BitVec.ofNat 8 (shiftBinopRow index)[0])
          (BitVec.ofNat 8 (shiftBinopRow index)[1])).toNat := by
  unfold shiftBinopRow at selected ⊢
  dsimp only at selected ⊢
  split_ifs at selected ⊢ <;> try dsimp only at selected ⊢
  all_goals simp [binaryByteRow] at selected
  all_goals solve
    | (rcases ht with rfl | rfl | rfl <;> omega)
    | (change 4 = tag at selected; subst tag; exact binary_pair 4 _ (Or.inl rfl))
    | (change 6 = tag at selected; subst tag; exact binary_pair 6 _ (Or.inr (Or.inl rfl)))
    | (change 7 = tag at selected; subst tag; exact binary_pair 7 _ (Or.inr (Or.inr rfl)))

/-- A selected binary tag in the native Clean table forces two bytes and their
    exact bitwise result. Other tagged regions cannot satisfy this query. -/
theorem binary_lookup {p : Nat} [Fact p.Prime] (hp : 256 < p)
    {entry : Vector (Expression (ZMod p)) 10} {env : Environment (ZMod p)}
    (h : (shiftBinopLookup entry).Contains env) (tag : Nat)
    (ht : tag = 4 ∨ tag = 6 ∨ tag = 7)
    (selected : (entry[9].eval env) = (tag : ZMod p)) :
    (entry[0].eval env).val < 256 ∧ (entry[1].eval env).val < 256 ∧
      (entry[2].eval env).val < 256 ∧
      BitVec.ofNat 8 (entry[2].eval env).val = byteOperation tag
        (BitVec.ofNat 8 (entry[0].eval env).val) (BitVec.ofNat 8 (entry[1].eval env).val) := by
  have hs := (shiftBinopLookup entry).table.imply_soundness _ _ h
  change ∃ i : Fin 524545, entry.map (Expression.eval env) =
    (shiftBinopRow i).map (fun (n : Nat) => (n : ZMod p)) at hs
  obtain ⟨i, rows⟩ := hs
  have column (j : Nat) (hj : j < 10) :
      entry[j].eval env = ((shiftBinopRow i)[j] : ZMod p) := by
    have eq := congrArg (fun (v : Vector (ZMod p) 10) => v[j]) rows
    simpa only [Vector.getElem_map] using eq
  have tagBound : (shiftBinopRow i)[9] < p := by
    unfold shiftBinopRow
    dsimp only
    split_ifs <;> simp [binaryByteRow] <;> omega
  have tagSmall : tag < p := by rcases ht with rfl | rfl | rfl <;> omega
  have tagged : (shiftBinopRow i)[9] = tag := by
    have eq := (column 9 (by decide)).symm.trans selected
    have value := congrArg ZMod.val eq
    simpa [ZMod.val_natCast, Nat.mod_eq_of_lt tagBound, Nat.mod_eq_of_lt tagSmall] using value
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
