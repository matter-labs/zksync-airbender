import Slop.Arithmetic.Bytes

namespace Airbender.Arithmetic
set_option warningAsError true

theorem Word.byte_fields {p : Nat} [Fact p.Prime] (hp : 65536 < p)
    (lo hi : ZMod p) (bytes : Fin 4 → ZMod p)
    (bounded : ∀ i, (bytes i).val < 256)
    (low : bytes ⟨0, by decide⟩ + 256 * bytes ⟨1, by decide⟩ = lo) (high : bytes ⟨2, by decide⟩ + 256 * bytes ⟨3, by decide⟩ = hi) :
    ∀ i : Fin 4, bytes i =
      (((Word.mk lo.val hi.val).toBitVec.extractLsb' (8 * i.val) 8).toNat : ZMod p) := by
  have l := byte_pair_value hp (bytes ⟨0, by decide⟩) (bytes ⟨1, by decide⟩) lo (bounded ⟨0, by decide⟩) (bounded ⟨1, by decide⟩) low
  have h := byte_pair_value hp (bytes ⟨2, by decide⟩) (bytes ⟨3, by decide⟩) hi (bounded ⟨2, by decide⟩) (bounded ⟨3, by decide⟩) high
  have b0 := bounded ⟨0, by decide⟩; have b1 := bounded ⟨1, by decide⟩; have b2 := bounded ⟨2, by decide⟩; have b3 := bounded ⟨3, by decide⟩
  intro i
  calc bytes i = ((bytes i).val : ZMod p) := (ZMod.natCast_zmod_val _).symm
    _ = _ := by
      apply congrArg (fun n : Nat => (n : ZMod p))
      fin_cases i
      all_goals simp only [Word.toBitVec, Word.value, limbBase, BitVec.extractLsb',
        BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
      all_goals norm_num only [Nat.reducePow, Nat.reduceMul, Fin.val_zero, Fin.val_one, Fin.val_ofNat] at *
      all_goals rw [l, h]
      all_goals omega

end Airbender.Arithmetic
