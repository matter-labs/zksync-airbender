module
public import Human.ISA.Blake2s
public import Slop.CleanCore.Utils.Rotation

@[expose] public section

/-! A Blake2s round (`Spec.round`, Clean's round on natural-number words) is its eight `G`s (`Spec.G`, Clean's `g`)
one after another (`round_G`): Clean's `g` keeps words below `2^32`, so going back to `Word` between two `G`s loses
nothing. -/

namespace Spec
open RV (Word)
open Airbender.Specs.BLAKE3 (g)

/-- Clean's `rotRight32_lt` (not transcribed in CleanCore): a rotation of a 32-bit word stays below `2^32`. -/
theorem rotRight32_lt (x r : Nat) (h : x < 2 ^ 32) : Airbender.rotRight32 x r < 2 ^ 32 := by
  have split : 2 ^ 32 = 2 ^ (r % 32) * 2 ^ (32 - r % 32) := by
    rw [← pow_add]; congr 1; have := Nat.mod_lt r (show 32 > 0 by decide); omega
  have low : x % 2 ^ (r % 32) < 2 ^ (r % 32) := Nat.mod_lt _ (by positivity)
  have high : x / 2 ^ (r % 32) < 2 ^ (32 - r % 32) := by
    rw [Nat.div_lt_iff_lt_mul (by positivity), mul_comm, ← split]; exact h
  simp only [Airbender.rotRight32]
  calc x % 2 ^ (r % 32) * 2 ^ (32 - r % 32) + x / 2 ^ (r % 32)
      < (x % 2 ^ (r % 32) + 1) * 2 ^ (32 - r % 32) := by
        rw [Nat.succ_mul]; exact Nat.add_lt_add_left high _
    _ ≤ 2 ^ (r % 32) * 2 ^ (32 - r % 32) := Nat.mul_le_mul_right _ low
    _ = 2 ^ 32 := split.symm

theorem g_lt (w : Vector Nat 16) (h : ∀ i (hi : i < 16), w[i] < 2 ^ 32) (a b c d : Fin 16) (x y : Nat) :
    ∀ i (hi : i < 16), (Airbender.Specs.BLAKE3.g w a b c d x y)[i] < 2 ^ 32 := by
  have ha : ∀ u v, Airbender.add32 u v < 2 ^ 32 := fun u v => Nat.mod_lt _ (by decide)
  have hr : ∀ u v, u < 2 ^ 32 → v < 2 ^ 32 → ∀ o, Airbender.rotRight32 (u ^^^ v) o < 2 ^ 32 :=
    fun u v hu hv o => rotRight32_lt _ _ (Nat.xor_lt_two_pow hu hv)
  intro i hi
  simp only [Airbender.Specs.BLAKE3.g, Vector.getElem_set, Fin.getElem_fin]
  split_ifs
  all_goals repeat (first | exact ha _ _ | apply hr | exact h _ _)

theorem map_toNat_ofNat (w : Vector Nat 16) (h : ∀ i (hi : i < 16), w[i] < 2 ^ 32) :
    (w.map (BitVec.ofNat 32)).map BitVec.toNat = w := by
  apply Vector.ext; intro i hi
  simp only [Vector.getElem_map, BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt (h i hi)

theorem toNat_lt (v : Vector Word 16) : ∀ i (hi : i < 16), (v.map BitVec.toNat)[i] < 2 ^ 32 := by
  intro i hi; simp only [Vector.getElem_map]; exact BitVec.isLt _

/-- `G` on Clean's words: `G` of a word vector is Clean's `g` of its words. -/
theorem G_map (v : Vector Nat 16) (h : ∀ i (hi : i < 16), v[i] < 2 ^ 32) (a b c d : Fin 16) (x y : Word) :
    G (v.map (BitVec.ofNat 32)) a b c d x y = (Airbender.Specs.BLAKE3.g v a b c d x.toNat y.toNat).map (BitVec.ofNat 32) := by
  rw [G, map_toNat_ofNat v h]

theorem clean_round (N M : Vector Nat 16) :
    Airbender.Specs.BLAKE3.round N M =
      g (g (g (g (g (g (g (g N 0 4 8 12 M[0] M[1]) 1 5 9 13 M[2] M[3]) 2 6 10 14 M[4] M[5]) 3 7 11 15 M[6] M[7])
        0 5 10 15 M[8] M[9]) 1 6 11 12 M[10] M[11]) 2 7 8 13 M[12] M[13]) 3 4 9 14 M[14] M[15] := by rfl

/-- A round is its eight `G`s: the four columns, then the four diagonals. -/
theorem round_G (m : Vector Word 16) (s : Fin 16 → Fin 16) (v : Vector Word 16) :
    round m s v =
      let v := G v 0 4 8 12 m[s 0] m[s 1]
      let v := G v 1 5 9 13 m[s 2] m[s 3]
      let v := G v 2 6 10 14 m[s 4] m[s 5]
      let v := G v 3 7 11 15 m[s 6] m[s 7]
      let v := G v 0 5 10 15 m[s 8] m[s 9]
      let v := G v 1 6 11 12 m[s 10] m[s 11]
      let v := G v 2 7 8 13 m[s 12] m[s 13]
      G v 3 4 9 14 m[s 14] m[s 15] := by
  obtain ⟨N, hN, rfl⟩ : ∃ N : Vector Nat 16, (∀ i (hi : i < 16), N[i] < 2 ^ 32) ∧ v = N.map (BitVec.ofNat 32) :=
    ⟨v.map BitVec.toNat, toNat_lt v, by apply Vector.ext; intro i hi; simp⟩
  simp (disch := repeat (first | apply g_lt | assumption)) only [G_map]
  unfold round
  rw [map_toNat_ofNat N hN, clean_round]
  simp only [Vector.getElem_ofFn, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk]

end Spec
