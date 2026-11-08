module
public import Slop.Blake2G.StateCells

@[expose] public section

namespace Airbender.Blake2G.Proofs
open Trace Trace.Proofs Delegation.Proofs Arithmetic
set_option warningAsError true

theorem block_word_injective (pointer : BitVec 32) (a b : Fin 16)
    (same : pointer + BitVec.ofNat 32 (4 * a.val) =
      pointer + BitVec.ofNat 32 (4 * b.val)) : a = b := by
  have bits := (BitVec.add_right_inj pointer).mp same
  have values := congrArg BitVec.toNat bits
  have ab := a.isLt
  have bb := b.isLt
  simp only [BitVec.toNat_ofNat] at values
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at values
  exact Fin.ext (by omega)

theorem aligned_block_words_distinct (state message : BitVec 32)
    (stateAligned : state.toNat % 64 = 0) (messageAligned : message.toNat % 64 = 0)
    (distinct : state ≠ message) (a b : Fin 16) :
    state + BitVec.ofNat 32 (4 * a.val) ≠ message + BitVec.ofNat 32 (4 * b.val) := by
  intro same
  have offset (pointer : BitVec 32) (aligned : pointer.toNat % 64 = 0) (index : Fin 16) :
      (pointer + BitVec.ofNat 32 (4 * index.val)).toNat % 64 = 4 * index.val := by
    have bound := index.isLt
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    rw [Nat.mod_mod_of_dvd _ (by decide : 64 ∣ 2 ^ 32)]
    rw [Nat.add_mod, aligned, Nat.mod_mod_of_dvd _ (by decide : 64 ∣ 2 ^ 32),
      Nat.mod_eq_of_lt (by omega), Nat.zero_add,
      Nat.mod_eq_of_lt (by omega)]
  have residue := congrArg (fun value : BitVec 32 => value.toNat % 64) same
  rw [offset state stateAligned a, offset message messageAligned b] at residue
  have index : a = b := Fin.ext (by omega)
  subst b
  exact distinct ((BitVec.add_left_inj (BitVec.ofNat 32 (4 * a.val))).mp same)

end Airbender.Blake2G.Proofs
