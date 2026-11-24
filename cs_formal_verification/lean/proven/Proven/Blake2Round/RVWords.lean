module
public import Human.Trace.Workers.Blake2Round.RVCompression
public import Proven.Delegation.RVNativeViews

@[expose] public section

/-! RV RAM blocks: aligned words read their encodings (`rv_block_at`), the encodings are the spec's `RV.readWords`
    (`rv_block_words`), and `RV.Same` states read the same blocks (`rv_words_at_same`). RAM at any address, the
    shadow RAM below `ROM_END` included. -/

namespace Airbender.Blake2Round.Proofs
open Trace Trace.Proofs Delegation.Proofs Arithmetic
set_option warningAsError true

/-- RV `block_at`: aligned RAM words read their encodings. -/
theorem rv_block_at {state : RV.State} {pointer : BitVec 32} {n offset : Nat}
    (pointerAligned : pointer.toNat % 4 = 0) :
    Blake2Round.Compression.RVWordsAt state pointer offset (rvBlockWords state pointer n offset) := by
  intro i
  simp only [rvBlockWords, Fin.getElem_fin, Vector.getElem_ofFn]
  refine ⟨Word.ofBitVec_bound _, rv_encoded_read ?_⟩
  change (pointer + BitVec.ofNat 32 (4 * (offset + i.val))).toNat % 4 = 0
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem rv_block_words {state : RV.State} {pointer : BitVec 32} {n : Nat} :
    (rvBlockWords state pointer n 0).map Word.toBitVec = RV.readWords state.mem pointer n := by
  apply Vector.ext
  intro i bound
  simp only [rvBlockWords, rvRamEncoding, RV.readWords, Vector.getElem_map, Vector.getElem_ofFn,
    Word.ofBitVec_roundtrip, Nat.zero_add]

theorem rv_block_words_offset {state : RV.State} {pointer : BitVec 32} {n offset : Nat} :
    (rvBlockWords state pointer n offset).map Word.toBitVec =
      RV.readWords state.mem (pointer + BitVec.ofNat 32 (4 * offset)) n := by
  apply Vector.ext
  intro i bound
  simp only [rvBlockWords, rvRamEncoding, RV.readWords, Vector.getElem_map, Vector.getElem_ofFn,
    Word.ofBitVec_roundtrip]
  congr 1
  rw [BitVec.add_assoc]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

/-- Transport an RV block read along `RV.Same`. -/
theorem rv_words_at_same {n : Nat} {left right : RV.State} (same : RV.Same left right) {pointer : BitVec 32}
    {offset : Nat} {words : Vector Word n}
    (reads : Blake2Round.Compression.RVWordsAt left pointer offset words) :
    Blake2Round.Compression.RVWordsAt right pointer offset words := by
  intro i
  exact ⟨(reads i).1, (readRV_congr_same same).symm.trans (reads i).2⟩

end Airbender.Blake2Round.Proofs
