import Airbender.Proofs.Keccak.SplitChiCallControl
import Airbender.Proofs.Arithmetic.Word

namespace Airbender.Keccak.Split.Native.Proofs
open Arithmetic Trace Trace.Proofs Reference.RiscV.Sail Reference.Sail
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 1600000
variable [Fact babyBearModulus.Prime]

/-- The exact pointer token preserves both raw native value limbs. -/
theorem chi5_pointer_word (cached : Bool) (w : Nat → ZMod babyBearModulus) :
    (readToken w (chi5PointerPort cached)).word =
      Word.mk (chi5Pointer cached w)[0].val (chi5Pointer cached w)[1].val := by
  change Word.mk (Nat.unpair ((chi5PointerPort cached).readCode w)).1
    (Nat.unpair ((chi5PointerPort cached).readCode w)).2 = _
  rw [(chi5_pointer_port cached w).2.1, Nat.unpair_pair]

/-- Initialized native pointer words recover the supported reference pointer exactly. -/
theorem chi5_call_pointer_binding (cached : Bool) (w : Nat → ZMod babyBearModulus)
    (index : Fin 361) (before : State) (arguments : ArgumentsAt index.val before)
    (bounded : (readToken w (chi5PointerPort cached)).word.Bounded)
    (observed : ∃ cell : Cell, cell.addressCode = (chi5PointerPort cached).address.code w ∧
      cell.read before = .ok (readToken w (chi5PointerPort cached)).word.toBitVec before) :
    ∃ pointer : BitVec 32, (Cell.register 11).read before = .ok pointer before ∧
      ROM.limit ≤ pointer.toNat ∧ pointer.toNat % 256 = 0 ∧
      (readToken w (chi5PointerPort cached)).word = Word.ofBitVec pointer := by
  obtain ⟨_, pointer, _, pointerRead, _, ram, aligned⟩ := arguments
  obtain ⟨cell, code, read⟩ := observed
  have address : (chi5PointerPort cached).address.code w = (Cell.register 11).addressCode := by
    cases cached <;> rfl
  have sameCell := cell_address_injective (code.trans address)
  rw [sameCell] at read
  have bits := (EStateM.Result.ok.inj (read.symm.trans pointerRead)).1
  refine ⟨pointer, pointerRead, ram, aligned, ?_⟩
  apply Word.eq_of_value bounded (Word.ofBitVec_bound pointer)
  rw [← Word.toBitVec_toNat bounded, bits, Word.ofBitVec_value]

omit [Fact babyBearModulus.Prime] in
/-- A supported aligned pointer leaves room for every sixty-four-bit state lane. -/
theorem chi5_pointer_lane_room (pointer : BitVec 32) (aligned : pointer.toNat % 256 = 0)
    (slot : Fin 25) (high : Bool) :
    pointer.toNat % 65536 + 8 * slot.val + (if high then 4 else 0) < 65536 ∧
      pointer.toNat + 8 * slot.val + (if high then 4 else 0) < 2 ^ 32 := by
  have small := pointer.isLt
  have slots := slot.isLt
  cases high <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega

end Airbender.Keccak.Split.Native.Proofs
