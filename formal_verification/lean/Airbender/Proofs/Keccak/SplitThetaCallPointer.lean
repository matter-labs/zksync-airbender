import Airbender.Proofs.Keccak.SplitThetaCallControl
import Airbender.Proofs.Arithmetic.Word

namespace Airbender.Keccak.Split.Native.Proofs
open Arithmetic Trace Trace.Proofs Reference.RiscV.Sail Reference.Sail
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
variable [Fact babyBearModulus.Prime]

/-- The exact pointer token preserves both raw native value limbs. -/
theorem theta_pointer_word (cached : Bool) (w : Nat → ZMod babyBearModulus) :
    (readToken w (thetaPointerPort cached)).word =
      Word.mk (thetaPointer cached w)[0].val (thetaPointer cached w)[1].val := by
  change Word.mk (Nat.unpair ((thetaPointerPort cached).readCode w)).1
    (Nat.unpair ((thetaPointerPort cached).readCode w)).2 = _
  rw [(theta_pointer_port cached w).2.1, Nat.unpair_pair]

/-- Initialized native pointer words recover the supported reference pointer exactly. -/
theorem theta_call_pointer_binding (cached : Bool) (w : Nat → ZMod babyBearModulus)
    (index : Fin 361) (before : State) (arguments : ArgumentsAt index.val before)
    (bounded : (readToken w (thetaPointerPort cached)).word.Bounded)
    (observed : ∃ cell : Cell, cell.addressCode = (thetaPointerPort cached).address.code w ∧
      cell.read before = .ok (readToken w (thetaPointerPort cached)).word.toBitVec before) :
    ∃ pointer : BitVec 32, (Cell.register 11).read before = .ok pointer before ∧
      ROM.limit ≤ pointer.toNat ∧ pointer.toNat % 256 = 0 ∧
      (readToken w (thetaPointerPort cached)).word = Word.ofBitVec pointer := by
  obtain ⟨_, pointer, _, pointerRead, _, ram, aligned⟩ := arguments
  obtain ⟨cell, code, read⟩ := observed
  have address : (thetaPointerPort cached).address.code w = (Cell.register 11).addressCode := by
    cases cached <;> rfl
  have sameCell := cell_address_injective (code.trans address)
  rw [sameCell] at read
  have bits := (EStateM.Result.ok.inj (read.symm.trans pointerRead)).1
  refine ⟨pointer, pointerRead, ram, aligned, ?_⟩
  apply Word.eq_of_value bounded (Word.ofBitVec_bound pointer)
  rw [← Word.toBitVec_toNat bounded, bits, Word.ofBitVec_value]

omit [Fact babyBearModulus.Prime] in
/-- A supported aligned pointer leaves room for every state or scratch lane. -/
theorem theta_pointer_lane_room (pointer : BitVec 32) (aligned : pointer.toNat % 256 = 0)
    (slot : Fin 31) (high : Bool) :
    pointer.toNat % 65536 + 8 * slot.val + (if high then 4 else 0) < 65536 ∧
      pointer.toNat + 8 * slot.val + (if high then 4 else 0) < 2 ^ 32 := by
  have small := pointer.isLt
  have slots := slot.isLt
  cases high <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega

end Airbender.Keccak.Split.Native.Proofs
