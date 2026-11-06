import Airbender.Proofs.ReducedMachine.NativeShiftWords

namespace Airbender.ReducedMachine.NativeShiftWordProofs
open Native Arithmetic NativeShiftNaturalProofs
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

/-- Left contributions reconstruct the exact native candidate word. -/
theorem left_assembly (lo hi amount : Nat) (low : lo < 65536) (high : hi < 65536) :
    (Word.toBitVec ⟨assembledLow .left lo hi amount,assembledHigh .left lo hi amount⟩) =
      (BitVec.ofNat 32 lo) <<< amount + (BitVec.ofNat 32 (hi * 65536)) <<< amount := by
  rw [← left_low lo amount low,← left_high hi amount high,← BitVec.ofNat_add]
  apply congrArg (BitVec.ofNat 32)
  dsimp [Word.value,limbBase,assembledLow,assembledHigh]
  ring

/-- Logical contributions plus the exact native filler reconstruct the candidate. -/
theorem right_assembly (mode : ShiftMode) (notLeft : mode ≠ .left) (lo hi amount : Nat)
    (low : lo < 65536) (high : hi < 65536) :
    (Word.toBitVec ⟨assembledLow mode lo hi amount,assembledHigh mode lo hi amount⟩) =
      ((BitVec.ofNat 32 lo) >>> amount + (BitVec.ofNat 32 (hi * 65536)) >>> amount) +
        BitVec.ofNat 32 (mode.filler hi amount) := by
  rw [← right_low lo amount low,← right_high hi amount high,← BitVec.ofNat_add,← BitVec.ofNat_add]
  apply congrArg (BitVec.ofNat 32)
  dsimp [Word.value,limbBase]
  simp only [assembledLow,assembledHigh,if_neg notLeft]
  have fill := Nat.mod_add_div (mode.filler hi amount) 65536
  omega

/-- Complete RV32 word semantics, retaining the original arithmetic-zero behavior. -/
theorem assembled_result (mode : ShiftMode) (lo hi : Nat) (amount : Fin 32)
    (low : lo < 65536) (high : hi < 65536) :
    (Word.toBitVec ⟨assembledLow mode lo hi amount.val,assembledHigh mode lo hi amount.val⟩) =
      mode.result (Word.toBitVec ⟨lo,hi⟩) amount.val := by
  cases mode
  · rw [left_assembly lo hi amount.val low high]
    simpa [ShiftBinop.Proofs.limbPieces,ShiftBinop.ShiftKind.result,ShiftMode.result] using
      ShiftBinop.Proofs.sll_limb_result lo hi amount low high
  · rw [right_assembly .right (by decide) lo hi amount.val low high]
    simpa [ShiftBinop.Proofs.limbPieces,ShiftBinop.ShiftKind.result,ShiftMode.result,ShiftMode.filler] using
      ShiftBinop.Proofs.srl_limb_result lo hi amount low high
  · rw [right_assembly .arithmetic (by decide) lo hi amount.val low high,filler_bits hi amount]
    rw [BitVec.add_comm (_ + _) _,← BitVec.add_assoc]
    simpa [ShiftBinop.Proofs.limbPieces,ShiftBinop.ShiftKind.result,ShiftMode.result] using
      ShiftBinop.Proofs.sra_limb_result lo hi amount low high

end Airbender.ReducedMachine.NativeShiftWordProofs
