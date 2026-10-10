import Airbender.Proofs.ShiftBinop.Arithmetic

namespace Airbender.Verification
open Arithmetic
set_option warningAsError true
set_option maxRecDepth 16384

theorem shift_assembly (tag : Nat) (valid : tag = 1 ∨ tag = 2 ∨ tag = 3 ∨ tag = 5)
    (x : BitVec 32) (amount : Nat) (reverse : tag = 5 → amount = 0)
    (parts : Fin 4 → Fin 4 → Nat) (output : Word)
    (bytes : ∀ i j : Fin 4, parts i j =
      ((shiftByteContribution i.val (x.extractLsb' (8 * i.val) 8).toNat amount tag).extractLsb' (8 * j.val) 8).toNat)
    (low : output.lo = parts 0 0 + 256 * parts 0 1 + parts 1 0 + 256 * parts 1 1 +
      parts 2 0 + 256 * parts 2 1 + parts 3 0 + 256 * parts 3 1)
    (high : output.hi = parts 0 2 + 256 * parts 0 3 + parts 1 2 + 256 * parts 1 3 +
      parts 2 2 + 256 * parts 2 3 + parts 3 2 + 256 * parts 3 3) :
    output.toBitVec = shiftOperation tag x amount := by
  let contribution (i : Fin 4) := shiftByteContribution i.val (x.extractLsb' (8 * i.val) 8).toNat amount tag
  have rebuild (i : Fin 4) :
      parts i 0 + 256 * parts i 1 + 65536 * parts i 2 + 16777216 * parts i 3 = (contribution i).toNat := by
    rw [bytes i 0, bytes i 1, bytes i 2, bytes i 3]
    exact (bytes_value (contribution i)).symm
  have value : output.value = (contribution 0).toNat + (contribution 1).toNat +
      (contribution 2).toNat + (contribution 3).toNat := by
    rw [Word.value, low, high, ← rebuild 0, ← rebuild 1, ← rebuild 2, ← rebuild 3]
    dsimp [limbBase]
    ring
  have combined := shift_contributions_value tag valid x amount reverse
  change (shiftOperation tag x amount).toNat =
    (contribution 0).toNat + (contribution 1).toNat + (contribution 2).toNat + (contribution 3).toNat at combined
  apply BitVec.eq_of_toNat_eq
  change output.value % wordModulus = _
  rw [value, ← combined]
  exact Nat.mod_eq_of_lt (shiftOperation tag x amount).isLt

theorem sum_byte_pairs [Fact p.Prime] (hp : 262144 < p)
    (bytes : Fin 4 → Fin 2 → ZMod p) (target : ZMod p)
    (small : ∀ i j, (bytes i j).val < 256)
    (equation : bytes 0 0 + 256 * bytes 0 1 + bytes 1 0 + 256 * bytes 1 1 +
      bytes 2 0 + 256 * bytes 2 1 + bytes 3 0 + 256 * bytes 3 1 = target) :
    target.val = (bytes 0 0).val + 256 * (bytes 0 1).val + (bytes 1 0).val + 256 * (bytes 1 1).val +
      (bytes 2 0).val + 256 * (bytes 2 1).val + (bytes 3 0).val + 256 * (bytes 3 1).val := by
  let total := (bytes 0 0).val + 256 * (bytes 0 1).val + (bytes 1 0).val + 256 * (bytes 1 1).val +
    (bytes 2 0).val + 256 * (bytes 2 1).val + (bytes 3 0).val + 256 * (bytes 3 1).val
  have field : target = (total : ZMod p) := by
    dsimp [total]
    push_cast
    simpa only [ZMod.natCast_zmod_val] using equation.symm
  have bound : total < p := by
    have a := small 0 0; have b := small 0 1; have c := small 1 0; have d := small 1 1
    have e := small 2 0; have f := small 2 1; have g := small 3 0; have h := small 3 1
    dsimp [total]
    omega
  rw [field, ZMod.val_natCast, Nat.mod_eq_of_lt bound]

end Airbender.Verification
