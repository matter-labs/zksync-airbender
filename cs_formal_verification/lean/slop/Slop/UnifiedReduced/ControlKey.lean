import Human.Circuits.UnifiedReduced.Tables.Setup
import Slop.Lookups

namespace Airbender.UnifiedReduced.Proofs
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000

private theorem packed_bits {right left borrow equal tag : Nat}
    (rightBound : right < 65536) (leftBound : left < 2) (borrowBound : borrow < 2)
    (equalBound : equal < 2) (tagBound : tag < 8) :
    let packed := right + 65536 * left + 131072 * borrow + 262144 * equal + 524288 * tag
    packed / 32768 % 2 = right / 32768 ∧ packed / 65536 % 2 = left ∧
      packed / 131072 % 2 = borrow ∧ packed / 262144 % 2 = equal ∧ packed / 524288 % 8 = tag := by
  dsimp only
  repeat' apply And.intro
  all_goals omega

theorem conditional_sign_key {right left borrow equal tag : Nat}
    (rightBound : right < 65536) (leftBound : left < 2) (borrowBound : borrow < 2)
    (equalBound : equal < 2) (tagBound : tag < 8) :
    Verification.conditionalValue
      (right + 65536 * left + 131072 * borrow + 262144 * equal + 524288 * tag) =
    Verification.conditionalValue (Setup.conditionalKey
      (right / 32768 + 2 * left + 4 * borrow + 8 * equal + 16 * tag)) := by
  have signBound : right / 32768 < 2 := by omega
  have native :
      (right / 32768 + 2 * left + 4 * borrow + 8 * equal + 16 * tag) % 2 = right / 32768 ∧
      (right / 32768 + 2 * left + 4 * borrow + 8 * equal + 16 * tag) / 2 % 2 = left ∧
      (right / 32768 + 2 * left + 4 * borrow + 8 * equal + 16 * tag) / 4 % 2 = borrow ∧
      (right / 32768 + 2 * left + 4 * borrow + 8 * equal + 16 * tag) / 8 % 2 = equal ∧
      (right / 32768 + 2 * left + 4 * borrow + 8 * equal + 16 * tag) / 16 % 8 = tag := by
    repeat' apply And.intro
    all_goals omega
  have original := packed_bits rightBound leftBound borrowBound equalBound tagBound
  have canonical := packed_bits (right := right / 32768 * 32768) (by omega)
    leftBound borrowBound equalBound tagBound
  have sign : right / 32768 * 32768 / 32768 = right / 32768 := by omega
  simp only [Setup.conditionalKey, native.1, native.2.1, native.2.2.1,
    native.2.2.2.1, native.2.2.2.2]
  rw [Nat.mul_comm left 65536, Nat.mul_comm borrow 131072,
    Nat.mul_comm equal 262144, Nat.mul_comm tag 524288]
  simp only [Verification.conditionalValue, original.1, original.2.1, original.2.2.1,
    original.2.2.2.1, original.2.2.2.2, canonical.1, canonical.2.1,
    canonical.2.2.1, canonical.2.2.2.1, canonical.2.2.2.2, sign]

end Airbender.UnifiedReduced.Proofs
