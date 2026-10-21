import Airbender.Proofs.Arithmetic.FieldChunks

namespace Airbender.Arithmetic
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

def carryLow {p : Nat} (value : ZMod p) : ZMod p := ((value.val % 2 : Nat) : ZMod p)
def carryHigh {p : Nat} (value : ZMod p) : ZMod p := ((value.val / 2 : Nat) : ZMod p)
def combinedLow {p : Nat} (value : ZMod p) : ZMod p := ((value.val % 16 : Nat) : ZMod p)
def combinedHigh {p : Nat} (value : ZMod p) : ZMod p := ((value.val / 16 : Nat) : ZMod p)

theorem carry_recompose {p : Nat} [Fact p.Prime] (value : ZMod p) :
    carryLow value + 2 * carryHigh value = value := by
  have split : value.val % 2 + 2 * (value.val / 2) = value.val := by omega
  calc
    carryLow value + 2 * carryHigh value =
        ((value.val % 2 + 2 * (value.val / 2) : Nat) : ZMod p) := by
      simp [carryLow, carryHigh]
    _ = (value.val : ZMod p) := by rw [split]
    _ = value := ZMod.natCast_zmod_val value

theorem carry_flags {p : Nat} [Fact p.Prime] {value : ZMod p} (bound : value.val < 3) :
    (carryLow value = 0 ∨ carryLow value = 1) ∧
      (carryHigh value = 0 ∨ carryHigh value = 1) := by
  have low : value.val % 2 = 0 ∨ value.val % 2 = 1 := by omega
  have high : value.val / 2 = 0 ∨ value.val / 2 = 1 := by omega
  constructor
  · rcases low with low | low <;> simp [carryLow, low]
  · rcases high with high | high <;> simp [carryHigh, high]

theorem combined_recompose {p : Nat} [Fact p.Prime] (value : ZMod p) :
    combinedLow value + 16 * combinedHigh value = value := by
  have split : value.val % 16 + 16 * (value.val / 16) = value.val := by omega
  calc
    combinedLow value + 16 * combinedHigh value =
        ((value.val % 16 + 16 * (value.val / 16) : Nat) : ZMod p) := by
      simp [combinedLow, combinedHigh]
    _ = (value.val : ZMod p) := by rw [split]
    _ = value := ZMod.natCast_zmod_val value

end Airbender.Arithmetic
