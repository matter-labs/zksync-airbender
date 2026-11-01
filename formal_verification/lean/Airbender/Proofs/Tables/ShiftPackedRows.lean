import Airbender.Proofs.Tables.ShiftPackedRowBinding

namespace Airbender.Verification.ShiftPackedReference
open Airbender.Setup.Proofs PackedSignedRun PackedWordBounds PackedWordColumn
set_option warningAsError true
set_option Elab.async false

theorem numericRow_bound (lane row : Nat) : numericRow lane row < 65536 ^ 256 := by
  unfold numericRow
  split
  · exact Nat.mod_lt _ (by positivity)
  · positivity

/-- Join complete control rows in a balanced tree. -/
def packedRows (lane first : Nat) : Nat → Nat
  | 0 => numericRow lane first
  | depth + 1 => packedRows lane first depth +
      wordPower (256 * 2 ^ depth) * packedRows lane (first + 2 ^ depth) depth

theorem packedRows_bound (lane first depth : Nat) :
    packedRows lane first depth < 65536 ^ (256 * 2 ^ depth) := by
  induction depth generalizing first with
  | zero => exact numericRow_bound lane first
  | succ depth ih =>
    have result := concat_bound _ _ _ _ (ih first) (ih (first + 2 ^ depth))
    have extent : 256 * 2 ^ (depth + 1) = 256 * 2 ^ depth + 256 * 2 ^ depth := by
      rw [pow_succ]; omega
    simpa only [packedRows, extent] using result

theorem packedRows_digit (lane first depth index : Nat) (laneBound : lane < 4)
    (rowBound : first + index / 256 < 1024) (within : index < 256 * 2 ^ depth) :
    digit 65536 (packedRows lane first depth) index =
      rowByte lane ((first + index / 256) / 256) ((first + index / 256) % 256) (index % 256) := by
  induction depth generalizing first index with
  | zero =>
    have quotient : index / 256 = 0 := Nat.div_eq_of_lt (by simpa using within)
    simp only [packedRows, quotient, Nat.add_zero, Nat.mod_eq_of_lt (show index < 256 by simpa using within)]
    rw [numericRow_binding ⟨lane, laneBound⟩ first (by simpa only [quotient, Nat.add_zero] using rowBound)]
    exact expectedRow_digit lane first index laneBound (by simpa only [quotient, Nat.add_zero] using rowBound) (by simpa using within)
  | succ depth ih =>
    have total : 256 * 2 ^ (depth + 1) = 256 * 2 ^ depth + 256 * 2 ^ depth := by
      rw [pow_succ]; omega
    by_cases low : index < 256 * 2 ^ depth
    · rw [packedRows, concat_low _ _ _ _ (packedRows_bound lane first depth) low]
      exact ih first index rowBound low
    · have tail : index - 256 * 2 ^ depth < 256 * 2 ^ depth := by omega
      have projected := concat_high (packedRows lane first depth)
        (packedRows lane (first + 2 ^ depth) depth) (256 * 2 ^ depth)
        (index - 256 * 2 ^ depth) (packedRows_bound lane first depth)
      rw [show 256 * 2 ^ depth + (index - 256 * 2 ^ depth) = index from by omega] at projected
      have parts := Nat.div_add_mod (index - 256 * 2 ^ depth) 256
      have original := Nat.div_add_mod index 256
      have small := Nat.mod_lt (index - 256 * 2 ^ depth) (show 0 < 256 by omega)
      have originalSmall := Nat.mod_lt index (show 0 < 256 by omega)
      have sameRow : first + 2 ^ depth + (index - 256 * 2 ^ depth) / 256 =
          first + index / 256 := by omega
      have sameControl : (index - 256 * 2 ^ depth) % 256 = index % 256 := by omega
      rw [packedRows, projected, ih (first + 2 ^ depth) _ (by rwa [sameRow]) tail,
        sameRow, sameControl]

def expectedSpan (lane start count : Nat) : Nat :=
  packedRows lane (start / 256) 4 / wordPower (start % 256) % wordPower count

def checkSpan (lane start count payload : Nat) : Bool :=
  decide (start + count ≤ 262144 ∧ start % 256 + count ≤ 4096) &&
    payload == expectedSpan lane start count

theorem expectedSpan_digit (lane start count index : Nat) (laneBound : lane < 4)
    (inside : start + count ≤ 262144) (spanBound : start % 256 + count ≤ 4096)
    (within : index < count) :
    digit 65536 (expectedSpan lane start count) index = ShiftCertificate.outputNatByte lane (start + index) := by
  have projection := segment_digit 65536 (packedRows lane (start / 256) 4)
    (start % 256) count index within
  rw [expectedSpan, wordPower_eq, wordPower_eq, projection]
  have quotient : start / 256 + (start % 256 + index) / 256 = (start + index) / 256 := by omega
  have remainder : (start % 256 + index) % 256 = (start + index) % 256 := by omega
  rw [packedRows_digit lane (start / 256) 4 (start % 256 + index) laneBound
    (by rw [quotient]; omega) (by change start % 256 + index < 4096; omega), quotient, remainder]
  have position : (start + index) / 256 / 256 = (start + index) / 65536 := by omega
  have amount : (start + index) % 256 / 8 % 32 = (start + index) / 8 % 32 := by omega
  have operation : (start + index) % 256 % 8 = (start + index) % 8 := by omega
  simp only [rowByte, position, amount, operation, ShiftCertificate.outputNatByte]

theorem checkSpan_sound (lane : Nat) (laneBound : lane < 4) (start count payload : Nat)
    (checked : checkSpan lane start count payload = true) (index : Nat) (within : index < count) :
    digit 65536 payload index = ShiftCertificate.outputNatByte lane (start + index) := by
  simp only [checkSpan, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at checked
  rw [checked.2]
  exact expectedSpan_digit lane start count index laneBound checked.1.1 checked.1.2 within

end Airbender.Verification.ShiftPackedReference
