module
public import Human.Helpers.Memory.InitialImage
public import Slop.Arithmetic.Word
public import Slop.PCState
public import Human.Circuits.AddSub.RowInput
public import Mathlib.Tactic.IntervalCases

@[expose] public section

namespace Airbender.Trace.Proofs
open Arithmetic

theorem initial_token_word (cell : Cell) (value : BitVec 32) :
    (cell.initialToken (p := p) value).word = Word.ofBitVec value := by
  simp [Cell.initialToken, MemoryToken.word]

theorem cell_address_injective : Function.Injective Cell.addressCode := by
  intro left right same
  cases left with
  | register a =>
    cases right with
    | register b =>
      have index := (Nat.pair_eq_pair.mp (Nat.pair_eq_pair.mp same).2).1
      exact congrArg Cell.register (BitVec.eq_of_toNat_eq index)
    | ram b => simp [Cell.addressCode, Nat.pair_eq_pair] at same
  | ram a =>
    cases right with
    | register b => simp [Cell.addressCode, Nat.pair_eq_pair] at same
    | ram b =>
      have limbs := Nat.pair_eq_pair.mp (Nat.pair_eq_pair.mp same).2
      apply congrArg Cell.ram
      apply BitVec.eq_of_toNat_eq
      rw [← Word.ofBitVec_value a, ← Word.ofBitVec_value b]
      simp only [Word.value, limbs.1, limbs.2]

end Airbender.Trace.Proofs
