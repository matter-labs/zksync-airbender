module
public import Proven.Blake2Round.Mask.Native
public import Proven.NonVacuous.Blake2RoundSpan.Row

@[expose] public section
namespace Airbender.Blake2Round.Mask.Proofs
open Arithmetic
set_option maxRecDepth 32768

/-- A later reference round with zero data supplies the unchanged query values. -/
def zeroSource : NonVacuous.Blake2RoundSpan.RowInput where
  round := 1
  statePointer := ⟨0, 64⟩
  messagePointer := ⟨128, 64⟩
  state _ := ⟨0, 0⟩
  extended _ := ⟨0, 0⟩
  message _ := ⟨0, 0⟩
  previous _ := 0
  invocation := 1

theorem zeroSource_valid : zeroSource.Valid where
  statePointer := by norm_num [zeroSource, Word.Bounded, limbBase]
  messagePointer := by norm_num [zeroSource, Word.Bounded, limbBase]
  state _ _ := by norm_num [zeroSource, Word.Bounded, limbBase]
  extended _ _ := by norm_num [zeroSource, Word.Bounded, limbBase]
  message _ _ := by norm_num [zeroSource, Word.Bounded, limbBase]
  previous _ _ := by change 0 < 1 + 2; decide
  invocation := by decide
  room := by decide

/-- The active zero-mask row has zero data, aligned RAM pointers and strict timestamp borrows. -/
def zeroAssignment (index : Nat) : ZMod babyBearModulus :=
  if index = 0 ∨ index = 1 then 1
  else if index = 4 ∨ index = 102 then 64
  else if index = 101 then 128
  else if 632 ≤ index ∧ index < 761 ∧ (index - 632) % 3 = 2 then 1
  else 0

theorem zero_asserts : ∀ i : Fin 220,
    ((FlatOperation.constraints (importedConstraints (p := babyBearModulus) setupTable)).get
      ⟨i.val, by rw [constraint_count]; exact i.isLt⟩).eval
      (Verification.environment zeroAssignment) = 0 := by
  decide +kernel

end Airbender.Blake2Round.Mask.Proofs
