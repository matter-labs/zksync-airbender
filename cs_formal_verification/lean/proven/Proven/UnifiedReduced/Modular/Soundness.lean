module
public import Human.Circuits.UnifiedReduced.Modular
public import Proven.AddSub.Modular.RVArithmetic

@[expose] public section
namespace Airbender.UnifiedReduced.Modular
open Arithmetic

/-- The selected modular branch checks the same two-limb subtraction against the guest
    prime in either host. Field capacity lifts its borrow equations to natural numbers. -/
theorem canonical_of_comparison {p : Nat} [CircuitField p] {w : Nat → ZMod p}
    (out : (wordAt w 50).Bounded) (rem : (wordAt w 74).Bounded) (bit : (w 53).val ≤ 1)
    (low : w 74 + 1 = w 50 + 65536 * w 53)
    (high : w 53 + w 75 + 30720 = w 51 + 65536) : (wordAt w 50).value < babyBearModulus := by
  apply (Word.borrow_iff (p := p) (left := wordAt w 50) (right := ⟨1, 30720⟩)
    (remainder := wordAt w 74) (lt_of_le_of_lt (by decide) CircuitField.limbCapacity)
    out ⟨by decide, by decide⟩ rem (carry := (w 53).val) bit (borrow := 1) (by decide) ?_ ?_).mp rfl
  · simpa [wordAt] using low
  · simpa [wordAt] using high

/-- The one-hot modular branch clears all ordinary arithmetic alternatives and selects
    exactly one of ADD, SUB, MUL or FMA. -/
theorem selected {p : Nat} [CircuitField p] {w : Nat → ZMod p} {op : AddSub.Modular.Opcode}
    (flags : ∀ k, 11 ≤ k → k ≤ 20 → w k = if k = op.selector + 1 then 1 else 0) :
    w 11 = 0 ∧ w 12 = 0 ∧ w 13 = 0 ∧ w 20 = 0 ∧ w 14 + w 15 + w 16 + w 17 = 1 := by
  cases op <;> simp (disch := decide) [flags, AddSub.Modular.Opcode.selector]

/-- Canonicalize the guest residue, then apply the Montgomery/RV correspondence.
    Both operations take place in the guest field, independently of the circuit host. -/
theorem soundness {p : Nat} [CircuitField p] {ops : Operations p}
    (certificate : ResultCertificate p ops) : ResultSoundness p ops := by
  intro setup w op holds flags left right old
  obtain ⟨bound, residue⟩ := certificate setup w op holds flags left right old
  rw [← AddSub.Modular.arithmeticResult_rv, Word.toBitVec, ← residue, ZMod.val_natCast_of_lt bound]

end Airbender.UnifiedReduced.Modular
