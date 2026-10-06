import Airbender.Proofs.JumpBranchSlt.Soundness
import Airbender.Proofs.BabyBear

namespace Airbender.JumpBranchSlt
open Airbender.Arithmetic

/-- Partial family coverage: local flags, without decoded instruction meaning. -/
theorem local_flags {p : Nat} [Fact p.Prime] {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints) :
    (w 4 = 0 ∨ w 4 = 1) ∧ ∀ k : Fin 5, w (11 + k.val) = 0 ∨ w (11 + k.val) = 1 :=
  Proofs.local_flags h

/-- Bounds from the four retained 16-bit queries. -/
theorem local_ranges {p : Nat} [Fact p.Prime] {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints) :
    (w 34).val < limbBase ∧ (w 35).val < limbBase ∧
      (w 1).val < limbBase ∧ (w 36).val < limbBase :=
  Proofs.local_ranges h

/-- Zero, sign, conditional-resolution and low-PC cleanup values follow from
    native Clean membership in the modeled fixed tables. Table provenance is unproved. -/
theorem lookup_values {p : Nat} [Fact p.Prime] (hp : 4194304 ≤ p)
    {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints) :
    w 41 = (if (w 34 + w 35).val = 0 then 1 else 0) ∧
    w 42 = (((w 23).val / 32768 : Nat) : ZMod p) ∧
    w 44 = (Verification.conditionalValue
      (w 43 + 65536 * w 42 + 131072 * w 38 + 262144 * w 41 + 524288 * w 10).val : ZMod p) ∧
    w 46 = (((w 36).val / 2 % 2 : Nat) : ZMod p) ∧
    w 16 = (((w 36).val - (w 36).val % 4 : Nat) : ZMod p) :=
  Proofs.lookup_values hp h

/-- Local field equations, without integer timestamp bounds or global ordering. -/
theorem timestamp_equations {p : Nat} [Fact p.Prime]
    (inverse : (-3840 : ZMod p) * 524288 = 1) {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints) :
    ∃ c : Nat, c ≤ 1 ∧ w 2 + 4 = w 18 + 524288 * c ∧ w 3 + c = w 19 :=
  Proofs.timestamp_equations inverse h

theorem babyBear_timestamp_equations {w : Nat → ZMod babyBearModulus}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints) :
    ∃ c : Nat, c ≤ 1 ∧ w 2 + 4 = w 18 + 524288 * c ∧ w 3 + c = w 19 :=
  timestamp_equations (by decide) h

/-- The retained subtraction computes an unsigned comparison borrow. -/
theorem unsigned_borrow {p : Nat} [Fact p.Prime] (hp : 196608 < p)
    {w : Nat → ZMod p} {left right : Word}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints)
    (selected : w 13 = 1) (other : w 11 = 0 ∧ w 12 = 0 ∧ w 14 = 0)
    (mapping : w 22 = (left.lo : ZMod p) ∧ w 23 = (left.hi : ZMod p) ∧
      w 26 + w 8 = (right.lo : ZMod p) ∧ w 27 + w 9 = (right.hi : ZMod p))
    (leftBound : left.Bounded) (rightBound : right.Bounded) :
    w 38 = 1 ↔ left.value < right.value :=
  Proofs.unsigned_borrow hp h selected other mapping leftBound rightBound

/-- The local SLTU/SLTIU destination is the unsigned comparison bit, derived through
    the imported resolution lookup. -/
theorem unsigned_destination {p : Nat} [Fact p.Prime] (hp : 4194304 ≤ p)
    {w : Nat → ZMod p} {left right : Word}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints)
    (selected : w 13 = 1) (other : w 11 = 0 ∧ w 12 = 0 ∧ w 14 = 0)
    (funct3 : w 10 = 3) (nonzero : w 15 = 0)
    (mapping : w 22 = (left.lo : ZMod p) ∧ w 23 = (left.hi : ZMod p) ∧
      w 26 + w 8 = (right.lo : ZMod p) ∧ w 27 + w 9 = (right.hi : ZMod p))
    (leftBound : left.Bounded) (rightBound : right.Bounded) :
    (⟨(w 30).val, (w 31).val⟩ : Word).value =
      if left.value < right.value then 1 else 0 :=
  Proofs.unsigned_destination hp h selected other funct3 nonzero mapping
    ⟨rfl, rfl⟩ leftBound rightBound

/-- The signed comparison result is proved through the same imported resolution
    query and subtraction borrow, using native bitvector signed ordering. -/
theorem signed_destination {p : Nat} [Fact p.Prime] (hp : 4194304 ≤ p)
    {w : Nat → ZMod p} {left right : Word}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints)
    (selected : w 13 = 1) (other : w 11 = 0 ∧ w 12 = 0 ∧ w 14 = 0)
    (funct3 : w 10 = 2) (nonzero : w 15 = 0)
    (mapping : w 22 = (left.lo : ZMod p) ∧ w 23 = (left.hi : ZMod p) ∧
      w 26 + w 8 = (right.lo : ZMod p) ∧ w 27 + w 9 = (right.hi : ZMod p))
    (leftBound : left.Bounded) (rightBound : right.Bounded) :
    (⟨(w 30).val, (w 31).val⟩ : Word).value =
      if left.toBitVec.toInt < right.toBitVec.toInt then 1 else 0 :=
  Proofs.signed_destination hp h selected other funct3 nonzero mapping
    ⟨rfl, rfl⟩ leftBound rightBound

namespace Comparison

/-- Shared soundness for SLT, SLTI, SLTU and SLTIU against native Sail register
    and PC effects. Alignment and the final-PC high bound are explicit
    interfaces; the imported arithmetic allows 32-bit PC wraparound. -/
theorem soundness {p : Nat} [Fact p.Prime] (hp : 4194304 ≤ p) :
    circuitModel.SoundnessUnder (InterfaceAssumptions (p := p)) spec :=
  Proofs.comparison_soundness hp

theorem babyBear_soundness :
    circuitModel.SoundnessUnder (InterfaceAssumptions (p := babyBearModulus)) spec :=
  soundness (by decide)

end Comparison

end Airbender.JumpBranchSlt
