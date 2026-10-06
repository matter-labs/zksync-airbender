import Airbender.Proofs.JumpBranchSlt
import Airbender.Proofs.BabyBear

namespace Airbender.JumpBranchSlt
open Airbender.Arithmetic

/-- Partial family coverage: local flags, without decoded instruction meaning. -/
theorem local_flags {p : Nat} [Fact p.Prime] {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints) :
    (w 4 = 0 ∨ w 4 = 1) ∧ ∀ k : Fin 5, w (11 + k.val) = 0 ∨ w (11 + k.val) = 1 :=
  Proofs.local_flags h

/-- All four retained 16-bit queries; generic comparison/alignment lookups are not emitted. -/
theorem local_ranges {p : Nat} [Fact p.Prime] {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints) :
    (w 34).val < limbBase ∧ (w 35).val < limbBase ∧
      (w 1).val < limbBase ∧ (w 36).val < limbBase :=
  Proofs.local_ranges h

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

/-- The retained subtraction computes an unsigned comparison borrow. This is not
    yet SLTU instruction soundness: its resolution lookup and Sail effect link remain. -/
theorem unsigned_borrow {p : Nat} [Fact p.Prime] (hp : 196608 < p)
    {w : Nat → ZMod p} {left right : Word}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints)
    (selected : w 13 = 1) (other : w 11 = 0 ∧ w 12 = 0 ∧ w 14 = 0)
    (immediate : w 8 = 0 ∧ w 9 = 0)
    (mapping : w 22 = (left.lo : ZMod p) ∧ w 23 = (left.hi : ZMod p) ∧
      w 26 = (right.lo : ZMod p) ∧ w 27 = (right.hi : ZMod p))
    (leftBound : left.Bounded) (rightBound : right.Bounded) :
    w 38 = 1 ↔ left.value < right.value :=
  Proofs.unsigned_borrow hp h selected other immediate mapping leftBound rightBound

end Airbender.JumpBranchSlt
