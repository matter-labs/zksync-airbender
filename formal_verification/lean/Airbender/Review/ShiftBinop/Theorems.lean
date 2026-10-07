import Airbender.Proofs.ShiftBinop

namespace Airbender.ShiftBinop
open Airbender.Arithmetic

-- Local claims only: destination-to-Sail soundness remains to be proved.
theorem local_flags {p : Nat} [Fact p.Prime] {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints) :
    (w 4 = 0 ∨ w 4 = 1) ∧ ∀ i : Fin 2, w (11 + i.val) = 0 ∨ w (11 + i.val) = 1 :=
  Proofs.local_flags h

theorem local_ranges {p : Nat} [Fact p.Prime] {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints) :
    (w 13).val < limbBase ∧ (w 14).val < limbBase := Proofs.local_ranges h

/-- Final-PC bounds follow from the imported range queries. Initial bounds
    remain explicit; the increment excludes 32-bit overflow. -/
theorem pc_successor {p : Nat} [Fact p.Prime] (hp : 196608 < p)
    (inverse : (-30720 : ZMod p) * 65536 = 1)
    {w : Nat → ZMod p} {initial final : Word}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints)
    (mapping : w 0 = (initial.lo : ZMod p) ∧ w 1 = (initial.hi : ZMod p) ∧
      final.lo = (w 13).val ∧ final.hi = (w 14).val)
    (initialBound : initial.Bounded) :
    final.value = initial.value + 4 ∧ initial.value + 4 < wordModulus ∧
      final.toBitVec = initial.toBitVec + 4 :=
  Proofs.pc_successor hp inverse h mapping initialBound

end Airbender.ShiftBinop
