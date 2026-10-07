import Airbender.Proofs.ShiftBinop
import Airbender.Proofs.ShiftBinop.Soundness
import Airbender.Proofs.ShiftBinop.Shifts
import Airbender.Proofs.BabyBear

namespace Airbender.ShiftBinop
open Airbender.Arithmetic

-- Shared local claims for the imported shift/binop family.
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

/-- XOR/OR/AND and SLL/SRL/SRA, including immediate forms, against Sail execution and
    native register/PC effects. Lookups force all operand/result bytes. -/
theorem soundness {p : Nat} [Fact p.Prime] (hp : 262144 < p)
    (inverse : (-30720 : ZMod p) * 65536 = 1) :
    circuitModel.SoundnessUnder (InterfaceAssumptions (p := p)) spec :=
  Proofs.soundness hp inverse

theorem babyBear_soundness :
    circuitModel.SoundnessUnder (InterfaceAssumptions (p := babyBearModulus)) spec :=
  soundness (by decide) (by decide)

end Airbender.ShiftBinop
