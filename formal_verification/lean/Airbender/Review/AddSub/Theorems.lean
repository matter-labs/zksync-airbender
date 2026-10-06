import Airbender.Review.AddSub.Model
import Airbender.Proofs.AddSub
import Airbender.Proofs.BabyBear
import Airbender.Proofs.AddSub.PC

namespace Airbender.AddSub
open Airbender.Reference.RiscV

/-- Any satisfying assignment with the stated interfaces agrees with Sail's execution.
    Covers ADD/ADDI/SUB/LUI/AUIPC destination writes; PC sequencing is a later obligation. -/
theorem soundness {p : Nat} [Fact p.Prime]
    (hp : 196608 < p) :
    (circuitModel (p := p)).SoundnessUnder InterfaceAssumptions Sail.spec :=
  Proofs.soundness hp

/-- Concrete instance for the imported BabyBear artifact. -/
theorem babyBear_soundness :
    (circuitModel (p := babyBearModulus)).SoundnessUnder InterfaceAssumptions Sail.spec :=
  soundness (p := babyBearModulus) (by decide)

/-- PC advances by four, with no 32-bit overflow, for any satisfying assignment.
    Initial PC bounds are a state-interface premise; final bounds come from lookups.
    This is the local equation theorem, before connection to Sail's full PC step. -/
theorem pc_successor {p : Nat} [Fact p.Prime]
    (hp : 196608 < p) (inverse : (-30720 : ZMod p) * 65536 = 1)
    {w : Nat → ZMod p} {initial final : Arithmetic.Word}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints)
    (mapping : PCMapping initial final w) (initialBounds : initial.Bounded) :
    final.value = initial.value + 4 ∧ initial.value + 4 < Arithmetic.wordModulus ∧
      final.toBitVec = initial.toBitVec + 4 :=
  Proofs.pc_successor hp inverse h mapping initialBounds

theorem babyBear_pc_successor {w : Nat → ZMod babyBearModulus}
    {initial final : Arithmetic.Word}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints)
    (mapping : PCMapping initial final w) (initialBounds : initial.Bounded) :
    final.value = initial.value + 4 ∧ initial.value + 4 < Arithmetic.wordModulus ∧
      final.toBitVec = initial.toBitVec + 4 :=
  pc_successor (by decide) (by decide) h mapping initialBounds

end Airbender.AddSub
