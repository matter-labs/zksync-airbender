import Airbender.Review.AddSub.Model
import Airbender.Proofs.AddSub
import Airbender.Proofs.BabyBear
import Airbender.Proofs.AddSub.PC
import Airbender.Proofs.AddSub.Selectors
import Airbender.Proofs.AddSub.Timestamp
import Airbender.Proofs.AddSub.Modular

namespace Airbender.AddSub
open Airbender.Reference.RiscV

/-- Any satisfying assignment with the stated interfaces agrees with Sail's execution.
    Covers ADD/ADDI/SUB/LUI/AUIPC, including x0/NOP preprocessing and discarded writes.
    PC sequencing is a later obligation. -/
theorem soundness {p : Nat} [Fact p.Prime]
    (hp : 196608 < p) :
    (circuitModel (p := p)).SoundnessUnder InterfaceAssumptions Sail.spec :=
  Proofs.soundness hp

/-- Concrete instance for the imported BabyBear artifact. -/
theorem babyBear_soundness :
    (circuitModel (p := babyBearModulus)).SoundnessUnder InterfaceAssumptions Sail.spec :=
  soundness (p := babyBearModulus) (by decide)

/-- Local equations enforce Boolean flags. The decoder contract supplies their
    instruction meaning and selection; Booleanity alone does not imply exclusivity. -/
theorem local_flags {p : Nat} [Fact p.Prime] {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints) :
    (w 4 = 0 ∨ w 4 = 1) ∧ ∀ k : Fin 9, w (10 + k.val) = 0 ∨ w (10 + k.val) = 1 :=
  Proofs.local_flags h

/-- Local timestamp increment, in 19-bit limbs. These are field equations;
    timestamp range lookups and global ordering are outside the current import. -/
theorem timestamp_equations {p : Nat} [Fact p.Prime]
    (inverse : (-3840 : ZMod p) * 524288 = 1) {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints) :
    ∃ c : Nat, c ≤ 1 ∧ w 2 + 4 = w 21 + 524288 * c ∧ w 3 + c = w 22 :=
  Proofs.timestamp_equations inverse h

theorem babyBear_timestamp_equations {w : Nat → ZMod babyBearModulus}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints) :
    ∃ c : Nat, c ≤ 1 ∧ w 2 + 4 = w 21 + 524288 * c ∧ w 3 + c = w 22 :=
  timestamp_equations (by decide) h

/-- ADDMOD/SUBMOD/MULMOD/FMAMOD word-level soundness, including canonical output
    and the specified Montgomery factor. Architectural register/PC binding is pending. -/
theorem Modular.soundness :
    Modular.circuitModel.SoundnessUnder Modular.InterfaceAssumptions Modular.spec :=
  Proofs.modular_soundness

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
