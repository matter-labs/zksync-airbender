import Airbender.Review.AddSub.Model
import Airbender.Proofs.AddSub
import Airbender.Proofs.BabyBear
import Airbender.Proofs.AddSub.PC
import Airbender.Proofs.AddSub.Selectors
import Airbender.Proofs.AddSub.Timestamp
import Airbender.Proofs.AddSub.Modular
import Airbender.Proofs.AddSub.NonDeterminism

namespace Airbender.AddSub
open Airbender.Reference.RiscV

/-- Any satisfying assignment with the stated interfaces agrees with Sail's execution.
    Covers ADD/ADDI/SUB/LUI/AUIPC, including x0/NOP preprocessing and discarded writes.
    Includes nextPC initialization and PC retirement for the normal decoded four-byte path. -/
theorem soundness {p : Nat} [Fact p.Prime]
    (hp : 196608 < p) (inverse : (-30720 : ZMod p) * 65536 = 1) :
    (circuitModel (p := p)).SoundnessUnder InterfaceAssumptions Sail.spec :=
  Proofs.soundness hp inverse

/-- Concrete instance for the imported BabyBear artifact. -/
theorem babyBear_soundness :
    (circuitModel (p := babyBearModulus)).SoundnessUnder InterfaceAssumptions Sail.spec :=
  soundness (p := babyBearModulus) (by decide) (by decide)

/-- Local equations enforce Boolean flags. The decoder contract supplies their
    instruction meaning and selection; Booleanity alone does not imply exclusivity. -/
theorem local_flags {p : Nat} [Fact p.Prime] {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints) :
    (w 4 = 0 ∨ w 4 = 1) ∧ ∀ k : Fin 9, w (10 + k.val) = 0 ∨ w (10 + k.val) = 1 :=
  Proofs.local_flags h

/-- Local delegation premises for the permutation interface; dispatch identity and
    delegated computation effects are still external obligations. -/
theorem delegation_zeroes {p : Nat} [Fact p.Prime] {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints)
    (selected : w 17 = 1) :
    w 29 = 0 ∧ w 30 = 0 ∧ w 27 = 0 ∧ w 28 = 0 ∧ w 33 = 0 ∧ w 34 = 0 :=
  Proofs.delegation_zeroes h selected

/-- Conditional native-state composition, shared across the covered instructions.
    The execution/memory argument must establish the state link. -/
theorem compose {first second : Sail.Input} {firstOutput secondOutput : Sail.Output}
    (hfirst : Sail.spec first firstOutput) (hsecond : Sail.spec second secondOutput)
    (link : ∀ after, Reference.Sail.run (Sail.projectedStep first.rd firstOutput) first.before =
      .ok SailRV32.Functions.RETIRE_SUCCESS after → second.before = after) :
    ∃ after,
      Reference.Sail.run (do let _ ← Sail.normalStep (Sail.execution first); Sail.normalStep (Sail.execution second)) first.before =
        .ok SailRV32.Functions.RETIRE_SUCCESS after ∧
      Reference.Sail.run (Sail.projectedStep first.rd firstOutput >>= fun _ =>
        Sail.projectedStep second.rd secondOutput) first.before = .ok SailRV32.Functions.RETIRE_SUCCESS after :=
  Sail.compose hfirst hsecond link

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

/-- ADDMOD/SUBMOD/MULMOD/FMAMOD canonical results and native register/PC effects,
    including old-destination reads, aliasing and discarded x0 writes. Custom arithmetic
    is the reviewed project specification, not an upstream Sail instruction. -/
theorem Modular.soundness :
    Modular.circuitModel.SoundnessUnder Modular.InterfaceAssumptions Modular.spec :=
  Proofs.modular_soundness

/-- CSRRW x0, 0x7C0, rs1 preserves native state except nextPC/PC retirement.
    The custom project specification treats source values as unproved hints;
    oracle responses and application I/O are not covered by this claim. -/
theorem NonDeterminism.write_soundness {p : Nat} [Fact p.Prime]
    (hp : 196608 < p) (inverse : (-30720 : ZMod p) * 65536 = 1) :
    (NonDeterminism.writeModel (p := p)).SoundnessUnder
      NonDeterminism.WriteInterfaces NonDeterminism.writeSpec :=
  Proofs.nondeterminism_write_soundness hp inverse

theorem NonDeterminism.babyBear_write_soundness :
    (NonDeterminism.writeModel (p := babyBearModulus)).SoundnessUnder
      NonDeterminism.WriteInterfaces NonDeterminism.writeSpec :=
  NonDeterminism.write_soundness (by decide) (by decide)

/-- PC advances by four, with no 32-bit overflow, for any satisfying assignment.
    Initial PC bounds are a state-interface premise; final bounds come from lookups.
    This local theorem is reused by the combined Sail soundness claim. -/
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
