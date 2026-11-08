module
public import Human.Circuits.Bigint.Execution
public import Slop.Bigint.SetupSoundness
public import Slop.Bigint.Multiplication
public import Slop.Delegation.Operations
public import Slop.Delegation.Requests
public import Slop.Delegation.PortEvents

@[expose] public section

namespace Airbender.Bigint.Native.Proofs
open Trace
set_option warningAsError true
set_option maxRecDepth 16384

theorem native_word_roles {p : Nat} (w : Nat → ZMod p) (i : Fin 8) :
    (Trace.readToken w (importedConstraintsMemoryPorts[1 + i.val]'(by change 1 + i.val < 19; omega))).word =
        ⟨(limbs w Variables.leftLimbs)[2 * i.val]'(by omega),
          (limbs w Variables.leftLimbs)[2 * i.val + 1]'(by omega)⟩ ∧
    ((⟨.bigint, w⟩ : Delegation.Row p).writeToken
      (importedConstraintsMemoryPorts[1 + i.val]'(by change 1 + i.val < 19; omega))).word =
        ⟨(output w).result[2 * i.val]'(by omega),
          (output w).result[2 * i.val + 1]'(by omega)⟩ ∧
    (Trace.readToken w (importedConstraintsMemoryPorts[10 + i.val]'(by change 10 + i.val < 19; omega))).word =
        ⟨(limbs w Variables.rightLimbs)[2 * i.val]'(by omega),
          (limbs w Variables.rightLimbs)[2 * i.val + 1]'(by omega)⟩ := by
  fin_cases i
  all_goals simp [readToken, MemoryPort.readCode, importedConstraintsMemoryPorts,
    Delegation.Row.writeToken, MemoryToken.word, MemoryPort.writeCode, WordColumns.code,
    limbs, output, Variables.leftLimbs, Variables.rightLimbs, Variables.writtenLimbs]

theorem arithmetic_effects {w : Nat → ZMod babyBearModulus}
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setupTable)) :
    ArithmeticEffects w := by
  refine ⟨?_, ?_, ?_⟩
  · intro operation selected
    apply Additive.Proofs.modeled_soundness (by decide) (additiveInput operation w) (output w) w
    refine ⟨holds, selected, ?_, ?_, ?_, ?_, rfl⟩
    · have flag := Control.Proofs.control_bits holds 6
      change w 65 = 0 ∨ w 65 = 1 at flag
      rcases flag with zero | one
      · simp [additiveInput, zero]
      · simp [additiveInput, one, ZMod.val_one'' (by decide : babyBearModulus ≠ 1)]
    · intro i; simp [additiveInput, limbs]
    · intro i; simp [additiveInput, limbs]
    · intro i; simp [output, limbs]
  · intro selected
    apply Equality.Proofs.modeled_soundness (by decide) (equalityInput w) (output w) w
    exact ⟨holds, selected, (by intro i; simp [equalityInput, limbs]), (by intro i; simp [equalityInput, limbs]),
      (by intro i; simp [output, limbs]), rfl⟩
  · intro operation selected
    apply Multiplication.Proofs.soundness (multiplicationInput operation w) (output w) w
    exact ⟨holds, selected, (by intro i; simp [multiplicationInput, limbs]), (by intro i; simp [multiplicationInput, limbs]),
      (by intro i; simp [output, limbs]), rfl⟩

end Airbender.Bigint.Native.Proofs
