module
public import Proven.Blake2G.NativeControl

@[expose] public section
namespace Airbender.Blake2G.Proofs
set_option warningAsError true
open Arithmetic
set_option backward.isDefEq.respectTransparency false

/-- The native G body has the exact reference state update and native counter reset. -/
theorem native_g_body (register : Fin 256) (state message : RV.Word) (mem : RV.Word → BitVec 8) :
    RV.Delegation.blakeGNative state message (BitVec.ofNat 32 register.val) mem =
      { writes := RV.writesAt state (RV.gStep (RV.readWords mem message 16) (nativeIndex register)
          (RV.readWords mem state 16)), reg := 12,
        val := (Control.step ⟨register, true⟩).register.toBitVec } := by
  have byte : (BitVec.ofNat 32 register.val).toNat = register.val := by
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show register.val < 2 ^ 32 by have := register.isLt; omega)]
  have bits := native_control_bits register
  simp only [RV.Delegation.blakeGNative, byte, bits.1]
  change (⟨RV.writesAt state (RV.gStep (RV.readWords mem message 16) (nativeIndex register)
      (RV.readWords mem state 16)), 12, _⟩ : RV.Effect) = _
  exact congrArg (RV.Effect.mk _ 12) bits.2

/-- The RV G effect accepts aligned block bases and implements the native byte behavior. -/
theorem native_g_effect (register : Fin 256) (state message : RV.Word) (mem : RV.Word → BitVec 8)
    (stateAligned : state.toNat % 64 = 0) (messageAligned : message.toNat % 64 = 0)
    (messageFits : message.toNat + 64 ≤ RV.RAM_END) :
    RV.Delegation.blakeG state message (BitVec.ofNat 32 register.val) mem =
      some (⟨RV.writesAt state (RV.gStep (RV.readWords mem message 16) (nativeIndex register)
          (RV.readWords mem state 16)), 12,
        (Control.step ⟨register, true⟩).register.toBitVec⟩ : RV.Effect) := by
  have byte : (BitVec.ofNat 32 register.val).toNat < 256 := by
    simp only [BitVec.toNat_ofNat]
    omega
  by_cases separate : state ≠ message
  · simp only [RV.Delegation.blakeG, stateAligned, messageAligned, messageFits, separate, byte,
      ne_eq, not_false_eq_true, and_self, ↓reduceIte]
    exact congrArg some (native_g_body register state message mem)
  · simp only [RV.Delegation.blakeG, stateAligned, messageAligned, messageFits, separate, byte,
      true_and, and_self, ↓reduceIte]
    exact congrArg some (native_g_body register state message mem)


end Airbender.Blake2G.Proofs
