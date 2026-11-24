module
public import Proven.Blake2G.NativeControl

@[expose] public section
namespace Airbender.Blake2G.Proofs
set_option warningAsError true
open Arithmetic
set_option backward.isDefEq.respectTransparency false

/-- The RV G effect accepts aligned block bases and implements the native byte behavior. -/
theorem native_g_effect (register : Fin 256) (state message : RV.Word) (mem : RV.Word → BitVec 8)
    (stateAligned : state.toNat % 64 = 0) (messageAligned : message.toNat % 64 = 0)
    (messageFits : message.toNat + 64 ≤ RV.RAM_END) :
    RV.Delegation.blakeG state message (BitVec.ofNat 32 register.val) mem =
      some (⟨RV.writesAt state (RV.gStep (RV.readWords mem message 16) (nativeIndex register)
          (RV.readWords mem state 16)), 12,
        (Control.step ⟨register, true⟩).register.toBitVec⟩ : RV.Effect) := by
  have byte : (BitVec.ofNat 32 register.val).toNat = register.val := by
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show register.val < 2 ^ 32 by have := register.isLt; omega)]
  have bits := native_control_bits register
  simp only [RV.Delegation.blakeG, byte, stateAligned, messageAligned, messageFits,
    register.isLt, and_self, ↓reduceIte, bits.1]
  apply congrArg some
  change (⟨RV.writesAt state (RV.gStep (RV.readWords mem message 16) (nativeIndex register)
      (RV.readWords mem state 16)), 12, _⟩ : RV.Effect) = _
  exact congrArg (RV.Effect.mk _ 12) bits.2



end Airbender.Blake2G.Proofs
