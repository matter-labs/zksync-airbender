import Airbender.Proofs.ReducedMachine.NativeJumpFields
import Airbender.Proofs.ReducedMachine.NativeJumpNumerics

namespace Airbender.ReducedMachine.Native
open Verification
set_option autoImplicit false

/-- Actual native jump routing; decoded mask and JAL/JALR identity remain
    explicit until original public decoding. This is not original execution. -/
theorem jump_routing {setup : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints setup))
    (jal : Bool) (mask : w 12 = (jumpMask jal : ZMod mersenne31Modulus)) : JumpRouting w jal := by
  have limbs := NativeJumpFieldProofs.limb_equations holds jal mask
  have write := NativeJumpFieldProofs.write holds jal mask
  exact ⟨NativeJumpFieldProofs.source holds jal mask,NativeJumpFieldProofs.source_port holds jal mask,
    NativeJumpFieldProofs.base holds jal mask,limbs.1,limbs.2,
    (NativeJumpFieldProofs.query_fields holds jal mask).1,NativeJumpFieldProofs.misaligned_rejected holds jal mask,
    NativeJumpFieldProofs.candidate holds jal mask,write.1,write.2,NativeJumpFieldProofs.pc holds jal mask⟩

/-- Exact native cleanup and PC selection derive output bounds/alignment and
    reject raw bit1, without source/PC/target-bound or expected-result premises. -/
theorem jump_pc_bounds {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints NativeFixed.table))
    (jal : Bool) (mask : w 12 = (jumpMask jal : ZMod mersenne31Modulus)) :
    (finalPCWord w).Bounded ∧ (finalPCWord w).toBitVec.toNat % 4 = 0 ∧ (w 61).val / 2 % 2 = 0 :=
  ⟨(NativeJumpNumericalProofs.final_bounds holds jal mask).1,
    (NativeJumpNumericalProofs.final_bounds holds jal mask).2,NativeJumpNumericalProofs.raw_bit1 holds jal mask⟩

end Airbender.ReducedMachine.Native
