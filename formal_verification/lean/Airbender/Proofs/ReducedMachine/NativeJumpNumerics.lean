import Airbender.Proofs.ReducedMachine.NativeJumpFields
import Airbender.Proofs.ReducedMachine.NativeBranchCleanup
import Airbender.Proofs.ReducedMachine.NativeArithmeticResult
import Airbender.Review.Circuits.ReducedMachine.PC

namespace Airbender.ReducedMachine.NativeJumpNumericalProofs
open Native Arithmetic Verification
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

/-- These are the exact shared native scalar/carry fields, independent of the
    arithmetic-profile masks. New jump equations provide their interpretation. -/
theorem raw_bounds {setup : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints setup)) :
    (jumpRawTargetWord w).Bounded := by
  simpa [jumpRawTargetWord,Word.Bounded,limbBase] using NativeArithmeticResultProofs.scalar_bounds holds

/-- Internal RV32 addition: original public decoding/initialization must derive
    these input bounds before an original architectural jump result is claimed. -/
theorem raw_result {setup : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints setup))
    (jal : Bool) (mask : w 12 = (jumpMask jal : ZMod mersenne31Modulus))
    (base : (jumpBaseWord w).Bounded) (immediate : (jumpImmediateWord w).Bounded) :
    (jumpRawTargetWord w).toBitVec = (jumpBaseWord w).toBitVec+(jumpImmediateWord w).toBitVec := by
  have equations := NativeJumpFieldProofs.limb_equations holds jal mask
  have carries := NativeArithmeticResultProofs.carries holds
  have sum := Word.add_of_limbs (p := mersenne31Modulus) (by decide)
    (left := jumpBaseWord w) (right := jumpImmediateWord w) (immediate := ⟨0,0⟩)
    (output := jumpRawTargetWord w) (carry := (w 95).val) (wrap := (w 63).val)
    base immediate (by constructor <;> decide) (raw_bounds holds)
    (le_trans carries.1 (by decide)) (le_trans carries.2 (by decide))
    (by simpa [jumpBaseWord,jumpImmediateWord,jumpRawTargetWord,ZMod.natCast_zmod_val] using equations.1)
    (by simpa [jumpBaseWord,jumpImmediateWord,jumpRawTargetWord,ZMod.natCast_zmod_val] using equations.2)
  simpa [Word.toBitVec,Word.value] using sum

/-- The actual jump query instantiates the already certified exact native tag17
    region. No old split table identity, input bound or regenerated data is used. -/
theorem cleanup {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints NativeFixed.table))
    (jal : Bool) (mask : w 12 = (jumpMask jal : ZMod mersenne31Modulus)) :
    (w 61).val < 65536 ∧ w 64 = ((w 61).val / 2 % 2 : Nat) ∧
      w 65 = (4*((w 61).val / 4) : Nat) := by
  have member := NativeQueryProofs.dynamic_queries holds 0
  change (NativeFixed.table (p := mersenne31Modulus)).Contains #[] #v[w 100,w 101,w 102,w 103] at member
  rw [(NativeJumpFieldProofs.query_fields holds jal mask).1] at member
  exact NativeBranchCleanupProofs.values member

/-- Active native jumps reject raw target bit1. JALR low-bit cleaning and the
    original JAL even-offset connection are separate architectural obligations. -/
theorem raw_bit1 {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints NativeFixed.table))
    (jal : Bool) (mask : w 12 = (jumpMask jal : ZMod mersenne31Modulus)) : (w 61).val / 2 % 2 = 0 := by
  have zero := NativeJumpFieldProofs.misaligned_rejected holds jal mask
  have bit := (cleanup holds jal mask).2.1
  rw [zero] at bit
  have value := congrArg ZMod.val bit
  rw [ZMod.val_natCast_of_lt (by have := Nat.mod_lt ((w 61).val / 2) (by decide : 0 < 2); change _ < 2147483647; omega)] at value
  simpa using value.symm

/-- Native scalar checks, exact cleanup output and actual PC selection derive
    canonical four-byte final PC bounds without supplied source/target ranges. -/
theorem final_bounds {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints NativeFixed.table))
    (jal : Bool) (mask : w 12 = (jumpMask jal : ZMod mersenne31Modulus)) :
    (finalPCWord w).Bounded ∧ (finalPCWord w).toBitVec.toNat % 4 = 0 := by
  have actual := cleanup holds jal mask
  have lowBound : 4*((w 61).val / 4) < 65536 := by omega
  have fieldBound : 4*((w 61).val / 4) < mersenne31Modulus := by change _ < 2147483647; omega
  have low := congrArg ZMod.val actual.2.2
  rw [ZMod.val_natCast_of_lt fieldBound] at low
  have high := (raw_bounds holds).2
  have selected := NativeJumpFieldProofs.pc holds jal mask
  have lo := congrArg (fun v : Vector (ZMod mersenne31Modulus) 2 => v[0]) selected
  have hi := congrArg (fun v : Vector (ZMod mersenne31Modulus) 2 => v[1]) selected
  have lowSelected : w 13 = w 65 := by simpa [finalPC,importedConstraintsTraceColumns] using lo
  have highSelected : w 14 = w 62 := by simpa [finalPC,importedConstraintsTraceColumns] using hi
  have bounds : (finalPCWord w).Bounded := by
    change (w 13).val < 65536 ∧ (w 14).val < 65536
    rw [lowSelected,highSelected,low]
    exact ⟨lowBound,high⟩
  refine ⟨bounds,?_⟩
  rw [Word.toBitVec_toNat bounds]
  change ((w 13).val+65536*(w 14).val)%4 = 0
  rw [lowSelected,low]
  omega

end Airbender.ReducedMachine.NativeJumpNumericalProofs
