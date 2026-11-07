import Airbender.Proofs.ReducedMachine.NativeWordMemoryAccess
import Airbender.Proofs.ReducedMachine.NativeArithmeticResult

namespace Airbender.ReducedMachine.NativeWordMemoryNumericalProofs
open Native Arithmetic Verification
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

theorem address_bounds {setup : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints setup)) : (wordMemoryAddressWord w).Bounded := by
  simpa [wordMemoryAddressWord,Word.Bounded,limbBase] using NativeArithmeticResultProofs.scalar_bounds holds

/-- Internal effective-address addition only. Original public decoding and
    initialized source history must discharge both input bounds. -/
theorem address_result {setup : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints setup))
    (store : Bool) (mask : w 12 = (wordMemoryMask store : ZMod mersenne31Modulus))
    (source : (sourceWord w).Bounded) (immediate : (wordMemoryImmediateWord w).Bounded) :
    (wordMemoryAddressWord w).toBitVec = (sourceWord w).toBitVec+(wordMemoryImmediateWord w).toBitVec := by
  have equations := NativeWordMemoryAccessProofs.limb_equations holds store mask
  have carries := NativeArithmeticResultProofs.carries holds
  have sum := Word.add_of_limbs (p := mersenne31Modulus) (by decide)
    (left := sourceWord w) (right := wordMemoryImmediateWord w) (immediate := ⟨0,0⟩)
    (output := wordMemoryAddressWord w) (carry := (w 95).val) (wrap := (w 63).val)
    source immediate (by constructor <;> decide) (address_bounds holds)
    (le_trans carries.1 (by decide)) (le_trans carries.2 (by decide))
    (by simpa [sourceWord,source1,NativePortProofs.source_columns,Trace.WordColumns.evaluate,wordMemoryImmediateWord,wordMemoryAddressWord,ZMod.natCast_zmod_val] using equations.1)
    (by simpa [sourceWord,source1,NativePortProofs.source_columns,Trace.WordColumns.evaluate,wordMemoryImmediateWord,wordMemoryAddressWord,ZMod.natCast_zmod_val] using equations.2)
  simpa [Word.toBitVec,Word.value] using sum

end Airbender.ReducedMachine.NativeWordMemoryNumericalProofs
