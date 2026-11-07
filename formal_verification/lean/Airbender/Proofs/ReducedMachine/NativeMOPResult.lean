import Airbender.Proofs.ReducedMachine.NativeMOPFields
import Airbender.Proofs.ReducedMachine.NativeArithmeticResult

namespace Airbender.ReducedMachine.NativeMOPResultProofs
open Native Verification Arithmetic
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

/-- Actual native scalar membership bounds the result and subtraction remainder. -/
theorem word_bounds {setup : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints setup)) :
    (mopOutputWord w).Bounded ∧ (⟨(w 69).val,(w 70).val⟩ : Word).Bounded := by
  have result := NativeArithmeticResultProofs.scalar_bounds holds
  have low := range16_bound (lookup_of_holds holds ⟨2,by change 2 < 22; decide⟩)
  have high := range16_bound (lookup_of_holds holds ⟨3,by change 3 < 22; decide⟩)
  refine ⟨result,?_⟩
  simpa [Word.Bounded,Expression.eval,environment,limbBase] using And.intro low high

/-- The ACTUAL final underflow bit and range-checked subtraction remainder
    establish canonical Mersenne31 output, never an assumed result range. -/
theorem canonical {setup : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints setup))
    (mode : MOPMode) (mask : w 12 = (mode.mask : ZMod mersenne31Modulus)) :
    (mopOutputWord w).value < mersenne31Modulus := by
  obtain ⟨low,high,underflow⟩ := NativeMOPFieldProofs.modulus_subtraction holds mode mask
  obtain ⟨result,remainder⟩ := word_bounds holds
  have carries := NativeArithmeticResultProofs.carries holds
  have actual := Word.borrow_iff (p := mersenne31Modulus) (by decide)
    (left := mopOutputWord w) (right := ⟨65535,32767⟩) (remainder := ⟨(w 69).val,(w 70).val⟩)
    (carry := (w 95).val) (borrow := (w 63).val) result (by constructor <;> decide) remainder carries.1 carries.2
    (by simpa [mopOutputWord,ZMod.natCast_zmod_val] using low)
    (by simpa [mopOutputWord,ZMod.natCast_zmod_val] using high)
  have one : (w 63).val = 1 := by rw [underflow]; decide +kernel
  simpa [Word.value,limbBase,mersenne31Modulus] using actual.mp one

/-- Native field arithmetic plus proved canonical output gives its unique
    numerical representative. Sources are actual native words, not Sail reads. -/
theorem result {setup : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints setup))
    (mode : MOPMode) (mask : w 12 = (mode.mask : ZMod mersenne31Modulus)) :
    (mopOutputWord w).value =
      (mode.field ((sourceWord w).value : ZMod mersenne31Modulus)
        ((registerOperandWord w).value : ZMod mersenne31Modulus)).val := by
  have second : importedConstraintsMemoryPorts[1].readValue = Trace.WordColumns.u16 #v[37,38] := rfl
  have field : ((mopOutputWord w).value : ZMod mersenne31Modulus) =
      mode.field ((sourceWord w).value : ZMod mersenne31Modulus)
        ((registerOperandWord w).value : ZMod mersenne31Modulus) := by
    simpa [mopOutputWord,Word.value,limbBase,sourceWord,source1,NativePortProofs.source_columns,
      Trace.WordColumns.evaluate,registerOperandWord,second,ZMod.natCast_zmod_val] using
      NativeMOPFieldProofs.field_relation holds mode mask
  have value := congrArg ZMod.val field
  rw [ZMod.val_natCast_of_lt (canonical holds mode mask)] at value
  exact value

/-- Assemble only actual local native observables; no architectural execution,
    public decoder or compiler/physical correspondence is inferred. -/
theorem effects {setup : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints setup))
    (mode : MOPMode) (mask : w 12 = (mode.mask : ZMod mersenne31Modulus)) : MOPNativeEffects w mode := by
  have source := NativeMOPFieldProofs.source holds mode mask
  have write := NativeMOPFieldProofs.write holds mode mask
  exact ⟨by simpa [MOPMode.useRegister] using source,
    NativeMOPFieldProofs.source_port holds mode mask,NativeMOPFieldProofs.tags holds mode mask,
    NativeMOPFieldProofs.candidate holds mode mask,write.1,write.2,(word_bounds holds).1,
    canonical holds mode mask,result holds mode mask,by
      simpa [finalPC,defaultPC,importedConstraintsTraceColumns] using NativeMOPFieldProofs.pc holds mode mask⟩

end Airbender.ReducedMachine.NativeMOPResultProofs
