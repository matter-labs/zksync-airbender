import Airbender.Proofs.ReducedMachine.NativeWordMemorySelectors
import Airbender.Proofs.ReducedMachine.NativeQueries

namespace Airbender.ReducedMachine.NativeWordMemoryFieldProofs
open Native Verification NativeWordMemorySelectorProofs
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

/-- Exact native equations32/33/113/114 derive the change of port spaces.
    In particular memory accesses are not silently treated as GPR events. -/
theorem routing {fixed : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints fixed))
    (store : Bool) (mask : w 12 = (wordMemoryMask store : ZMod mersenne31Modulus)) :
    WordMemoryRouting w store := by
  have e32 := assertion_of_holds holds ⟨32,by change 32 < 117; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at e32
  have e33 := assertion_of_holds holds ⟨33,by change 33 < 117; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at e33
  have e113 := assertion_of_holds holds ⟨113,by change 113 < 117; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at e113
  have e114 := assertion_of_holds holds ⟨114,by change 114 < 117; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at e114
  cases store
  · have f18 : w 18 = 0 := by simpa [bit] using flags holds false mask ⟨1,by decide⟩
    have f27 : w 27 = 1 := by simpa [bit] using flags holds false mask ⟨10,by decide⟩
    have f31 : w 31 = 0 := by simpa [bit] using flags holds false mask ⟨14,by decide⟩
    simp [f18] at e32 e33
    simp [f27] at e113
    simp [f31] at e114
    have lo : w 47 = w 9 := by linear_combination -e32
    have hi : w 48 = w 10 := by linear_combination -e33
    exact ⟨by simp [lo,hi],by simpa using e113,by change w 89 = 1; linear_combination -e114⟩
  · have f18 : w 18 = 1 := by simpa [bit] using flags holds true mask ⟨1,by decide⟩
    have f27 : w 27 = 0 := by simpa [bit] using flags holds true mask ⟨10,by decide⟩
    have f31 : w 31 = 1 := by simpa [bit] using flags holds true mask ⟨14,by decide⟩
    simp [f18] at e32 e33
    simp [f27] at e113
    simp [f31] at e114
    have lo : w 47 = w 37 := by linear_combination -e32
    have hi : w 48 = w 38 := by linear_combination -e33
    exact ⟨by simp [lo,hi],by change w 88 = 1; linear_combination -e113,by simpa using e114⟩

end Airbender.ReducedMachine.NativeWordMemoryFieldProofs
