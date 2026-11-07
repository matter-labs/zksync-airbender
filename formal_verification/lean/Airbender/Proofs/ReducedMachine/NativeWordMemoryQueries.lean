import Airbender.Proofs.ReducedMachine.NativeWordMemoryFields

namespace Airbender.ReducedMachine.NativeWordMemoryQueryProofs
open Native Verification NativeWordMemorySelectorProofs
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

/-- Actual load separator/ROM and store offset/separator queries. Both load
    queries remain active for RAM accesses; no ROM-value answer is assumed. -/
theorem fields {setup : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints setup))
    (store : Bool) (mask : w 12 = (wordMemoryMask store : ZMod mersenne31Modulus)) :
    #v[w 100,w 101,w 102,w 103] =
      (if store then #v[w 61,w 64,w 65,18] else #v[w 62,w 64,w 65,23]) ∧
    #v[w 104,w 105,w 106,w 107] =
      (if store then #v[w 62,w 66,w 67,23] else #v[w 61+65536*w 65,w 66,w 67,24]) ∧
    w 111 = 0 ∧ w 115 = 0 := by
  have e82 := assertion_of_holds holds ⟨82,by change 82 < 117; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at e82
  have e83 := assertion_of_holds holds ⟨83,by change 83 < 117; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at e83
  have e84 := assertion_of_holds holds ⟨84,by change 84 < 117; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at e84
  have e85 := assertion_of_holds holds ⟨85,by change 85 < 117; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at e85
  have e86 := assertion_of_holds holds ⟨86,by change 86 < 117; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at e86
  have e87 := assertion_of_holds holds ⟨87,by change 87 < 117; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at e87
  have e88 := assertion_of_holds holds ⟨88,by change 88 < 117; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at e88
  have e89 := assertion_of_holds holds ⟨89,by change 89 < 117; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at e89
  have e93 := assertion_of_holds holds ⟨93,by change 93 < 117; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at e93
  have e97 := assertion_of_holds holds ⟨97,by change 97 < 117; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at e97
  have f22 : w 22 = 0 := by cases store <;> simpa [bit] using flags holds _ mask ⟨5,by decide⟩
  have f23 : w 23 = 0 := by cases store <;> simpa [bit] using flags holds _ mask ⟨6,by decide⟩
  have f24 : w 24 = 0 := by cases store <;> simpa [bit] using flags holds _ mask ⟨7,by decide⟩
  have f25 : w 25 = 0 := by cases store <;> simpa [bit] using flags holds _ mask ⟨8,by decide⟩
  have f29 : w 29 = 0 := by cases store <;> simpa [bit] using flags holds _ mask ⟨12,by decide⟩
  cases store
  · have f27 : w 27 = 1 := by simpa [bit] using flags holds false mask ⟨10,by decide⟩
    have f31 : w 31 = 0 := by simpa [bit] using flags holds false mask ⟨14,by decide⟩
    simp [f22,f23,f24,f25,f27,f29,f31] at e82 e83 e84 e85 e86 e87 e88 e89 e93 e97
    have q100 : w 100 = w 62 := by linear_combination -e82
    have q101 : w 101 = w 64 := by linear_combination -e83
    have q102 : w 102 = w 65 := by linear_combination -e84
    have q103 : w 103 = 23 := by linear_combination -e85
    have q104 : w 104 = w 61+65536*w 65 := by linear_combination -e86
    have q105 : w 105 = w 66 := by linear_combination -e87
    have q106 : w 106 = w 67 := by linear_combination -e88
    have q107 : w 107 = 24 := by linear_combination -e89
    simp [q100,q101,q102,q103,q104,q105,q106,q107,e93,e97]
  · have f27 : w 27 = 0 := by simpa [bit] using flags holds true mask ⟨10,by decide⟩
    have f31 : w 31 = 1 := by simpa [bit] using flags holds true mask ⟨14,by decide⟩
    simp [f22,f23,f24,f25,f27,f29,f31] at e82 e83 e84 e85 e86 e87 e88 e89 e93 e97
    have q100 : w 100 = w 61 := by linear_combination -e82
    have q101 : w 101 = w 64 := by linear_combination -e83
    have q102 : w 102 = w 65 := by linear_combination -e84
    have q103 : w 103 = 18 := by linear_combination -e85
    have q104 : w 104 = w 62 := by linear_combination -e86
    have q105 : w 105 = w 66 := by linear_combination -e87
    have q106 : w 106 = w 67 := by linear_combination -e88
    have q107 : w 107 = 23 := by linear_combination -e89
    simp [q100,q101,q102,q103,q104,q105,q106,q107,e93,e97]

end Airbender.ReducedMachine.NativeWordMemoryQueryProofs
