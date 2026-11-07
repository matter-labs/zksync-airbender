import Airbender.Proofs.ReducedMachine.NativeWordMemoryFields

namespace Airbender.ReducedMachine.NativeWordMemoryAccessProofs
open Native Verification NativeWordMemorySelectorProofs
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

theorem load_access {setup : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints setup))
    (mask : w 12 = (wordMemoryMask false : ZMod mersenne31Modulus)) : WordLoadAccess w := by
  have e54 := assertion_of_holds holds ⟨54,by change 54 < 117; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at e54
  have e55 := assertion_of_holds holds ⟨55,by change 55 < 117; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at e55
  have e56 := assertion_of_holds holds ⟨56,by change 56 < 117; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at e56
  have e57 := assertion_of_holds holds ⟨57,by change 57 < 117; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at e57
  have e58 := assertion_of_holds holds ⟨58,by change 58 < 117; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at e58
  have e59 := assertion_of_holds holds ⟨59,by change 59 < 117; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at e59
  have e98 := assertion_of_holds holds ⟨98,by change 98 < 117; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at e98
  have e99 := assertion_of_holds holds ⟨99,by change 99 < 117; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at e99
  have e100 := assertion_of_holds holds ⟨100,by change 100 < 117; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at e100
  have e101 := assertion_of_holds holds ⟨101,by change 101 < 117; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at e101
  have e102 := assertion_of_holds holds ⟨102,by change 102 < 117; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at e102
  have e103 := assertion_of_holds holds ⟨103,by change 103 < 117; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at e103
  have e106 := assertion_of_holds holds ⟨106,by change 106 < 117; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at e106
  have e107 := assertion_of_holds holds ⟨107,by change 107 < 117; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at e107
  have f17 : w 17 = 1 := by simpa [bit] using flags holds false mask ⟨0,by decide⟩
  have f20 : w 20 = 0 := by simpa [bit] using flags holds false mask ⟨3,by decide⟩
  have f21 : w 21 = 0 := by simpa [bit] using flags holds false mask ⟨4,by decide⟩
  have f22 : w 22 = 0 := by simpa [bit] using flags holds false mask ⟨5,by decide⟩
  have f23 : w 23 = 0 := by simpa [bit] using flags holds false mask ⟨6,by decide⟩
  have f24 : w 24 = 0 := by simpa [bit] using flags holds false mask ⟨7,by decide⟩
  have f25 : w 25 = 0 := by simpa [bit] using flags holds false mask ⟨8,by decide⟩
  have f26 : w 26 = 0 := by simpa [bit] using flags holds false mask ⟨9,by decide⟩
  have f27 : w 27 = 1 := by simpa [bit] using flags holds false mask ⟨10,by decide⟩
  have f28 : w 28 = 0 := by simpa [bit] using flags holds false mask ⟨11,by decide⟩
  have f29 : w 29 = 0 := by simpa [bit] using flags holds false mask ⟨12,by decide⟩
  have f30 : w 30 = 0 := by simpa [bit] using flags holds false mask ⟨13,by decide⟩
  have f31 : w 31 = 0 := by simpa [bit] using flags holds false mask ⟨14,by decide⟩
  simp [f27] at e54 e55
  have rom : w 86 = 1-w 64 := by linear_combination -e54
  have ram : w 87 = w 64 := by linear_combination -e55
  simp [rom,ram] at e56 e57 e58 e59
  have addressLo : w 39 = w 61 := by linear_combination -e56-e58
  have addressHi : w 40 = w 62 := by linear_combination -e57-e59
  simp [f20,f21,f22,f23,f24,f25,f26,f28,f29,f30,rom,ram] at e98 e99
  have candidateLo : w 116 = (1-w 64)*w 66+w 64*w 37 := by linear_combination -e98
  have candidateHi : w 117 = (1-w 64)*w 67+w 64*w 38 := by linear_combination -e99
  simp [f17] at e102 e103 e106 e107
  have rd : w 45 = w 7 := by linear_combination -e102
  have lowWrite : w 43 = (1-w 8)*w 116 := by linear_combination -e106-e100
  have highWrite : w 44 = (1-w 8)*w 117 := by linear_combination -e107-e101
  exact ⟨by simp [addressLo,addressHi],rom,ram,by simp [candidateLo,candidateHi],by simp [rd,e103],by simp [lowWrite,highWrite]⟩

theorem store_access {setup : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints setup))
    (mask : w 12 = (wordMemoryMask true : ZMod mersenne31Modulus)) : WordStoreAccess w := by
  have e60 := assertion_of_holds holds ⟨60,by change 60 < 117; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at e60
  have e61 := assertion_of_holds holds ⟨61,by change 61 < 117; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at e61
  have e62 := assertion_of_holds holds ⟨62,by change 62 < 117; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at e62
  have e63 := assertion_of_holds holds ⟨63,by change 63 < 117; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at e63
  have e64 := assertion_of_holds holds ⟨64,by change 64 < 117; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at e64
  have e65 := assertion_of_holds holds ⟨65,by change 65 < 117; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at e65
  have e66 := assertion_of_holds holds ⟨66,by change 66 < 117; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at e66
  have e67 := assertion_of_holds holds ⟨67,by change 67 < 117; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at e67
  have f27 : w 27 = 0 := by simpa [bit] using flags holds true mask ⟨10,by decide⟩
  have f31 : w 31 = 1 := by simpa [bit] using flags holds true mask ⟨14,by decide⟩
  simp [f27] at e60 e61
  simp [f31] at e62 e63 e64 e65 e66 e67
  have operand := (NativeWordMemoryFieldProofs.routing holds true mask).operand
  have lowOperand : w 47 = w 37 := by simpa using congrArg (fun q : Vector (ZMod mersenne31Modulus) 2 => q[0]) operand
  have highOperand : w 48 = w 38 := by simpa using congrArg (fun q : Vector (ZMod mersenne31Modulus) 2 => q[1]) operand
  have rs2 : w 39 = w 6 := by linear_combination -e60
  have addressLo : w 45 = w 61 := by linear_combination -e64
  have addressHi : w 46 = w 62 := by linear_combination -e65
  have lowWrite : w 43 = w 37 := by linear_combination -e66+lowOperand
  have highWrite : w 44 = w 38 := by linear_combination -e67+highOperand
  exact ⟨by simp [rs2,e61],by simp [addressLo,addressHi],by simp [lowWrite,highWrite],e62,by linear_combination -e63⟩

theorem limb_equations {setup : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints setup))
    (store : Bool) (mask : w 12 = (wordMemoryMask store : ZMod mersenne31Modulus)) :
    w 35+w 9 = w 61+65536*w 95 ∧ w 95+w 36+w 10 = w 62+65536*w 63 := by
  have e74 := assertion_of_holds holds ⟨74,by change 74 < 117; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at e74
  have e75 := assertion_of_holds holds ⟨75,by change 75 < 117; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at e75
  have f20 : w 20 = 0 := by cases store <;> simpa [bit] using flags holds _ mask ⟨3,by decide⟩
  have f21 : w 21 = 0 := by cases store <;> simpa [bit] using flags holds _ mask ⟨4,by decide⟩
  have f23 : w 23 = 0 := by cases store <;> simpa [bit] using flags holds _ mask ⟨6,by decide⟩
  have f25 : w 25 = 0 := by cases store <;> simpa [bit] using flags holds _ mask ⟨8,by decide⟩
  have f28 : w 28 = 0 := by cases store <;> simpa [bit] using flags holds _ mask ⟨11,by decide⟩
  have f30 : w 30 = 0 := by cases store <;> simpa [bit] using flags holds _ mask ⟨13,by decide⟩
  cases store
  · have f27 : w 27 = 1 := by simpa [bit] using flags holds false mask ⟨10,by decide⟩
    have f31 : w 31 = 0 := by simpa [bit] using flags holds false mask ⟨14,by decide⟩
    simp [f20,f21,f23,f25,f27,f28,f30,f31] at e74 e75
    exact ⟨by linear_combination e74,by linear_combination e75⟩
  · have f27 : w 27 = 0 := by simpa [bit] using flags holds true mask ⟨10,by decide⟩
    have f31 : w 31 = 1 := by simpa [bit] using flags holds true mask ⟨14,by decide⟩
    simp [f20,f21,f23,f25,f27,f28,f30,f31] at e74 e75
    exact ⟨by linear_combination e74,by linear_combination e75⟩

theorem pc {setup : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints setup))
    (store : Bool) (mask : w 12 = (wordMemoryMask store : ZMod mersenne31Modulus)) :
    #v[w 13,w 14] = #v[w 49,w 50] := by
  have e110 := assertion_of_holds holds ⟨110,by change 110 < 117; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at e110
  have e111 := assertion_of_holds holds ⟨111,by change 111 < 117; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at e111
  have f20 : w 20 = 0 := by cases store <;> simpa [bit] using flags holds _ mask ⟨3,by decide⟩
  have f21 : w 21 = 0 := by cases store <;> simpa [bit] using flags holds _ mask ⟨4,by decide⟩
  have f22 : w 22 = 0 := by cases store <;> simpa [bit] using flags holds _ mask ⟨5,by decide⟩
  have f23 : w 23 = 0 := by cases store <;> simpa [bit] using flags holds _ mask ⟨6,by decide⟩
  have f24 : w 24 = 0 := by cases store <;> simpa [bit] using flags holds _ mask ⟨7,by decide⟩
  have f25 : w 25 = 0 := by cases store <;> simpa [bit] using flags holds _ mask ⟨8,by decide⟩
  have f26 : w 26 = 0 := by cases store <;> simpa [bit] using flags holds _ mask ⟨9,by decide⟩
  have f28 : w 28 = 0 := by cases store <;> simpa [bit] using flags holds _ mask ⟨11,by decide⟩
  have f29 : w 29 = 0 := by cases store <;> simpa [bit] using flags holds _ mask ⟨12,by decide⟩
  have f30 : w 30 = 0 := by cases store <;> simpa [bit] using flags holds _ mask ⟨13,by decide⟩
  cases store
  · have f27 : w 27 = 1 := by simpa [bit] using flags holds false mask ⟨10,by decide⟩
    have f31 : w 31 = 0 := by simpa [bit] using flags holds false mask ⟨14,by decide⟩
    simp [f20,f21,f22,f23,f24,f25,f26,f27,f28,f29,f30,f31] at e110 e111
    have lo : w 13 = w 49 := by linear_combination -e110
    have hi : w 14 = w 50 := by linear_combination -e111
    simp [lo,hi]
  · have f27 : w 27 = 0 := by simpa [bit] using flags holds true mask ⟨10,by decide⟩
    have f31 : w 31 = 1 := by simpa [bit] using flags holds true mask ⟨14,by decide⟩
    simp [f20,f21,f22,f23,f24,f25,f26,f27,f28,f29,f30,f31] at e110 e111
    have lo : w 13 = w 49 := by linear_combination -e110
    have hi : w 14 = w 50 := by linear_combination -e111
    simp [lo,hi]

end Airbender.ReducedMachine.NativeWordMemoryAccessProofs
