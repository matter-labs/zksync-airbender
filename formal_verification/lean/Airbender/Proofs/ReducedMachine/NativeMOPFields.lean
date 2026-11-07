import Airbender.Proofs.ReducedMachine.NativeMOPSelectors
import Airbender.Proofs.ReducedMachine.NativePorts

namespace Airbender.ReducedMachine.NativeMOPFieldProofs
open Verification Native NativeMOPSelectorProofs
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

theorem source {setup : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints setup))
    (mode : MOPMode) (mask : w 12 = (mode.mask : ZMod mersenne31Modulus)) :
    source2 w = if mode.useRegister then #v[w 37,w 38] else #v[w 9,w 10] := by
  have e32 := assertion_of_holds holds ⟨32,by change 32 < 117; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at e32
  have e33 := assertion_of_holds holds ⟨33,by change 33 < 117; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at e33
  have f18 := flags holds mode mask ⟨1,by decide⟩
  have lo : w 47 = if mode.useRegister then w 37 else w 9 := by
    cases mode <;> simp [bit,MOPMode.useRegister] at f18 ⊢
    all_goals simp [f18] at e32; linear_combination -e32
  have hi : w 48 = if mode.useRegister then w 38 else w 10 := by
    cases mode <;> simp [bit,MOPMode.useRegister] at f18 ⊢
    all_goals simp [f18] at e33; linear_combination -e33
  cases mode <;> simp_all [source2,MOPMode.useRegister]


theorem source_port {setup : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints setup))
    (mode : MOPMode) (mask : w 12 = (mode.mask : ZMod mersenne31Modulus)) : w 39 = w 6 ∧ w 40 = 0 ∧ w 88 = 1 := by
  have e60 := assertion_of_holds holds ⟨60,by change 60 < 117; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at e60
  have e61 := assertion_of_holds holds ⟨61,by change 61 < 117; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at e61
  have e113 := assertion_of_holds holds ⟨113,by change 113 < 117; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at e113
  have f27 := flags holds mode mask ⟨10,by decide⟩
  have off : w 27 = 0 := by cases mode <;> simpa [bit] using f27
  simp [off] at e60 e61 e113
  exact ⟨by linear_combination -e60,e61,by linear_combination -e113⟩

theorem tags {setup : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints setup))
    (mode : MOPMode) (mask : w 12 = (mode.mask : ZMod mersenne31Modulus)) : lookupSelectors w = #v[0,0,0,0] := by
  have e85 := assertion_of_holds holds ⟨85,by change 85 < 117; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at e85
  have e89 := assertion_of_holds holds ⟨89,by change 89 < 117; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at e89
  have e93 := assertion_of_holds holds ⟨93,by change 93 < 117; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at e93
  have e97 := assertion_of_holds holds ⟨97,by change 97 < 117; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at e97
  have f22 := flags holds mode mask ⟨5,by decide⟩
  have f23 := flags holds mode mask ⟨6,by decide⟩
  have f24 := flags holds mode mask ⟨7,by decide⟩
  have f25 := flags holds mode mask ⟨8,by decide⟩
  have f27 := flags holds mode mask ⟨10,by decide⟩
  have f29 := flags holds mode mask ⟨12,by decide⟩
  have f31 := flags holds mode mask ⟨14,by decide⟩
  cases mode
  all_goals
    simp only [bit] at f22 f23 f24 f25 f27 f29 f31
    simp [f22,f23,f24,f25,f27,f29,f31] at e85 e89 e93 e97
    simp [lookupSelectors,e85,e89,e93,e97]

theorem candidate {setup : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints setup))
    (mode : MOPMode) (mask : w 12 = (mode.mask : ZMod mersenne31Modulus)) :
    mopCandidate w = #v[w 61,w 62] := by
  have e54 := assertion_of_holds holds ⟨54,by change 54 < 117; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at e54
  have e55 := assertion_of_holds holds ⟨55,by change 55 < 117; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at e55
  have e98 := assertion_of_holds holds ⟨98,by change 98 < 117; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at e98
  have e99 := assertion_of_holds holds ⟨99,by change 99 < 117; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at e99
  have f20 := flags holds mode mask ⟨3,by decide⟩
  have f21 := flags holds mode mask ⟨4,by decide⟩
  have f22 := flags holds mode mask ⟨5,by decide⟩
  have f23 := flags holds mode mask ⟨6,by decide⟩
  have f24 := flags holds mode mask ⟨7,by decide⟩
  have f25 := flags holds mode mask ⟨8,by decide⟩
  have f26 := flags holds mode mask ⟨9,by decide⟩
  have f27 := flags holds mode mask ⟨10,by decide⟩
  have f28 := flags holds mode mask ⟨11,by decide⟩
  have f29 := flags holds mode mask ⟨12,by decide⟩
  have f30 := flags holds mode mask ⟨13,by decide⟩
  have f31 := flags holds mode mask ⟨14,by decide⟩
  cases mode
  all_goals
    simp only [bit] at f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31
    simp [f27] at e54 e55
    simp [f20,f21,f22,f23,f24,f25,f26,f28,f29,f30,e54,e55] at e98 e99
    have low : w 116 = w 61 := by linear_combination -e98
    have high : w 117 = w 62 := by linear_combination -e99
    simp [mopCandidate,low,high]

theorem write {setup : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints setup))
    (mode : MOPMode) (mask : w 12 = (mode.mask : ZMod mersenne31Modulus)) :
    rdPort.address.code w = Nat.pair 0 (Nat.pair (rdIndex w).val 0) ∧
    rdWrite w = (mopCandidate w).map (fun value => (1 - rdZeroFlag w) * value) := by
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
  have e114 := assertion_of_holds holds ⟨114,by change 114 < 117; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at e114
  have f17 := flags holds mode mask ⟨0,by decide⟩
  have f31 := flags holds mode mask ⟨14,by decide⟩
  have update : w 17 = 1 := by cases mode <;> simpa [bit] using f17
  have off : w 31 = 0 := by cases mode <;> simpa [bit] using f31
  simp [update,off] at e102 e103 e106 e107 e114
  have address : w 45 = w 7 := by linear_combination -e102
  have space : w 89 = 1 := by linear_combination -e114
  have lo : w 43 = (1 - w 8) * w 116 := by linear_combination -e106 - e100
  have hi : w 44 = (1 - w 8) * w 117 := by linear_combination -e107 - e101
  constructor
  · simp [NativePortProofs.address_columns,Trace.MemoryAddress.code,Trace.pairCode,space,address,e103,rdIndex,
      importedConstraintsDecoderColumns]
  · simp [rdWrite,NativePortProofs.write_columns,Trace.WordColumns.evaluate,
      mopCandidate,rdZeroFlag,importedConstraintsDecoderColumns,lo,hi]

theorem pc {setup : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints setup))
    (mode : MOPMode) (mask : w 12 = (mode.mask : ZMod mersenne31Modulus)) : finalPC w = defaultPC w := by
  have e110 := assertion_of_holds holds ⟨110,by change 110 < 117; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at e110
  have e111 := assertion_of_holds holds ⟨111,by change 111 < 117; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at e111
  have f20 := flags holds mode mask ⟨3,by decide⟩
  have f21 := flags holds mode mask ⟨4,by decide⟩
  have f22 := flags holds mode mask ⟨5,by decide⟩
  have f23 := flags holds mode mask ⟨6,by decide⟩
  have f24 := flags holds mode mask ⟨7,by decide⟩
  have f25 := flags holds mode mask ⟨8,by decide⟩
  have f26 := flags holds mode mask ⟨9,by decide⟩
  have f27 := flags holds mode mask ⟨10,by decide⟩
  have f28 := flags holds mode mask ⟨11,by decide⟩
  have f29 := flags holds mode mask ⟨12,by decide⟩
  have f30 := flags holds mode mask ⟨13,by decide⟩
  have f31 := flags holds mode mask ⟨14,by decide⟩
  cases mode
  all_goals
    simp only [bit] at f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31
    simp [f20,f21,f22,f23,f24,f25,f26,f27,f28,f29,f30,f31] at e110 e111
    have lo : w 13 = w 49 := by linear_combination -e110
    have hi : w 14 = w 50 := by linear_combination -e111
    simp [finalPC,defaultPC,importedConstraintsTraceColumns,lo,hi]

theorem field_relation {setup : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints setup))
    (mode : MOPMode) (mask : w 12 = (mode.mask : ZMod mersenne31Modulus)) :
    w 61+65536*w 62 = mode.field (w 35+65536*w 36) (w 37+65536*w 38) := by
  have e32 := assertion_of_holds holds ⟨32,by change 32 < 117; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at e32
  have e33 := assertion_of_holds holds ⟨33,by change 33 < 117; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at e33
  have e49 := assertion_of_holds holds ⟨49,by change 49 < 117; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at e49
  have e50 := assertion_of_holds holds ⟨50,by change 50 < 117; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at e50
  have e51 := assertion_of_holds holds ⟨51,by change 51 < 117; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at e51
  have e52 := assertion_of_holds holds ⟨52,by change 52 < 117; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at e52
  have f18 := flags holds mode mask ⟨1,by decide⟩
  have f28 := flags holds mode mask ⟨11,by decide⟩
  have f32 := flags holds mode mask ⟨15,by decide⟩
  have f33 := flags holds mode mask ⟨16,by decide⟩
  have f34 := flags holds mode mask ⟨17,by decide⟩
  have enabled : w 28 = 1 := by cases mode <;> simpa [bit] using f28
  have registers : w 18 = 1 := by cases mode <;> simpa [bit] using f18
  simp [registers] at e32 e33
  have low : w 47 = w 37 := by linear_combination -e32
  have high : w 48 = w 38 := by linear_combination -e33
  simp [low,high] at e49 e50
  have modulus : (4294967294 : ZMod mersenne31Modulus) = 0 := by decide +kernel
  have product : w 83 = (w 35+65536*w 36)*(w 37+65536*w 38) := by
    linear_combination -e49 - (w 38*w 36)*modulus
  simp [enabled] at e51 e52
  have sameLow : w 61 = w 84 := by linear_combination -e51
  have sameHigh : w 62 = w 85 := by linear_combination -e52
  rw [sameLow,sameHigh]
  cases mode
  all_goals
    simp [bit] at f32 f33 f34
    simp [f32,f33,f34,product] at e50
    simp only [MOPMode.field]
    linear_combination -e50

theorem modulus_subtraction {setup : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints setup))
    (mode : MOPMode) (mask : w 12 = (mode.mask : ZMod mersenne31Modulus)) :
    w 69+65535 = w 61+65536*w 95 ∧ w 95+w 70+32767 = w 62+65536*w 63 ∧ w 63 = 1 := by
  have e53 := assertion_of_holds holds ⟨53,by change 53 < 117; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at e53
  have e74 := assertion_of_holds holds ⟨74,by change 74 < 117; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at e74
  have e75 := assertion_of_holds holds ⟨75,by change 75 < 117; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at e75
  have f20 := flags holds mode mask ⟨3,by decide⟩
  have f21 := flags holds mode mask ⟨4,by decide⟩
  have f22 := flags holds mode mask ⟨5,by decide⟩
  have f23 := flags holds mode mask ⟨6,by decide⟩
  have f24 := flags holds mode mask ⟨7,by decide⟩
  have f25 := flags holds mode mask ⟨8,by decide⟩
  have f26 := flags holds mode mask ⟨9,by decide⟩
  have f27 := flags holds mode mask ⟨10,by decide⟩
  have f28 := flags holds mode mask ⟨11,by decide⟩
  have f29 := flags holds mode mask ⟨12,by decide⟩
  have f30 := flags holds mode mask ⟨13,by decide⟩
  have f31 := flags holds mode mask ⟨14,by decide⟩
  cases mode
  all_goals
    simp only [bit] at f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31
    simp [f28] at e53
    simp [f20,f21,f23,f25,f27,f28,f30,f31] at e74 e75
    exact ⟨by linear_combination e74,by linear_combination e75,by linear_combination -e53⟩

end Airbender.ReducedMachine.NativeMOPFieldProofs
