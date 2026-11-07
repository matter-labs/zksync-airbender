import Airbender.Proofs.ReducedMachine.NativeJumpSelectors
import Airbender.Proofs.ReducedMachine.NativePorts
import Airbender.Proofs.ReducedMachine.NativeQueries

namespace Airbender.ReducedMachine.NativeJumpFieldProofs
open Verification Native NativeJumpSelectorProofs
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

theorem source {setup : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints setup))
    (jal : Bool) (mask : w 12 = (jumpMask jal : ZMod mersenne31Modulus)) :
    source2 w = #v[w 9,w 10] := by
  have e32 := assertion_of_holds holds ⟨32,by change 32 < 117; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at e32
  have e33 := assertion_of_holds holds ⟨33,by change 33 < 117; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at e33
  have f18 : w 18 = 0 := by simpa [bit] using flags holds jal mask ⟨1,by decide⟩
  simp [f18] at e32 e33
  have lo : w 47 = w 9 := by linear_combination -e32
  have hi : w 48 = w 10 := by linear_combination -e33
  simp [source2,lo,hi]

theorem source_port {setup : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints setup))
    (jal : Bool) (mask : w 12 = (jumpMask jal : ZMod mersenne31Modulus)) :
    w 39 = w 6 ∧ w 40 = 0 ∧ w 88 = 1 := by
  have e60 := assertion_of_holds holds ⟨60,by change 60 < 117; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at e60
  have e61 := assertion_of_holds holds ⟨61,by change 61 < 117; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at e61
  have e113 := assertion_of_holds holds ⟨113,by change 113 < 117; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at e113
  have f27 : w 27 = 0 := by simpa [bit] using flags holds jal mask ⟨10,by decide⟩
  simp [f27] at e60 e61 e113
  exact ⟨by linear_combination -e60,e61,by linear_combination -e113⟩

theorem base {setup : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints setup))
    (jal : Bool) (mask : w 12 = (jumpMask jal : ZMod mersenne31Modulus)) :
    #v[w 81,w 82] = (if jal then #v[w 0,w 1] else #v[w 35,w 36]) := by
  have e46 := assertion_of_holds holds ⟨46,by change 46 < 117; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at e46
  have e47 := assertion_of_holds holds ⟨47,by change 47 < 117; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at e47
  have selected := flags holds jal mask ⟨15,by decide⟩
  cases jal
  all_goals simp [bit] at selected
  all_goals simp [selected] at e46 e47
  all_goals simp
  all_goals exact ⟨by linear_combination -e46,by linear_combination -e47⟩

theorem limb_equations {setup : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints setup))
    (jal : Bool) (mask : w 12 = (jumpMask jal : ZMod mersenne31Modulus)) :
    w 81+w 9 = w 61+65536*w 95 ∧ w 95+w 82+w 10 = w 62+65536*w 63 := by
  have e74 := assertion_of_holds holds ⟨74,by change 74 < 117; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at e74
  have e75 := assertion_of_holds holds ⟨75,by change 75 < 117; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at e75
  have f20 : w 20 = 0 := by simpa [bit] using flags holds jal mask ⟨3,by decide⟩
  have f21 : w 21 = 0 := by simpa [bit] using flags holds jal mask ⟨4,by decide⟩
  have f22 : w 22 = 0 := by simpa [bit] using flags holds jal mask ⟨5,by decide⟩
  have f23 : w 23 = 0 := by simpa [bit] using flags holds jal mask ⟨6,by decide⟩
  have f24 : w 24 = 0 := by simpa [bit] using flags holds jal mask ⟨7,by decide⟩
  have f25 : w 25 = 1 := by simpa [bit] using flags holds jal mask ⟨8,by decide⟩
  have f26 : w 26 = 0 := by simpa [bit] using flags holds jal mask ⟨9,by decide⟩
  have f27 : w 27 = 0 := by simpa [bit] using flags holds jal mask ⟨10,by decide⟩
  have f28 : w 28 = 0 := by simpa [bit] using flags holds jal mask ⟨11,by decide⟩
  have f29 : w 29 = 0 := by simpa [bit] using flags holds jal mask ⟨12,by decide⟩
  have f30 : w 30 = 0 := by simpa [bit] using flags holds jal mask ⟨13,by decide⟩
  have f31 : w 31 = 0 := by simpa [bit] using flags holds jal mask ⟨14,by decide⟩
  simp [f20,f21,f23,f25,f27,f28,f30,f31] at e74 e75
  exact ⟨by linear_combination e74,by linear_combination e75⟩

theorem query_fields {setup : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints setup))
    (jal : Bool) (mask : w 12 = (jumpMask jal : ZMod mersenne31Modulus)) :
    #v[w 100,w 101,w 102,w 103] = #v[w 61,w 64,w 65,17] ∧
      w 107 = 0 ∧ w 111 = 0 ∧ w 115 = 0 := by
  have e82 := assertion_of_holds holds ⟨82,by change 82 < 117; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at e82
  have e83 := assertion_of_holds holds ⟨83,by change 83 < 117; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at e83
  have e84 := assertion_of_holds holds ⟨84,by change 84 < 117; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at e84
  have e85 := assertion_of_holds holds ⟨85,by change 85 < 117; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at e85
  have e89 := assertion_of_holds holds ⟨89,by change 89 < 117; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at e89
  have e93 := assertion_of_holds holds ⟨93,by change 93 < 117; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at e93
  have e97 := assertion_of_holds holds ⟨97,by change 97 < 117; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at e97
  have f20 : w 20 = 0 := by simpa [bit] using flags holds jal mask ⟨3,by decide⟩
  have f21 : w 21 = 0 := by simpa [bit] using flags holds jal mask ⟨4,by decide⟩
  have f22 : w 22 = 0 := by simpa [bit] using flags holds jal mask ⟨5,by decide⟩
  have f23 : w 23 = 0 := by simpa [bit] using flags holds jal mask ⟨6,by decide⟩
  have f24 : w 24 = 0 := by simpa [bit] using flags holds jal mask ⟨7,by decide⟩
  have f25 : w 25 = 1 := by simpa [bit] using flags holds jal mask ⟨8,by decide⟩
  have f26 : w 26 = 0 := by simpa [bit] using flags holds jal mask ⟨9,by decide⟩
  have f27 : w 27 = 0 := by simpa [bit] using flags holds jal mask ⟨10,by decide⟩
  have f28 : w 28 = 0 := by simpa [bit] using flags holds jal mask ⟨11,by decide⟩
  have f29 : w 29 = 0 := by simpa [bit] using flags holds jal mask ⟨12,by decide⟩
  have f30 : w 30 = 0 := by simpa [bit] using flags holds jal mask ⟨13,by decide⟩
  have f31 : w 31 = 0 := by simpa [bit] using flags holds jal mask ⟨14,by decide⟩
  simp [f22,f23,f24,f25,f27,f29,f31] at e82 e83 e84 e85 e89 e93 e97
  have key : w 100 = w 61 := by linear_combination -e82
  have low : w 101 = w 64 := by linear_combination -e83
  have high : w 102 = w 65 := by linear_combination -e84
  have tag : w 103 = 17 := by linear_combination -e85
  simp [key,low,high,tag,e89,e93,e97]

theorem misaligned_rejected {setup : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints setup))
    (jal : Bool) (mask : w 12 = (jumpMask jal : ZMod mersenne31Modulus)) :
    w 64 = 0 := by
  have e48 := assertion_of_holds holds ⟨48,by change 48 < 117; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at e48
  have f25 : w 25 = 1 := by simpa [bit] using flags holds jal mask ⟨8,by decide⟩
  simpa [f25] using e48

theorem candidate {setup : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints setup))
    (jal : Bool) (mask : w 12 = (jumpMask jal : ZMod mersenne31Modulus)) :
    jumpCandidate w = defaultPC w := by
  have e54 := assertion_of_holds holds ⟨54,by change 54 < 117; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at e54
  have e55 := assertion_of_holds holds ⟨55,by change 55 < 117; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at e55
  have e98 := assertion_of_holds holds ⟨98,by change 98 < 117; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at e98
  have e99 := assertion_of_holds holds ⟨99,by change 99 < 117; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at e99
  have f20 : w 20 = 0 := by simpa [bit] using flags holds jal mask ⟨3,by decide⟩
  have f21 : w 21 = 0 := by simpa [bit] using flags holds jal mask ⟨4,by decide⟩
  have f22 : w 22 = 0 := by simpa [bit] using flags holds jal mask ⟨5,by decide⟩
  have f23 : w 23 = 0 := by simpa [bit] using flags holds jal mask ⟨6,by decide⟩
  have f24 : w 24 = 0 := by simpa [bit] using flags holds jal mask ⟨7,by decide⟩
  have f25 : w 25 = 1 := by simpa [bit] using flags holds jal mask ⟨8,by decide⟩
  have f26 : w 26 = 0 := by simpa [bit] using flags holds jal mask ⟨9,by decide⟩
  have f27 : w 27 = 0 := by simpa [bit] using flags holds jal mask ⟨10,by decide⟩
  have f28 : w 28 = 0 := by simpa [bit] using flags holds jal mask ⟨11,by decide⟩
  have f29 : w 29 = 0 := by simpa [bit] using flags holds jal mask ⟨12,by decide⟩
  have f30 : w 30 = 0 := by simpa [bit] using flags holds jal mask ⟨13,by decide⟩
  have f31 : w 31 = 0 := by simpa [bit] using flags holds jal mask ⟨14,by decide⟩
  simp [f20,f21,f22,f23,f24,f25,f26,f27,f28,f29,f30] at e54 e55 e98 e99
  simp [e54,e55] at e98 e99
  have lo : w 116 = w 49 := by linear_combination -e98
  have hi : w 117 = w 50 := by linear_combination -e99
  simp [jumpCandidate,defaultPC,lo,hi]

theorem write {setup : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints setup))
    (jal : Bool) (mask : w 12 = (jumpMask jal : ZMod mersenne31Modulus)) :
    rdPort.address.code w = Nat.pair 0 (Nat.pair (rdIndex w).val 0) ∧
    rdWrite w = (jumpCandidate w).map (fun value => (1 - rdZeroFlag w) * value) := by
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
  have f17 := flags holds jal mask ⟨0,by decide⟩
  have f31 := flags holds jal mask ⟨14,by decide⟩
  have update : w 17 = 1 := by simpa [bit] using f17
  have off : w 31 = 0 := by simpa [bit] using f31
  simp [update,off] at e102 e103 e106 e107 e114
  have address : w 45 = w 7 := by linear_combination -e102
  have space : w 89 = 1 := by linear_combination -e114
  have lo : w 43 = (1 - w 8) * w 116 := by linear_combination -e106 - e100
  have hi : w 44 = (1 - w 8) * w 117 := by linear_combination -e107 - e101
  constructor
  · simp [NativePortProofs.address_columns,Trace.MemoryAddress.code,Trace.pairCode,space,address,e103,rdIndex,
      importedConstraintsDecoderColumns]
  · simp [rdWrite,NativePortProofs.write_columns,Trace.WordColumns.evaluate,
      jumpCandidate,rdZeroFlag,importedConstraintsDecoderColumns,lo,hi]

theorem pc {setup : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints setup))
    (jal : Bool) (mask : w 12 = (jumpMask jal : ZMod mersenne31Modulus)) :
    finalPC w = #v[w 65,w 62] := by
  have e110 := assertion_of_holds holds ⟨110,by change 110 < 117; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at e110
  have e111 := assertion_of_holds holds ⟨111,by change 111 < 117; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at e111
  have f20 : w 20 = 0 := by simpa [bit] using flags holds jal mask ⟨3,by decide⟩
  have f21 : w 21 = 0 := by simpa [bit] using flags holds jal mask ⟨4,by decide⟩
  have f22 : w 22 = 0 := by simpa [bit] using flags holds jal mask ⟨5,by decide⟩
  have f23 : w 23 = 0 := by simpa [bit] using flags holds jal mask ⟨6,by decide⟩
  have f24 : w 24 = 0 := by simpa [bit] using flags holds jal mask ⟨7,by decide⟩
  have f25 : w 25 = 1 := by simpa [bit] using flags holds jal mask ⟨8,by decide⟩
  have f26 : w 26 = 0 := by simpa [bit] using flags holds jal mask ⟨9,by decide⟩
  have f27 : w 27 = 0 := by simpa [bit] using flags holds jal mask ⟨10,by decide⟩
  have f28 : w 28 = 0 := by simpa [bit] using flags holds jal mask ⟨11,by decide⟩
  have f29 : w 29 = 0 := by simpa [bit] using flags holds jal mask ⟨12,by decide⟩
  have f30 : w 30 = 0 := by simpa [bit] using flags holds jal mask ⟨13,by decide⟩
  have f31 : w 31 = 0 := by simpa [bit] using flags holds jal mask ⟨14,by decide⟩
  simp [f20,f21,f22,f23,f24,f25,f26,f27,f28,f29,f30,f31] at e110 e111
  have lo : w 13 = w 65 := by linear_combination -e110
  have hi : w 14 = w 62 := by linear_combination -e111
  simp [finalPC,importedConstraintsTraceColumns,lo,hi]

end Airbender.ReducedMachine.NativeJumpFieldProofs
