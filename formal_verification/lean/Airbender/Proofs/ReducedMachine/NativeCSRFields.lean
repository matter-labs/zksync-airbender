import Airbender.Proofs.ReducedMachine.NativeCSRSelectors
import Airbender.Proofs.ReducedMachine.NativePorts

namespace Airbender.ReducedMachine.NativeCSRFieldProofs
open Verification Native NativeCSRSelectorProofs
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

/-- Exact imported coordinates, including the ABI group and in-cycle index. -/
theorem request_columns : importedConstraintsRequestColumns =
    (⟨92,94,some 93,3⟩ : DelegationRequestCoordinates) := rfl

theorem source_port {setup : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints setup))
    (mask : w 12 = (csrMask : ZMod mersenne31Modulus)) : w 39 = w 6 ∧ w 40 = 0 ∧ w 88 = 1 := by
  have e60 := assertion_of_holds holds ⟨60,by change 60 < 117; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at e60
  have e61 := assertion_of_holds holds ⟨61,by change 61 < 117; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at e61
  have e113 := assertion_of_holds holds ⟨113,by change 113 < 117; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at e113
  have f27 := flags holds mask ⟨10,by decide⟩
  have off : w 27 = 0 := by simpa [bit] using f27
  simp [off] at e60 e61 e113
  exact ⟨by linear_combination -e60,e61,by linear_combination -e113⟩

theorem tags {setup : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints setup))
    (mask : w 12 = (csrMask : ZMod mersenne31Modulus)) : lookupSelectors w = #v[25,0,0,0] := by
  have e85 := assertion_of_holds holds ⟨85,by change 85 < 117; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at e85
  have e89 := assertion_of_holds holds ⟨89,by change 89 < 117; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at e89
  have e93 := assertion_of_holds holds ⟨93,by change 93 < 117; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at e93
  have e97 := assertion_of_holds holds ⟨97,by change 97 < 117; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at e97
  have f22 := flags holds mask ⟨5,by decide⟩
  have f23 := flags holds mask ⟨6,by decide⟩
  have f24 := flags holds mask ⟨7,by decide⟩
  have f25 := flags holds mask ⟨8,by decide⟩
  have f27 := flags holds mask ⟨10,by decide⟩
  have f29 := flags holds mask ⟨12,by decide⟩
  have f31 := flags holds mask ⟨14,by decide⟩
  simp only [bit] at f22 f23 f24 f25 f27 f29 f31
  simp [f22,f23,f24,f25,f27,f29,f31] at e85 e89 e93 e97
  have tag : w 103 = 25 := by linear_combination -e85
  simp [lookupSelectors,tag,e89,e93,e97]

theorem candidate {setup : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints setup))
    (mask : w 12 = (csrMask : ZMod mersenne31Modulus)) :
    csrCandidate w = #v[w 90,w 91] := by
  have e54 := assertion_of_holds holds ⟨54,by change 54 < 117; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at e54
  have e55 := assertion_of_holds holds ⟨55,by change 55 < 117; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at e55
  have e98 := assertion_of_holds holds ⟨98,by change 98 < 117; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at e98
  have e99 := assertion_of_holds holds ⟨99,by change 99 < 117; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at e99
  have f20 := flags holds mask ⟨3,by decide⟩
  have f21 := flags holds mask ⟨4,by decide⟩
  have f22 := flags holds mask ⟨5,by decide⟩
  have f23 := flags holds mask ⟨6,by decide⟩
  have f24 := flags holds mask ⟨7,by decide⟩
  have f25 := flags holds mask ⟨8,by decide⟩
  have f26 := flags holds mask ⟨9,by decide⟩
  have f27 := flags holds mask ⟨10,by decide⟩
  have f28 := flags holds mask ⟨11,by decide⟩
  have f29 := flags holds mask ⟨12,by decide⟩
  have f30 := flags holds mask ⟨13,by decide⟩
  have f31 := flags holds mask ⟨14,by decide⟩
  simp only [bit] at f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31
  simp [f27] at e54 e55
  simp [f20,f21,f22,f23,f24,f25,f26,f28,f29,f30,e54,e55] at e98 e99
  have low : w 116 = w 90 := by linear_combination -e98
  have high : w 117 = w 91 := by linear_combination -e99
  simp [csrCandidate,low,high]

theorem write {setup : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints setup))
    (mask : w 12 = (csrMask : ZMod mersenne31Modulus)) :
    rdPort.address.code w = Nat.pair 0 (Nat.pair (rdIndex w).val 0) ∧
    rdWrite w = (csrCandidate w).map (fun value => (1 - rdZeroFlag w) * value) := by
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
  have f17 := flags holds mask ⟨0,by decide⟩
  have f31 := flags holds mask ⟨14,by decide⟩
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
      csrCandidate,rdZeroFlag,importedConstraintsDecoderColumns,lo,hi]

theorem pc {setup : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints setup))
    (mask : w 12 = (csrMask : ZMod mersenne31Modulus)) : finalPC w = defaultPC w := by
  have e110 := assertion_of_holds holds ⟨110,by change 110 < 117; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at e110
  have e111 := assertion_of_holds holds ⟨111,by change 111 < 117; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at e111
  have f20 := flags holds mask ⟨3,by decide⟩
  have f21 := flags holds mask ⟨4,by decide⟩
  have f22 := flags holds mask ⟨5,by decide⟩
  have f23 := flags holds mask ⟨6,by decide⟩
  have f24 := flags holds mask ⟨7,by decide⟩
  have f25 := flags holds mask ⟨8,by decide⟩
  have f26 := flags holds mask ⟨9,by decide⟩
  have f27 := flags holds mask ⟨10,by decide⟩
  have f28 := flags holds mask ⟨11,by decide⟩
  have f29 := flags holds mask ⟨12,by decide⟩
  have f30 := flags holds mask ⟨13,by decide⟩
  have f31 := flags holds mask ⟨14,by decide⟩
  simp only [bit] at f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31
  simp [f20,f21,f22,f23,f24,f25,f26,f27,f28,f29,f30,f31] at e110 e111
  have lo : w 13 = w 49 := by linear_combination -e110
  have hi : w 14 = w 50 := by linear_combination -e111
  simp [finalPC,defaultPC,importedConstraintsTraceColumns,lo,hi]

theorem source {setup : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints setup))
    (mask : w 12 = (csrMask : ZMod mersenne31Modulus)) : source2 w = #v[w 9,w 10] := by
  have e32 := assertion_of_holds holds ⟨32,by change 32 < 117; decide⟩
  have e33 := assertion_of_holds holds ⟨33,by change 33 < 117; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at e32 e33
  have off : w 18 = 0 := by simpa [bit] using flags holds mask ⟨1,by decide⟩
  simp [off] at e32 e33
  have lo : w 47 = w 9 := by linear_combination -e32
  have hi : w 48 = w 10 := by linear_combination -e33
  simp [source2,lo,hi]

theorem query {setup : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints setup))
    (mask : w 12 = (csrMask : ZMod mersenne31Modulus)) :
    #v[w 100,w 101,w 102,w 103] = #v[w 9,w 64,w 65,25] := by
  have e82 := assertion_of_holds holds ⟨82,by change 82 < 117; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at e82
  have e83 := assertion_of_holds holds ⟨83,by change 83 < 117; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at e83
  have e84 := assertion_of_holds holds ⟨84,by change 84 < 117; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at e84
  have e85 := assertion_of_holds holds ⟨85,by change 85 < 117; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at e85
  have f22 : w 22 = 0 := by simpa [bit] using flags holds mask ⟨5,by decide⟩
  have f23 : w 23 = 0 := by simpa [bit] using flags holds mask ⟨6,by decide⟩
  have f24 : w 24 = 1 := by simpa [bit] using flags holds mask ⟨7,by decide⟩
  have f25 : w 25 = 0 := by simpa [bit] using flags holds mask ⟨8,by decide⟩
  have f27 : w 27 = 0 := by simpa [bit] using flags holds mask ⟨10,by decide⟩
  have f29 : w 29 = 0 := by simpa [bit] using flags holds mask ⟨12,by decide⟩
  have f31 : w 31 = 0 := by simpa [bit] using flags holds mask ⟨14,by decide⟩
  simp [f22,f23,f24,f25,f27,f29,f31] at e82 e83 e84 e85
  have lo : w 100 = w 9 := by linear_combination -e82
  have supported : w 101 = w 64 := by linear_combination -e83
  have delegated : w 102 = w 65 := by linear_combination -e84
  have tag : w 103 = 25 := by linear_combination -e85
  simp [lo,supported,delegated,tag]

theorem request_equations {setup : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints setup))
    (mask : w 12 = (csrMask : ZMod mersenne31Modulus)) :
    w 64 = 1 ∧ w 92 = w 65 ∧ w 93 = w 36*w 92 ∧ w 94 = w 9*w 92 ∧
      w 90*w 65 = 0 ∧ w 91*w 65 = 0 := by
  have e68 := assertion_of_holds holds ⟨68,by change 68 < 117; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at e68
  have e69 := assertion_of_holds holds ⟨69,by change 69 < 117; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at e69
  have e70 := assertion_of_holds holds ⟨70,by change 70 < 117; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at e70
  have e71 := assertion_of_holds holds ⟨71,by change 71 < 117; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at e71
  have e72 := assertion_of_holds holds ⟨72,by change 72 < 117; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at e72
  have e73 := assertion_of_holds holds ⟨73,by change 73 < 117; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at e73
  have active : w 24 = 1 := by simpa [bit] using flags holds mask ⟨7,by decide⟩
  simp [active] at e68 e69
  exact ⟨by linear_combination -e68,by linear_combination -e69,
    by linear_combination -e70,by linear_combination -e71,mul_eq_zero.mpr e72,mul_eq_zero.mpr e73⟩

end Airbender.ReducedMachine.NativeCSRFieldProofs
