import Airbender.Proofs.ReducedMachine.NativeComparisonSelectors
import Airbender.Proofs.ReducedMachine.NativePorts
import Airbender.Proofs.ReducedMachine.NativeQueries

namespace Airbender.ReducedMachine.NativeComparisonFieldProofs
open Verification Native NativeComparisonSelectorProofs
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

/-- Actual register/immediate routing; the readonly rs2 port is separate. -/
theorem source {setup : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints setup))
    (useRegister : Bool) (mask : w 12 = (comparisonMask useRegister : ZMod mersenne31Modulus)) :
    source2 w = if useRegister then #v[w 37,w 38] else #v[w 9,w 10] := by
  have e32 := assertion_of_holds holds ⟨32,by change 32 < 117; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at e32
  have e33 := assertion_of_holds holds ⟨33,by change 33 < 117; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at e33
  have f18 : w 18 = (if useRegister then 1 else 0) := by simpa [bit] using flags holds useRegister mask ⟨1,by decide⟩
  simp [f18] at e32 e33
  have lo : w 47 = if useRegister then w 37 else w 9 := by
    cases useRegister <;> simp at e32 ⊢ <;> linear_combination -e32
  have hi : w 48 = if useRegister then w 38 else w 10 := by
    cases useRegister <;> simp at e33 ⊢ <;> linear_combination -e33
  cases useRegister <;> simp_all [source2]

/-- The actual second source remains readonly original rs2/register-space. -/
theorem source_port {setup : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints setup))
    (useRegister : Bool) (mask : w 12 = (comparisonMask useRegister : ZMod mersenne31Modulus)) :
    w 39 = w 6 ∧ w 40 = 0 ∧ w 88 = 1 := by
  have e60 := assertion_of_holds holds ⟨60,by change 60 < 117; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at e60
  have e61 := assertion_of_holds holds ⟨61,by change 61 < 117; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at e61
  have e113 := assertion_of_holds holds ⟨113,by change 113 < 117; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at e113
  have f27 : w 27 = 0 := by simpa [bit] using flags holds useRegister mask ⟨10,by decide⟩
  simp [f27] at e60 e61 e113
  exact ⟨by linear_combination -e60,e61,by linear_combination -e113⟩

/-- Actual rd register-space/address and field-masked port write. Original
    public decoding must still identify rdZeroFlag with architectural x0. -/
theorem write {setup : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints setup))
    (useRegister : Bool) (mask : w 12 = (comparisonMask useRegister : ZMod mersenne31Modulus)) :
    rdPort.address.code w = Nat.pair 0 (Nat.pair (rdIndex w).val 0) ∧
    rdWrite w = (arithmeticCandidate w).map (fun value => (1 - rdZeroFlag w) * value) := by
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
  have f17 := flags holds useRegister mask ⟨0,by decide⟩
  have f31 := flags holds useRegister mask ⟨14,by decide⟩
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
      arithmeticCandidate,rdZeroFlag,importedConstraintsDecoderColumns,lo,hi]

/-- The two actual conditional queries retain packed flags and separate outputs. -/
theorem query_fields {setup : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints setup))
    (useRegister : Bool) (mask : w 12 = (comparisonMask useRegister : ZMod mersenne31Modulus)) :
    #v[w 100,w 101,w 102,w 103] = #v[w 69,w 64,w 65,17] ∧
    #v[w 104,w 105,w 106,w 107] = #v[w 11+8*w 63+16*w 68+32*w 56+64*w 59,w 66,w 67,22] := by
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
  have f20 : w 20 = 0 := by simpa [bit] using flags holds useRegister mask ⟨3,by decide⟩
  have f21 : w 21 = 0 := by simpa [bit] using flags holds useRegister mask ⟨4,by decide⟩
  have f22 : w 22 = 0 := by simpa [bit] using flags holds useRegister mask ⟨5,by decide⟩
  have f23 : w 23 = 1 := by simpa [bit] using flags holds useRegister mask ⟨6,by decide⟩
  have f24 : w 24 = 0 := by simpa [bit] using flags holds useRegister mask ⟨7,by decide⟩
  have f25 : w 25 = 0 := by simpa [bit] using flags holds useRegister mask ⟨8,by decide⟩
  have f26 : w 26 = 0 := by simpa [bit] using flags holds useRegister mask ⟨9,by decide⟩
  have f27 : w 27 = 0 := by simpa [bit] using flags holds useRegister mask ⟨10,by decide⟩
  have f28 : w 28 = 0 := by simpa [bit] using flags holds useRegister mask ⟨11,by decide⟩
  have f29 : w 29 = 0 := by simpa [bit] using flags holds useRegister mask ⟨12,by decide⟩
  have f30 : w 30 = 0 := by simpa [bit] using flags holds useRegister mask ⟨13,by decide⟩
  have f31 : w 31 = 0 := by simpa [bit] using flags holds useRegister mask ⟨14,by decide⟩
  have f32 : w 32 = 0 := by simpa [bit] using flags holds useRegister mask ⟨15,by decide⟩
  have f33 : w 33 = 0 := by simpa [bit] using flags holds useRegister mask ⟨16,by decide⟩
  have f34 : w 34 = 0 := by simpa [bit] using flags holds useRegister mask ⟨17,by decide⟩
  simp [f22,f23,f24,f25,f27,f29,f31,f33] at e82 e83 e84 e85 e86 e87 e88 e89
  have key : w 104 = w 11+8*w 63+16*w 68+32*w 56+64*w 59 := by linear_combination -e86
  have cleanup : w 100 = w 69 := by linear_combination -e82
  simp [key,cleanup]
  exact ⟨⟨by linear_combination -e83,by linear_combination -e84,by linear_combination -e85⟩,
    by linear_combination -e87,by linear_combination -e88,by linear_combination -e89⟩

/-- Shared native subtraction produces the actual comparison borrow. -/
theorem limb_equations {setup : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints setup))
    (useRegister : Bool) (mask : w 12 = (comparisonMask useRegister : ZMod mersenne31Modulus)) :
    w 61+w 47 = w 35+65536*w 95 ∧ w 95+w 62+w 48 = w 36+65536*w 63 := by
  have e74 := assertion_of_holds holds ⟨74,by change 74 < 117; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at e74
  have e75 := assertion_of_holds holds ⟨75,by change 75 < 117; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at e75
  have f20 : w 20 = 0 := by simpa [bit] using flags holds useRegister mask ⟨3,by decide⟩
  have f21 : w 21 = 0 := by simpa [bit] using flags holds useRegister mask ⟨4,by decide⟩
  have f22 : w 22 = 0 := by simpa [bit] using flags holds useRegister mask ⟨5,by decide⟩
  have f23 : w 23 = 1 := by simpa [bit] using flags holds useRegister mask ⟨6,by decide⟩
  have f24 : w 24 = 0 := by simpa [bit] using flags holds useRegister mask ⟨7,by decide⟩
  have f25 : w 25 = 0 := by simpa [bit] using flags holds useRegister mask ⟨8,by decide⟩
  have f26 : w 26 = 0 := by simpa [bit] using flags holds useRegister mask ⟨9,by decide⟩
  have f27 : w 27 = 0 := by simpa [bit] using flags holds useRegister mask ⟨10,by decide⟩
  have f28 : w 28 = 0 := by simpa [bit] using flags holds useRegister mask ⟨11,by decide⟩
  have f29 : w 29 = 0 := by simpa [bit] using flags holds useRegister mask ⟨12,by decide⟩
  have f30 : w 30 = 0 := by simpa [bit] using flags holds useRegister mask ⟨13,by decide⟩
  have f31 : w 31 = 0 := by simpa [bit] using flags holds useRegister mask ⟨14,by decide⟩
  have f32 : w 32 = 0 := by simpa [bit] using flags holds useRegister mask ⟨15,by decide⟩
  have f33 : w 33 = 0 := by simpa [bit] using flags holds useRegister mask ⟨16,by decide⟩
  have f34 : w 34 = 0 := by simpa [bit] using flags holds useRegister mask ⟨17,by decide⟩
  simp [f20,f21,f23,f25,f27,f28,f30,f31] at e74 e75
  exact ⟨by linear_combination e74,by linear_combination e75⟩

/-- The conditional comparison output is the actual low candidate, with zero high limb. -/
theorem candidate {setup : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints setup))
    (useRegister : Bool) (mask : w 12 = (comparisonMask useRegister : ZMod mersenne31Modulus)) : w 116 = w 67 ∧ w 117 = 0 := by
  have e54 := assertion_of_holds holds ⟨54,by change 54 < 117; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at e54
  have e55 := assertion_of_holds holds ⟨55,by change 55 < 117; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at e55
  have e98 := assertion_of_holds holds ⟨98,by change 98 < 117; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at e98
  have e99 := assertion_of_holds holds ⟨99,by change 99 < 117; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at e99
  have f20 : w 20 = 0 := by simpa [bit] using flags holds useRegister mask ⟨3,by decide⟩
  have f21 : w 21 = 0 := by simpa [bit] using flags holds useRegister mask ⟨4,by decide⟩
  have f22 : w 22 = 0 := by simpa [bit] using flags holds useRegister mask ⟨5,by decide⟩
  have f23 : w 23 = 1 := by simpa [bit] using flags holds useRegister mask ⟨6,by decide⟩
  have f24 : w 24 = 0 := by simpa [bit] using flags holds useRegister mask ⟨7,by decide⟩
  have f25 : w 25 = 0 := by simpa [bit] using flags holds useRegister mask ⟨8,by decide⟩
  have f26 : w 26 = 0 := by simpa [bit] using flags holds useRegister mask ⟨9,by decide⟩
  have f27 : w 27 = 0 := by simpa [bit] using flags holds useRegister mask ⟨10,by decide⟩
  have f28 : w 28 = 0 := by simpa [bit] using flags holds useRegister mask ⟨11,by decide⟩
  have f29 : w 29 = 0 := by simpa [bit] using flags holds useRegister mask ⟨12,by decide⟩
  have f30 : w 30 = 0 := by simpa [bit] using flags holds useRegister mask ⟨13,by decide⟩
  have f31 : w 31 = 0 := by simpa [bit] using flags holds useRegister mask ⟨14,by decide⟩
  have f32 : w 32 = 0 := by simpa [bit] using flags holds useRegister mask ⟨15,by decide⟩
  have f33 : w 33 = 0 := by simpa [bit] using flags holds useRegister mask ⟨16,by decide⟩
  have f34 : w 34 = 0 := by simpa [bit] using flags holds useRegister mask ⟨17,by decide⟩
  simp [f20,f21,f22,f23,f24,f25,f26,f27,f28,f29,f30] at e54 e55 e98 e99
  simp [e54,e55] at e98 e99
  exact ⟨by linear_combination -e98,e99⟩

/-- Native conditional next-PC routing; lookup semantics must derive whether it jumps. -/
theorem pc_selection {setup : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints setup))
    (useRegister : Bool) (mask : w 12 = (comparisonMask useRegister : ZMod mersenne31Modulus)) :
    w 13 = w 66*w 69+(1-w 66)*w 49 ∧
    w 14 = w 66*w 70+(1-w 66)*w 50 := by
  have e42 := assertion_of_holds holds ⟨42,by change 42 < 117; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at e42
  have e43 := assertion_of_holds holds ⟨43,by change 43 < 117; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at e43
  have e110 := assertion_of_holds holds ⟨110,by change 110 < 117; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at e110
  have e111 := assertion_of_holds holds ⟨111,by change 111 < 117; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at e111
  have f20 : w 20 = 0 := by simpa [bit] using flags holds useRegister mask ⟨3,by decide⟩
  have f21 : w 21 = 0 := by simpa [bit] using flags holds useRegister mask ⟨4,by decide⟩
  have f22 : w 22 = 0 := by simpa [bit] using flags holds useRegister mask ⟨5,by decide⟩
  have f23 : w 23 = 1 := by simpa [bit] using flags holds useRegister mask ⟨6,by decide⟩
  have f24 : w 24 = 0 := by simpa [bit] using flags holds useRegister mask ⟨7,by decide⟩
  have f25 : w 25 = 0 := by simpa [bit] using flags holds useRegister mask ⟨8,by decide⟩
  have f26 : w 26 = 0 := by simpa [bit] using flags holds useRegister mask ⟨9,by decide⟩
  have f27 : w 27 = 0 := by simpa [bit] using flags holds useRegister mask ⟨10,by decide⟩
  have f28 : w 28 = 0 := by simpa [bit] using flags holds useRegister mask ⟨11,by decide⟩
  have f29 : w 29 = 0 := by simpa [bit] using flags holds useRegister mask ⟨12,by decide⟩
  have f30 : w 30 = 0 := by simpa [bit] using flags holds useRegister mask ⟨13,by decide⟩
  have f31 : w 31 = 0 := by simpa [bit] using flags holds useRegister mask ⟨14,by decide⟩
  have f32 : w 32 = 0 := by simpa [bit] using flags holds useRegister mask ⟨15,by decide⟩
  have f33 : w 33 = 0 := by simpa [bit] using flags holds useRegister mask ⟨16,by decide⟩
  have f34 : w 34 = 0 := by simpa [bit] using flags holds useRegister mask ⟨17,by decide⟩
  simp [f20,f21,f22,f23,f24,f25,f26,f27,f28,f29,f30,f31] at e110 e111
  constructor
  · linear_combination -e110-e42
  · linear_combination -e111-e43

/-- Actual full-pool membership for the monolithic resolver, not a split-table identity. -/
theorem query {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints NativeFixed.table))
    (useRegister : Bool) (mask : w 12 = (comparisonMask useRegister : ZMod mersenne31Modulus)) :
    (NativeFixed.table (p := mersenne31Modulus)).Contains #[]
      #v[w 11+8*w 63+16*w 68+32*w 56+64*w 59,w 66,w 67,22] := by
  have member := NativeQueryProofs.dynamic_queries holds 1
  change (NativeFixed.table (p := mersenne31Modulus)).Contains #[] #v[w 104,w 105,w 106,w 107] at member
  rw [(query_fields holds useRegister mask).2] at member
  exact member

end Airbender.ReducedMachine.NativeComparisonFieldProofs
