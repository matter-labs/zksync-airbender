import Airbender.Proofs.ReducedMachine.NativeBitwiseSelectors
import Airbender.Proofs.ReducedMachine.NativePorts
import Airbender.Proofs.ReducedMachine.NativeQueries

namespace Airbender.ReducedMachine.NativeBitwiseFieldProofs
open Verification Native NativeBitwiseSelectorProofs
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

/-- Actual register/immediate routing; the readonly rs2 port is separate. -/
theorem source {setup : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints setup))
    (useRegister : Bool) (mask : w 12 = (bitwiseMask useRegister : ZMod mersenne31Modulus)) :
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
    (useRegister : Bool) (mask : w 12 = (bitwiseMask useRegister : ZMod mersenne31Modulus)) :
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

/-- All actual query triples/tags and inverse-256 source decomposition come
    from accepted monolithic equations, not a supplied byte/result answer. -/
theorem query_fields {setup : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints setup))
    (useRegister : Bool) (mask : w 12 = (bitwiseMask useRegister : ZMod mersenne31Modulus)) :
    (∀ slot : Fin 4, #v[w (100 + 4 * slot.val),w (101 + 4 * slot.val),
      w (102 + 4 * slot.val),w (103 + 4 * slot.val)] = (bitwiseBytes w)[slot].push (w 11)) ∧
    w 35 = w 55 + 256 * w 104 ∧ w 47 = w 58 + 256 * w 105 ∧
    w 36 = w 108 + 256 * w 57 ∧ w 48 = w 109 + 256 * w 60 := by
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
  have e90 := assertion_of_holds holds ⟨90,by change 90 < 117; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at e90
  have e91 := assertion_of_holds holds ⟨91,by change 91 < 117; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at e91
  have e92 := assertion_of_holds holds ⟨92,by change 92 < 117; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at e92
  have e93 := assertion_of_holds holds ⟨93,by change 93 < 117; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at e93
  have e94 := assertion_of_holds holds ⟨94,by change 94 < 117; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at e94
  have e95 := assertion_of_holds holds ⟨95,by change 95 < 117; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at e95
  have e96 := assertion_of_holds holds ⟨96,by change 96 < 117; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at e96
  have e97 := assertion_of_holds holds ⟨97,by change 97 < 117; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at e97
  have f22 : w 22 = 1 := by simpa [bit] using flags holds useRegister mask ⟨5,by decide⟩
  have f23 : w 23 = 0 := by simpa [bit] using flags holds useRegister mask ⟨6,by decide⟩
  have f24 : w 24 = 0 := by simpa [bit] using flags holds useRegister mask ⟨7,by decide⟩
  have f25 : w 25 = 0 := by simpa [bit] using flags holds useRegister mask ⟨8,by decide⟩
  have f27 : w 27 = 0 := by simpa [bit] using flags holds useRegister mask ⟨10,by decide⟩
  have f29 : w 29 = 0 := by simpa [bit] using flags holds useRegister mask ⟨12,by decide⟩
  have f31 : w 31 = 0 := by simpa [bit] using flags holds useRegister mask ⟨14,by decide⟩
  simp [f22,f23,f24,f25,f27,f29,f31] at e82 e83 e84 e85 e86 e87 e88 e89 e90 e91 e92 e93 e94 e95 e96 e97
  have v100 : w 100 = w 55 := by linear_combination -e82
  have v101 : w 101 = w 58 := by linear_combination -e83
  have v102 : w 102 = w 64 := by linear_combination -e84
  have v103 : w 103 = w 11 := by linear_combination -e85
  have v106 : w 106 = w 65 := by linear_combination -e88
  have v107 : w 107 = w 11 := by linear_combination -e89
  have v110 : w 110 = w 66 := by linear_combination -e92
  have v111 : w 111 = w 11 := by linear_combination -e93
  have v112 : w 112 = w 57 := by linear_combination -e94
  have v113 : w 113 = w 60 := by linear_combination -e95
  have v114 : w 114 = w 67 := by linear_combination -e96
  have v115 : w 115 = w 11 := by linear_combination -e97
  have modulus : (2147483647 : ZMod mersenne31Modulus) = 0 := by decide +kernel
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro slot
    fin_cases slot <;> simp [bitwiseBytes,v100,v101,v102,v103,v106,v107,v110,v111,v112,v113,v114,v115]
  · linear_combination (norm := (ring_nf; simp only [modulus,mul_zero,neg_zero,add_zero])) 256 * e86
  · linear_combination (norm := (ring_nf; simp only [modulus,mul_zero,neg_zero,add_zero])) 256 * e87
  · linear_combination e90
  · linear_combination e91

/-- Native candidate word assembly from the four actual byte outputs. -/
theorem candidate {setup : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints setup))
    (useRegister : Bool) (mask : w 12 = (bitwiseMask useRegister : ZMod mersenne31Modulus)) :
    w 116 = w 64 + 256 * w 65 ∧ w 117 = w 66 + 256 * w 67 := by
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
  have f22 : w 22 = 1 := by simpa [bit] using flags holds useRegister mask ⟨5,by decide⟩
  have f23 : w 23 = 0 := by simpa [bit] using flags holds useRegister mask ⟨6,by decide⟩
  have f24 : w 24 = 0 := by simpa [bit] using flags holds useRegister mask ⟨7,by decide⟩
  have f25 : w 25 = 0 := by simpa [bit] using flags holds useRegister mask ⟨8,by decide⟩
  have f26 : w 26 = 0 := by simpa [bit] using flags holds useRegister mask ⟨9,by decide⟩
  have f27 : w 27 = 0 := by simpa [bit] using flags holds useRegister mask ⟨10,by decide⟩
  have f28 : w 28 = 0 := by simpa [bit] using flags holds useRegister mask ⟨11,by decide⟩
  have f29 : w 29 = 0 := by simpa [bit] using flags holds useRegister mask ⟨12,by decide⟩
  have f30 : w 30 = 0 := by simpa [bit] using flags holds useRegister mask ⟨13,by decide⟩
  simp [f20,f21,f22,f23,f24,f25,f26,f27,f28,f29,f30] at e54 e55 e98 e99
  simp [e54,e55] at e98 e99
  exact ⟨by linear_combination -e98,by linear_combination -e99⟩

/-- Actual rd register-space/address and field-masked port write. Original
    public decoding must still identify rdZeroFlag with architectural x0. -/
theorem write {setup : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints setup))
    (useRegister : Bool) (mask : w 12 = (bitwiseMask useRegister : ZMod mersenne31Modulus)) :
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

/-- Bitwise rows select actual default PC. Numerical increment is separate. -/
theorem pc {setup : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints setup))
    (useRegister : Bool) (mask : w 12 = (bitwiseMask useRegister : ZMod mersenne31Modulus)) : finalPC w = defaultPC w := by
  have e110 := assertion_of_holds holds ⟨110,by change 110 < 117; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at e110
  have e111 := assertion_of_holds holds ⟨111,by change 111 < 117; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at e111
  have f20 : w 20 = 0 := by simpa [bit] using flags holds useRegister mask ⟨3,by decide⟩
  have f21 : w 21 = 0 := by simpa [bit] using flags holds useRegister mask ⟨4,by decide⟩
  have f22 : w 22 = 1 := by simpa [bit] using flags holds useRegister mask ⟨5,by decide⟩
  have f23 : w 23 = 0 := by simpa [bit] using flags holds useRegister mask ⟨6,by decide⟩
  have f24 : w 24 = 0 := by simpa [bit] using flags holds useRegister mask ⟨7,by decide⟩
  have f25 : w 25 = 0 := by simpa [bit] using flags holds useRegister mask ⟨8,by decide⟩
  have f26 : w 26 = 0 := by simpa [bit] using flags holds useRegister mask ⟨9,by decide⟩
  have f27 : w 27 = 0 := by simpa [bit] using flags holds useRegister mask ⟨10,by decide⟩
  have f28 : w 28 = 0 := by simpa [bit] using flags holds useRegister mask ⟨11,by decide⟩
  have f29 : w 29 = 0 := by simpa [bit] using flags holds useRegister mask ⟨12,by decide⟩
  have f30 : w 30 = 0 := by simpa [bit] using flags holds useRegister mask ⟨13,by decide⟩
  have f31 : w 31 = 0 := by simpa [bit] using flags holds useRegister mask ⟨14,by decide⟩
  simp [f20,f21,f22,f23,f24,f25,f26,f27,f28,f29,f30,f31] at e110 e111
  have lo : w 13 = w 49 := by linear_combination -e110
  have hi : w 14 = w 50 := by linear_combination -e111
  simp [finalPC,defaultPC,importedConstraintsTraceColumns,lo,hi]

/-- Every actual query participates in the complete native pool, including
    rows whose eventual destination is discarded. -/
theorem queries {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints NativeFixed.table))
    (useRegister : Bool) (mask : w 12 = (bitwiseMask useRegister : ZMod mersenne31Modulus))
    (slot : Fin 4) : (NativeFixed.table (p := mersenne31Modulus)).Contains #[]
      ((bitwiseBytes w)[slot].push (w 11)) := by
  rw [← (query_fields holds useRegister mask).1 slot]
  exact NativeQueryProofs.dynamic_queries holds slot

end Airbender.ReducedMachine.NativeBitwiseFieldProofs
