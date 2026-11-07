import Airbender.Proofs.ReducedMachine.NativeBranchSelectors
import Airbender.Proofs.ReducedMachine.NativePorts
import Airbender.Proofs.ReducedMachine.NativeQueries
import Airbender.Proofs.ReducedMachine.NativeConditionalEquality

namespace Airbender.ReducedMachine.NativeBranchFieldProofs
open Verification Native NativeBranchSelectorProofs
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

/-- Branch operands use the actual readonly second register port. -/
theorem source {setup : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints setup))
    (mask : w 12 = (branchMask : ZMod mersenne31Modulus)) :
    source2 w = #v[w 37,w 38] := by
  have e32 := assertion_of_holds holds ⟨32,by change 32 < 117; decide⟩
  have e33 := assertion_of_holds holds ⟨33,by change 33 < 117; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at e32 e33
  have selected : w 18 = 1 := by simpa [bit] using flags holds mask ⟨1,by decide⟩
  simp [selected] at e32 e33
  have lo : w 47 = w 37 := by linear_combination -e32
  have hi : w 48 = w 38 := by linear_combination -e33
  simp [source2,lo,hi]

theorem source_port {setup : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints setup))
    (mask : w 12 = (branchMask : ZMod mersenne31Modulus)) :
    w 39 = w 6 ∧ w 40 = 0 ∧ w 88 = 1 := by
  have e60 := assertion_of_holds holds ⟨60,by change 60 < 117; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at e60
  have e61 := assertion_of_holds holds ⟨61,by change 61 < 117; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at e61
  have e113 := assertion_of_holds holds ⟨113,by change 113 < 117; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at e113
  have f27 : w 27 = 0 := by simpa [bit] using flags holds mask ⟨10,by decide⟩
  simp [f27] at e60 e61 e113
  exact ⟨by linear_combination -e60,e61,by linear_combination -e113⟩

/-- The branch's third port remains present, in register space at x0,
    with zero write. Its old read still participates in native history. -/
theorem dummy_port {setup : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints setup))
    (mask : w 12 = (branchMask : ZMod mersenne31Modulus)) :
    rdPort.address.code w = Nat.pair 0 (Nat.pair 0 0) ∧ rdWrite w = #v[0,0] := by
  have e104 := assertion_of_holds holds ⟨104,by change 104 < 117; decide⟩
  have e105 := assertion_of_holds holds ⟨105,by change 105 < 117; decide⟩
  have e108 := assertion_of_holds holds ⟨108,by change 108 < 117; decide⟩
  have e109 := assertion_of_holds holds ⟨109,by change 109 < 117; decide⟩
  have e114 := assertion_of_holds holds ⟨114,by change 114 < 117; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at e104 e105 e108 e109 e114
  have branch : w 19 = 1 := by simpa [bit] using flags holds mask ⟨2,by decide⟩
  have noStore : w 31 = 0 := by simpa [bit] using flags holds mask ⟨14,by decide⟩
  simp [branch] at e104 e105 e108 e109
  have space : w 89 = 1 := by linear_combination -e114-noStore
  constructor
  · simp [NativePortProofs.address_columns,Trace.MemoryAddress.code,Trace.pairCode,space,e104,e105]
  · simp [rdWrite,NativePortProofs.write_columns,Trace.WordColumns.evaluate,e108,e109]

theorem query_fields {setup : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints setup))
    (mask : w 12 = (branchMask : ZMod mersenne31Modulus)) :
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
  have f20 : w 20 = 0 := by simpa [bit] using flags holds mask ⟨3,by decide⟩
  have f21 : w 21 = 0 := by simpa [bit] using flags holds mask ⟨4,by decide⟩
  have f22 : w 22 = 0 := by simpa [bit] using flags holds mask ⟨5,by decide⟩
  have f23 : w 23 = 1 := by simpa [bit] using flags holds mask ⟨6,by decide⟩
  have f24 : w 24 = 0 := by simpa [bit] using flags holds mask ⟨7,by decide⟩
  have f25 : w 25 = 0 := by simpa [bit] using flags holds mask ⟨8,by decide⟩
  have f26 : w 26 = 0 := by simpa [bit] using flags holds mask ⟨9,by decide⟩
  have f27 : w 27 = 0 := by simpa [bit] using flags holds mask ⟨10,by decide⟩
  have f28 : w 28 = 0 := by simpa [bit] using flags holds mask ⟨11,by decide⟩
  have f29 : w 29 = 0 := by simpa [bit] using flags holds mask ⟨12,by decide⟩
  have f30 : w 30 = 0 := by simpa [bit] using flags holds mask ⟨13,by decide⟩
  have f31 : w 31 = 0 := by simpa [bit] using flags holds mask ⟨14,by decide⟩
  have f32 : w 32 = 0 := by simpa [bit] using flags holds mask ⟨15,by decide⟩
  have f33 : w 33 = 0 := by simpa [bit] using flags holds mask ⟨16,by decide⟩
  have f34 : w 34 = 0 := by simpa [bit] using flags holds mask ⟨17,by decide⟩
  simp [f22,f23,f24,f25,f27,f29,f31,f33] at e82 e83 e84 e85 e86 e87 e88 e89
  have key : w 104 = w 11+8*w 63+16*w 68+32*w 56+64*w 59 := by linear_combination -e86
  have cleanup : w 100 = w 69 := by linear_combination -e82
  simp [key,cleanup]
  exact ⟨⟨by linear_combination -e83,by linear_combination -e84,by linear_combination -e85⟩,
    by linear_combination -e87,by linear_combination -e88,by linear_combination -e89⟩

theorem limb_equations {setup : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints setup))
    (mask : w 12 = (branchMask : ZMod mersenne31Modulus)) :
    w 61+w 47 = w 35+65536*w 95 ∧ w 95+w 62+w 48 = w 36+65536*w 63 := by
  have e74 := assertion_of_holds holds ⟨74,by change 74 < 117; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at e74
  have e75 := assertion_of_holds holds ⟨75,by change 75 < 117; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at e75
  have f20 : w 20 = 0 := by simpa [bit] using flags holds mask ⟨3,by decide⟩
  have f21 : w 21 = 0 := by simpa [bit] using flags holds mask ⟨4,by decide⟩
  have f22 : w 22 = 0 := by simpa [bit] using flags holds mask ⟨5,by decide⟩
  have f23 : w 23 = 1 := by simpa [bit] using flags holds mask ⟨6,by decide⟩
  have f24 : w 24 = 0 := by simpa [bit] using flags holds mask ⟨7,by decide⟩
  have f25 : w 25 = 0 := by simpa [bit] using flags holds mask ⟨8,by decide⟩
  have f26 : w 26 = 0 := by simpa [bit] using flags holds mask ⟨9,by decide⟩
  have f27 : w 27 = 0 := by simpa [bit] using flags holds mask ⟨10,by decide⟩
  have f28 : w 28 = 0 := by simpa [bit] using flags holds mask ⟨11,by decide⟩
  have f29 : w 29 = 0 := by simpa [bit] using flags holds mask ⟨12,by decide⟩
  have f30 : w 30 = 0 := by simpa [bit] using flags holds mask ⟨13,by decide⟩
  have f31 : w 31 = 0 := by simpa [bit] using flags holds mask ⟨14,by decide⟩
  have f32 : w 32 = 0 := by simpa [bit] using flags holds mask ⟨15,by decide⟩
  have f33 : w 33 = 0 := by simpa [bit] using flags holds mask ⟨16,by decide⟩
  have f34 : w 34 = 0 := by simpa [bit] using flags holds mask ⟨17,by decide⟩
  simp [f20,f21,f23,f25,f27,f28,f30,f31] at e74 e75
  exact ⟨by linear_combination e74,by linear_combination e75⟩

theorem pc_selection {setup : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints setup))
    (mask : w 12 = (branchMask : ZMod mersenne31Modulus)) :
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
  have f20 : w 20 = 0 := by simpa [bit] using flags holds mask ⟨3,by decide⟩
  have f21 : w 21 = 0 := by simpa [bit] using flags holds mask ⟨4,by decide⟩
  have f22 : w 22 = 0 := by simpa [bit] using flags holds mask ⟨5,by decide⟩
  have f23 : w 23 = 1 := by simpa [bit] using flags holds mask ⟨6,by decide⟩
  have f24 : w 24 = 0 := by simpa [bit] using flags holds mask ⟨7,by decide⟩
  have f25 : w 25 = 0 := by simpa [bit] using flags holds mask ⟨8,by decide⟩
  have f26 : w 26 = 0 := by simpa [bit] using flags holds mask ⟨9,by decide⟩
  have f27 : w 27 = 0 := by simpa [bit] using flags holds mask ⟨10,by decide⟩
  have f28 : w 28 = 0 := by simpa [bit] using flags holds mask ⟨11,by decide⟩
  have f29 : w 29 = 0 := by simpa [bit] using flags holds mask ⟨12,by decide⟩
  have f30 : w 30 = 0 := by simpa [bit] using flags holds mask ⟨13,by decide⟩
  have f31 : w 31 = 0 := by simpa [bit] using flags holds mask ⟨14,by decide⟩
  have f32 : w 32 = 0 := by simpa [bit] using flags holds mask ⟨15,by decide⟩
  have f33 : w 33 = 0 := by simpa [bit] using flags holds mask ⟨16,by decide⟩
  have f34 : w 34 = 0 := by simpa [bit] using flags holds mask ⟨17,by decide⟩
  simp [f20,f21,f22,f23,f24,f25,f26,f27,f28,f29,f30,f31] at e110 e111
  constructor
  · linear_combination -e110-e42
  · linear_combination -e111-e43

theorem query {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints NativeFixed.table))
    (mask : w 12 = (branchMask : ZMod mersenne31Modulus)) :
    (NativeFixed.table (p := mersenne31Modulus)).Contains #[]
      #v[w 11+8*w 63+16*w 68+32*w 56+64*w 59,w 66,w 67,22] := by
  have member := NativeQueryProofs.dynamic_queries holds 1
  change (NativeFixed.table (p := mersenne31Modulus)).Contains #[] #v[w 104,w 105,w 106,w 107] at member
  rw [(query_fields holds mask).2] at member
  exact member

/-- Shared zero-test semantics with the actual major flag discharged. -/
theorem equality_flag {setup : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints setup))
    (mask : w 12 = (branchMask : ZMod mersenne31Modulus)) :
    w 68 = if (w 61).val = 0 ∧ (w 62).val = 0 then 1 else 0 := by
  apply NativeConditionalEqualityProofs.remainder_zero holds
  simpa [bit] using flags holds mask ⟨6,by decide⟩

theorem routing {setup : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints setup))
    (mask : w 12 = (branchMask : ZMod mersenne31Modulus)) : BranchRouting w := by
  exact ⟨source holds mask,source_port holds mask,(dummy_port holds mask).1,
    (dummy_port holds mask).2,(pc_selection holds mask).1,
    (pc_selection holds mask).2,equality_flag holds mask⟩

end Airbender.ReducedMachine.NativeBranchFieldProofs
