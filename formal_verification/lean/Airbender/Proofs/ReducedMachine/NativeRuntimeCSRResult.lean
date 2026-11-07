import Airbender.Proofs.ReducedMachine.NativeCSRFields
import Airbender.Proofs.ReducedMachine.NativeCSRResult
import Airbender.Review.Circuits.ReducedMachine.RuntimeCSR
import Airbender.Proofs.ReducedMachine.NativeRuntimeQueries

namespace Airbender.ReducedMachine.NativeRuntimeCSRResultProofs
open Native NativeRuntimeCSR Verification Arithmetic
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

/-- Exact native pooled membership supplies the actual supported-key domain
    and delegation flag; no supplied CSR allow-list or request answer. -/
theorem properties {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints NativeRuntimePool.table))
    (mask : w 12 = (csrMask : ZMod mersenne31Modulus)) :
    ((w 9).val = 1984 ∨ (w 9).val = 1991) ∧
      w 64 = 1 ∧ w 65 = (delegated (w 9).val : Nat) := by
  have query := NativeRuntimeQueryProofs.dynamic_queries holds 0
  change (NativeRuntimePool.table (p := mersenne31Modulus)).Contains #[] #v[w 100,w 101,w 102,w 103] at query
  rw [NativeCSRFieldProofs.query holds mask] at query
  have actual := NativeRuntimePool.csr_properties query
  have relations := NativeCSRFieldProofs.request_equations holds mask
  have allowed : (w 9).val = 1984 ∨ (w 9).val = 1991 := by
    by_contra unsupported
    have zero : w 64 = 0 := by simpa [supported,unsupported] using actual.2.1
    have impossible : (0 : ZMod mersenne31Modulus) = 1 := zero.symm.trans relations.1
    exact zero_ne_one impossible
  exact ⟨allowed,relations.1,actual.2.2⟩

/-- Request fields come from the imported coordinates and actual native
    relations. The in-cycle index is metadata, not a global schedule theorem. -/
theorem request {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints NativeRuntimePool.table))
    (mask : w 12 = (csrMask : ZMod mersenne31Modulus)) :
    csrRequest w = ⟨(delegated (w 9).val : Nat),w 9*(delegated (w 9).val : Nat),
      some (w 36*(delegated (w 9).val : Nat)),3⟩ := by
  have actual := properties holds mask
  have relations := NativeCSRFieldProofs.request_equations holds mask
  simp [csrRequest,NativeCSRFieldProofs.request_columns,relations.2.1,relations.2.2.1,relations.2.2.2.1,actual.2.2]

/-- Delegation returns actual zero oracle/candidate, independent of rd masking. -/
theorem delegation_zero {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints NativeRuntimePool.table))
    (mask : w 12 = (csrMask : ZMod mersenne31Modulus))
    (delegated : delegated (w 9).val = 1) : csrOracleWord w = ⟨0,0⟩ := by
  have actual := properties holds mask
  have relations := NativeCSRFieldProofs.request_equations holds mask
  have flag : w 65 = 1 := by simpa [delegated] using actual.2.2
  have low : w 90 = 0 := by simpa [flag] using relations.2.2.2.2.1
  have high : w 91 = 0 := by simpa [flag] using relations.2.2.2.2.2
  simp [csrOracleWord,low,high]

/-- Masked ABI-high offsets inherit the actual native source-high lookup bound;
    no caller source/history bound or expected offset is supplied. -/
theorem offset_bound {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints NativeRuntimePool.table))
    (mask : w 12 = (csrMask : ZMod mersenne31Modulus)) : (w 93).val < 65536 := by
  have actual := properties holds mask
  have relations := NativeCSRFieldProofs.request_equations holds mask
  by_cases isDelegate : (w 9).val = 1991
  · have flag : w 65 = 1 := by simpa [delegated,isDelegate] using actual.2.2
    rw [relations.2.2.1,relations.2.1,flag,mul_one]
    exact (NativeRuntimeQueryProofs.results holds).1
  · have flag : w 65 = 0 := by simpa [delegated,isDelegate] using actual.2.2
    rw [relations.2.2.1,relations.2.1,flag,mul_zero]
    decide

/-- Assemble local actual native behavior only. No original CSR execution,
    initialized architectural effects or worker fulfillment is inferred. -/
theorem effects {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints NativeRuntimePool.table))
    (mask : w 12 = (csrMask : ZMod mersenne31Modulus)) : CSRRuntimeEffects w := by
  have actual := properties holds mask
  have write := NativeCSRFieldProofs.write holds mask
  exact ⟨actual.1,actual.2.1,actual.2.2,NativeCSRFieldProofs.source holds mask,
    NativeCSRFieldProofs.source_port holds mask,NativeCSRFieldProofs.tags holds mask,
    NativeCSRFieldProofs.candidate holds mask,write.1,write.2,NativeCSRResultProofs.oracle_bounds holds,
    delegation_zero holds mask,request holds mask,offset_bound holds mask,by
      simpa [finalPC,defaultPC,importedConstraintsTraceColumns] using NativeCSRFieldProofs.pc holds mask⟩
end Airbender.ReducedMachine.NativeRuntimeCSRResultProofs
