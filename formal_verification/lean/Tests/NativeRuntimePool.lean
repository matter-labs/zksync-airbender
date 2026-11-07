import Airbender.Review.Circuits.ReducedMachine.RuntimeCSRTheorems
import Airbender.Review.Circuits.ReducedMachine.Tables.CSRTheorems

namespace Tests.NativeRuntimePool
open Airbender Arithmetic ReducedMachine Native Verification
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

/-- All thirteen other actual regions, including the retained ROM, are shared
    data by construction. This does not identify two whole setup tables. -/
theorem unchanged_regions (region : NativeRuntimePoolProofs.Region) (other : region ≠ .csr) :
    NativeRuntimePoolProofs.regionData region = region.data :=
  NativeRuntimePoolProofs.unchanged_region region other

/-- Every actual runtime CSR row occurs at its full native pool offset. This
    positive table-membership result does not assert a complete accepted row. -/
theorem all_csr_pool_rows (key : Fin 4096) :
    (NativeRuntimePool.table (p := mersenne31Modulus)).Contains #[] ((NativeRuntimeCSR.row key.val).map Nat.cast) := by
  refine ⟨⟨key.val+1507585,by change key.val+1507585<5771521; have := key.isLt; omega⟩,?_⟩
  change _ = (NativeRuntimePool.rowNat ⟨key.val+1507585,_⟩).map Nat.cast
  have h0 : ¬ key.val+1507585 < 1 := by omega
  have h1 : ¬ key.val+1507585 < 65537 := by omega
  have h2 : ¬ key.val+1507585 < 131073 := by omega
  have h3 : ¬ key.val+1507585 < 196609 := by omega
  have h4 : ¬ key.val+1507585 < 262145 := by omega
  have h5 : ¬ key.val+1507585 < 327681 := by omega
  have h6 : ¬ key.val+1507585 < 393217 := by omega
  have h7 : ¬ key.val+1507585 < 393345 := by omega
  have h8 : ¬ key.val+1507585 < 393473 := by omega
  have h9 : ¬ key.val+1507585 < 459009 := by omega
  have h10 : ¬ key.val+1507585 < 1507585 := by omega
  have selected : key.val+1507585 < 1511681 := by have := key.isLt; omega
  rw [NativeRuntimePool.rowNat,dif_neg h0,dif_neg h1,dif_neg h2,dif_neg h3,dif_neg h4,dif_neg h5,dif_neg h6,dif_neg h7,dif_neg h8,dif_neg h9,dif_neg h10,dif_pos selected]
  simp only [Nat.add_sub_cancel_right]
  rw [NativeRuntimeCSRProofs.rows]

/-- Positive full-pool CSR membership; not complete accepted execution rows. -/
theorem runtime_pool_positive :
    (NativeRuntimePool.table (p := mersenne31Modulus)).Contains #[] #v[1991,1,1,25] ∧
    (NativeRuntimePool.table (p := mersenne31Modulus)).Contains #[] #v[1984,1,0,25] := by
  constructor
  · convert all_csr_pool_rows ⟨1991,by decide⟩ using 1; decide +kernel
  · convert all_csr_pool_rows ⟨1984,by decide⟩ using 1; decide +kernel

theorem fixture_pool_row_rejected :
    ¬ (NativeRuntimePool.table (p := mersenne31Modulus)).Contains #[] #v[1988,1,1,25] := by
  intro member
  have actual := (NativeRuntimePool.csr_properties member).2.1
  have key : (1988 : ZMod mersenne31Modulus).val = 1988 := by decide +kernel
  rw [key] at actual
  norm_num [NativeRuntimeCSR.supported] at actual

theorem bigint_pool_row_rejected :
    ¬ (NativeRuntimePool.table (p := mersenne31Modulus)).Contains #[] #v[1994,1,1,25] := by
  intro member
  have actual := (NativeRuntimePool.csr_properties member).2.1
  have key : (1994 : ZMod mersenne31Modulus).val = 1994 := by decide +kernel
  rw [key] at actual
  norm_num [NativeRuntimeCSR.supported] at actual

/-- The original complete fixture still rejects Blake2 CSR1991. -/
theorem original_fixture_stays_distinct :
    ¬ (NativeFixed.table (p := mersenne31Modulus)).Contains #[] #v[1991,1,1,25] := by
  intro member
  have actual := (NativeFixed.csr_properties_implementation member).2.1
  have key : (1991 : ZMod mersenne31Modulus).val = 1991 := by decide +kernel
  rw [key] at actual
  norm_num [NativeFixed.csrSupported] at actual

section ConditionalNative
variable {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints NativeRuntimePool.table))
    (mask : w 12 = (csrMask : ZMod mersenne31Modulus))
include holds mask

/-- Unsupported keys are excluded by the actual selected query/support equation. -/
theorem unsupported_native_csr_rejected
    (unsupported : (w 9).val ≠ 1984 ∧ (w 9).val ≠ 1991) : False := by
  rcases (runtime_csr_native_effects holds mask).key with h | h
  · exact unsupported.1 h
  · exact unsupported.2 h

theorem fixture_native_csr_rejected (key : (w 9).val = 1988 ∨ (w 9).val = 1989) : False := by
  have actual := (runtime_csr_native_effects holds mask).key
  omega

theorem bigint_native_csr_rejected (key : (w 9).val = 1994) : False := by
  have actual := (runtime_csr_native_effects holds mask).key
  omega

/-- No reference stream or nondeterminism value is identified. -/
theorem nondeterminism_request_zero (key : (w 9).val = 1984) :
    csrRequest w = ⟨0,0,some 0,3⟩ ∧ (csrOracleWord w).Bounded := by
  have actual := runtime_csr_native_effects holds mask
  exact ⟨by simpa [key,NativeRuntimeCSR.delegated] using actual.request,actual.oracleBounded⟩

theorem nonzero_blake_oracle_rejected (key : (w 9).val = 1991)
    (bad : csrOracleWord w ≠ ⟨0,0⟩) : False := by
  have flag : NativeRuntimeCSR.delegated (w 9).val = 1 := by simp [NativeRuntimeCSR.delegated,key]
  exact bad ((runtime_csr_native_effects holds mask).delegationZero flag)

/-- The native CSR key and actual source-high word determine every request field. -/
theorem blake_request (key : w 9 = 1991) :
    csrRequest w = ⟨1,1991,some (w 36),3⟩ := by
  have keyValue : (1991 : ZMod mersenne31Modulus).val = 1991 := by decide +kernel
  simpa [key,keyValue,NativeRuntimeCSR.delegated] using (runtime_csr_native_effects holds mask).request

/-- Discarding rd does not discard the actual delegation request. -/
theorem discarded_destination_keeps_request (key : (w 9).val = 1991)
    (zero : rdZeroFlag w = 1) : rdWrite w = #v[0,0] ∧ (csrRequest w).multiplicity = 1 := by
  have actual := runtime_csr_native_effects holds mask
  constructor
  · rw [actual.written]
    simp [zero,csrCandidate]
  · rw [actual.request]
    simp [key,NativeRuntimeCSR.delegated]

theorem oversized_abi_high_rejected (bad : 65536 ≤ (w 93).val) : False := by
  have actual := (runtime_csr_native_effects holds mask).offsetBounded
  omega
end ConditionalNative

section ActualLookups
variable {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints NativeRuntimePool.table))
include holds
/-- Actual slot16 remains the source-high bound in this constructed full pool. -/
theorem oversized_source_high_rejected (bad : 65536 ≤ (w 36).val) : False := by
  have actual := (NativeRuntimeQueryProofs.results holds).1
  omega

/-- Every dynamic selector is derived without a selected CSR mask. -/
theorem absent_dynamic_tag_rejected (slot : Fin 4) (bad : w (103+4*slot.val) = 32) : False := by
  have actual := NativeRuntimeQueryProofs.dynamic_selectors holds slot
  rw [bad] at actual
  have tagValue : (32 : ZMod mersenne31Modulus).val = 32 := by decide +kernel
  rw [tagValue] at actual
  norm_num [NativeRuntimePool.tags,NativeFixed.tags] at actual
end ActualLookups
end Tests.NativeRuntimePool
