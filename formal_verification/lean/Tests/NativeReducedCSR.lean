import Airbender.Review.Circuits.ReducedMachine.CSRTheorems
import Airbender.Review.Circuits.ReducedMachine.Tables.CSRTheorems

namespace Tests.NativeReducedCSR
open Airbender Arithmetic ReducedMachine Native NativeFixed Verification
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

/-- Adjacent unsupported keys are retained, with zero support/delegation. -/
theorem fixture_matrix :
    (#[csrSupported 0,csrSupported 1983,csrSupported 1984,csrSupported 1985,
      csrSupported 1988,csrSupported 1989,csrSupported 1990,csrSupported 4095] : Array Nat) = #[0,0,1,0,1,1,0,0] ∧
    (#[csrDelegated 1984,csrDelegated 1988,csrDelegated 1989] : Array Nat) = #[0,1,1] := by decide +kernel

/-- Every actual CSR fixture row occurs at its full native pool offset. This
    positive table-membership result does not assert a complete accepted row. -/
theorem native_pool_rows (key : Fin 4096) :
    (NativeFixed.table (p := mersenne31Modulus)).Contains #[] ((csrRow key.val).map Nat.cast) := by
  refine ⟨⟨key.val+1507585,by change key.val+1507585<5771521; have := key.isLt; omega⟩,?_⟩
  change _ = (rowNat ⟨key.val+1507585,_⟩).map Nat.cast
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
  rw [rowNat,dif_neg h0,dif_neg h1,dif_neg h2,dif_neg h3,dif_neg h4,dif_neg h5,dif_neg h6,dif_neg h7,dif_neg h8,dif_neg h9,dif_neg h10,dif_pos selected]
  simp only [Nat.add_sub_cancel_right]
  rw [NativeCSRTableProofs.rows]

/-- A stored unsupported key cannot be forged into an allowed CSR. -/
theorem forged_support_rejected : ¬ (NativeFixed.table (p := mersenne31Modulus)).Contains #[] #v[1985,1,0,25] := by
  intro member
  have actual := (csr_properties_implementation member).2.1
  have key : (1985 : ZMod mersenne31Modulus).val = 1985 := by decide +kernel
  rw [key] at actual
  norm_num [csrSupported] at actual

theorem nondeterminism_cannot_delegate : ¬ (NativeFixed.table (p := mersenne31Modulus)).Contains #[] #v[1984,1,1,25] := by
  intro member
  have actual := (csr_properties_implementation member).2.2
  have key : (1984 : ZMod mersenne31Modulus).val = 1984 := by decide +kernel
  rw [key] at actual
  norm_num [csrDelegated] at actual

theorem outside_key_rejected (supported delegated : ZMod mersenne31Modulus) :
    ¬ (NativeFixed.table (p := mersenne31Modulus)).Contains #[] #v[4096,supported,delegated,25] := by
  intro member
  have actual := (csr_properties_implementation member).1
  have key : (4096 : ZMod mersenne31Modulus).val = 4096 := by decide +kernel
  rw [key] at actual
  exact Nat.lt_irrefl _ actual

section ConditionalNative
variable {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints NativeFixed.table))
    (mask : w 12 = (csrMask : ZMod mersenne31Modulus))
include holds mask

theorem unsupported_csr_rejected (unsupported : (w 9).val ≠ 1984 ∧ (w 9).val ≠ 1988 ∧ (w 9).val ≠ 1989) : False := by
  rcases (csr_native_effects holds mask).key with h | h | h
  · exact unsupported.1 h
  · exact unsupported.2.1 h
  · exact unsupported.2.2 h

/-- No nondeterminism stream/value is assumed or identified by this result. -/
theorem nondeterminism_request_zero (key : (w 9).val = 1984) :
    csrRequest w = ⟨0,0,some 0,3⟩ ∧ (csrOracleWord w).Bounded := by
  have actual := csr_native_effects holds mask
  exact ⟨by simpa [key,csrDelegated] using actual.request,actual.oracleBounded⟩

/-- Delegation zero is independent of the rd/x0 write mask. -/
theorem nonzero_delegation_oracle_rejected (key : (w 9).val = 1988 ∨ (w 9).val = 1989)
    (bad : csrOracleWord w ≠ ⟨0,0⟩) : False := by
  have flag : csrDelegated (w 9).val = 1 := by simp [csrDelegated,key]
  exact bad ((csr_native_effects holds mask).delegationZero flag)

/-- A discarded destination does not erase the actual delegation request. -/
theorem discarded_destination_keeps_request (key : (w 9).val = 1988)
    (zero : rdZeroFlag w = 1) : rdWrite w = #v[0,0] ∧ (csrRequest w).multiplicity = 1 := by
  have actual := csr_native_effects holds mask
  constructor
  · rw [actual.written]
    simp [zero,csrCandidate]
  · rw [actual.request]
    simp [key,csrDelegated]

theorem abi_group_retained : (csrRequest w).offsetHigh ≠ none := by
  rw [(csr_native_effects holds mask).request]
  simp

theorem oversized_abi_high_rejected : (w 93).val < 65536 := (csr_native_effects holds mask).offsetBounded

end ConditionalNative

-- Independent partial fixtures for nondeterminism and both delegate keys.
private def sample (scenario : Fin 3) (column : Nat) : ZMod mersenne31Modulus :=
  let key : Nat := #v[1984,1988,1989][scenario]
  let delegate : Nat := if scenario.val = 0 then 0 else 1
  match column with
  | 9 => key | 12 => 129 | 17 | 24 | 64 => 1
  | 36 => 4660 | 65 | 92 => delegate
  | 90 => if scenario.val = 0 then 4660 else 0
  | 91 => if scenario.val = 0 then 43981 else 0
  | 93 => 4660*delegate | 94 => key*delegate
  | _ => 0

private def polynomialValue (scenario : Fin 3) (index : Fin 117) : ZMod mersenne31Modulus :=
  ((FlatOperation.constraints (importedConstraints NativeFixed.table)).get index).eval (environment (sample scenario))

/-- Positive checks of actual six CSR support/request/zero-return equations,
    not all117 equations/22 lookups or initialized reference execution. -/
theorem native_request_slices (scenario : Fin 3) (slot : Fin 6) :
    polynomialValue scenario ⟨68+slot.val,by omega⟩ = 0 := by
  fin_cases scenario <;> fin_cases slot <;> decide +kernel

/-- The independent nondeterminism fixture uses a nonzero bounded return;
    delegated fixtures return zero. No full native witness is claimed. -/
theorem partial_fixture_oracles :
    csrOracleWord (sample 0) = ⟨4660,43981⟩ ∧
    csrOracleWord (sample 1) = ⟨0,0⟩ ∧ csrOracleWord (sample 2) = ⟨0,0⟩ := by decide +kernel

end Tests.NativeReducedCSR
