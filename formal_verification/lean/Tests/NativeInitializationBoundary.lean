import Airbender.Review.Circuits.ReducedMachine.InitializationBoundaryTheorems
import Airbender.Proofs.ReducedMachine.NativeCSRPositiveWitness

namespace Airbender.Tests.NativeInitializationBoundary
open Airbender.NativeInitializationBoundary Airbender.NativeInitializationBoundaryProofs
open Airbender.NativeInitializationOrdering Airbender.ReducedMachine.Native
open Airbender.ReducedMachine.NativeMemoryBoundary Airbender.Blake2Worker.Native
set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false

private def row (column : Nat) : F := if 126 ≤ column ∧ column ≤ 131 then (column-125 : Nat) else 0
private def limbs : Vector F 6 := #v[1,2,3,4,5,6]
private theorem actual_record : record row = limbs := by decide +kernel
private theorem reference_endpoint {w : Nat → F} : EndpointAccepted w (record w) := by
  intro slot
  simp [term]

theorem actual_geometry : record row = #v[row 126,row 127,row 128,row 129,row 130,row 131] ∧
    scalar16Layout.traceLength-2 = 8388606 := geometry row

theorem public_constant_unscaled : term (2 : F) 7 3 = 11 ∧ term (2 : F) 7 3 ≠ 2*(7-3) := by decide +kernel

theorem all_six_actual_fields : record row = #v[1,2,3,4,5,6] := actual_record

/-- Public-boundary SOURCE SLICE, not complete source/global acceptance. No
    fixed first-address0 is invented from the native binding helper. -/
theorem nonzero_public_record_allowed : EndpointAccepted row limbs ∧ limbs[0] ≠ 0 :=
  ⟨by rw [← actual_record]; exact reference_endpoint,by decide +kernel⟩

theorem changed_address_rejected : ¬ EndpointAccepted row #v[9,2,3,4,5,6] := by
  intro accepted
  have h := accepted 0
  have wrong : term (1 : F) (record row)[0] (#v[(9 : F),2,3,4,5,6])[0] ≠ 0 := by decide +kernel
  exact wrong h

theorem changed_teardown_value_rejected : ¬ EndpointAccepted row #v[1,2,9,4,5,6] := by
  intro accepted
  have h := accepted 2
  have wrong : term (1 : F) (record row)[2] (#v[(1 : F),2,9,4,5,6])[2] ≠ 0 := by decide +kernel
  exact wrong h

theorem changed_teardown_time_rejected : ¬ EndpointAccepted row #v[1,2,3,4,5,9] := by
  intro accepted
  have h := accepted 5
  have wrong : term (1 : F) (record row)[5] (#v[(1 : F),2,3,4,5,9])[5] ≠ 0 := by decide +kernel
  exact wrong h

private def wideTime (column : Nat) : F := if column = 130 then 700000 else 0
/-- Boundary-only raw timestamp SLICE; no absent global enforcement claim. -/
theorem raw_wide_timestamp_retained : EndpointAccepted wideTime (record wideTime) ∧
    (record wideTime)[4].val ≥ 524288 := ⟨reference_endpoint,by decide +kernel⟩

theorem complete_body_zero_boundary (active : Bool) :
    FlatOperation.ConstraintsHoldFlat (Verification.environment (Airbender.ReducedMachine.NativeCSRPositiveWitness.assignment active))
      (importedConstraints Airbender.ReducedMachine.NativeRuntimePool.table) ∧
    EndpointAccepted (Airbender.ReducedMachine.NativeCSRPositiveWitness.assignment active) #v[0,0,0,0,0,0] := by
  refine ⟨Airbender.ReducedMachine.NativeCSRPositiveWitness.body active,?_⟩
  have zero : record (Airbender.ReducedMachine.NativeCSRPositiveWitness.assignment active) = #v[0,0,0,0,0,0] := by
    cases active <;> decide +kernel
  rw [← zero]; exact reference_endpoint

private def rows (i : Nat) : Nat → F := if i = scalar16Layout.traceLength-2 then row else fun _ => 0

theorem last_ordinary_not_normalized : EndpointAccepted (rows (scalar16Layout.traceLength-2)) limbs ∧
    ¬ EndpointAccepted (rows (scalar16Layout.traceLength-1)) limbs := by
  constructor
  · change EndpointAccepted row limbs
    exact nonzero_public_record_allowed.1
  · intro accepted
    have h := accepted 0
    have wrong : term (1 : F) (record (rows (scalar16Layout.traceLength-1)))[0] limbs[0] ≠ 0 := by decide +kernel
    exact wrong h

theorem complete_conditional_interval {R : Type} [Field R] (embed : F →+* R)
    (memory : MemoryKeyChallenges R) (pc : PCChallenges R) (gamma : R)
    {proof : Airbender.NativeScalar16Arguments.Proof R} {values : PublicValues}
    (accepted : Accepted embed memory pc gamma proof values)
    (i : Nat) (bound : i < scalar16Layout.traceLength-1) :
    addressValue values.first ≤ Airbender.NativeInitializationSorted.addressValue (proof.initialization.main.rows i) ∧
      Airbender.NativeInitializationSorted.addressValue (proof.initialization.main.rows i) ≤ addressValue values.oneBeforeLast :=
  (native_initialization_public_interval embed memory pc gamma accepted).2.2 i bound

theorem complete_conditional_strict {R : Type} [Field R] (embed : F →+* R)
    (memory : MemoryKeyChallenges R) (pc : PCChallenges R) (gamma : R)
    {proof : Airbender.NativeScalar16Arguments.Proof R} {values : PublicValues}
    (accepted : Accepted embed memory pc gamma proof values)
    (i : Nat) (bound : i < scalar16Layout.traceLength-2)
    (nonpadding : ¬ PaddingRecord (proof.initialization.main.rows i)) :
    Airbender.NativeInitializationSorted.addressValue (proof.initialization.main.rows i) < addressValue values.oneBeforeLast :=
  strict_terminal embed memory pc gamma accepted i bound nonpadding

end Airbender.Tests.NativeInitializationBoundary
