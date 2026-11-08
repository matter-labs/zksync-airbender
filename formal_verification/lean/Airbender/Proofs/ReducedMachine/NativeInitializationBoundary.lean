import Airbender.Review.Circuits.ReducedMachine.InitializationBoundary
import Airbender.Proofs.ReducedMachine.NativeInitializationSorted

namespace Airbender.NativeInitializationBoundaryProofs
open Airbender.NativeInitializationBoundary Airbender.NativeInitializationOrdering
open Airbender.ReducedMachine.Native Airbender.ReducedMachine.NativeMainAuxiliary
open Airbender.ReducedMachine.NativeMemoryBoundary Airbender.Blake2Worker.Native
set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false

theorem geometry (w : Nat → F) : record w = #v[w 126,w 127,w 128,w 129,w 130,w 131] ∧
    scalar16Layout.traceLength-2 = 8388606 := by
  constructor
  · simp [record,address,Airbender.ReducedMachine.NativeMainAuxiliaryProofs.initialization_geometry.1,
      Airbender.ReducedMachine.NativeMainAuxiliaryProofs.initialization_geometry.2.1,
      Airbender.ReducedMachine.NativeMainAuxiliaryProofs.initialization_geometry.2.2.1]
  · rfl

theorem unit_scaling {R : Type} [CommRing R] (actual values : R) : term 1 actual values = actual-values := by simp [term]

theorem endpoint {w : Nat → F} {values : Vector F 6} (accepted : EndpointAccepted w values) :
    record w = values := by
  apply Vector.ext
  intro i bound
  exact sub_eq_zero.mp (by simpa only [unit_scaling] using accepted ⟨i,bound⟩)

theorem record_address (w : Nat → F) :
    addressValue (record w) = Airbender.NativeInitializationSorted.addressValue w := rfl

theorem full_endpoints {R : Type} [Field R] (embed : F →+* R)
    (memory : MemoryKeyChallenges R) (pc : PCChallenges R) (gamma : R)
    {proof : Airbender.NativeScalar16Arguments.Proof R} {values : PublicValues}
    (accepted : Accepted embed memory pc gamma proof values) :
    record (proof.initialization.main.rows 0) = values.first ∧
    record (proof.initialization.main.rows (scalar16Layout.traceLength-2)) = values.oneBeforeLast :=
  ⟨endpoint accepted.first,endpoint accepted.oneBeforeLast⟩

theorem public_bounds {R : Type} [Field R] (embed : F →+* R)
    (memory : MemoryKeyChallenges R) (pc : PCChallenges R) (gamma : R)
    {proof : Airbender.NativeScalar16Arguments.Proof R} {values : PublicValues}
    (accepted : Accepted embed memory pc gamma proof values) :
    values.first[0].val < 65536 ∧ values.first[1].val < 65536 ∧
      values.oneBeforeLast[0].val < 65536 ∧ values.oneBeforeLast[1].val < 65536 := by
  obtain ⟨first,last⟩ := full_endpoints embed memory pc gamma accepted
  rw [← first,← last]
  exact ⟨(NativeScalar16LookupProofs.initialization_bounds accepted.scalar.lookups 0 (by decide +kernel)).1,
    (NativeScalar16LookupProofs.initialization_bounds accepted.scalar.lookups 0 (by decide +kernel)).2,
    (NativeScalar16LookupProofs.initialization_bounds accepted.scalar.lookups (scalar16Layout.traceLength-2) (by decide +kernel)).1,
    (NativeScalar16LookupProofs.initialization_bounds accepted.scalar.lookups (scalar16Layout.traceLength-2) (by decide +kernel)).2⟩

theorem public_interval {R : Type} [Field R] (embed : F →+* R)
    (memory : MemoryKeyChallenges R) (pc : PCChallenges R) (gamma : R)
    {proof : Airbender.NativeScalar16Arguments.Proof R} {values : PublicValues}
    (accepted : Accepted embed memory pc gamma proof values) :
    ∀ i < scalar16Layout.traceLength-1,
      addressValue values.first ≤ Airbender.NativeInitializationSorted.addressValue (proof.initialization.main.rows i) ∧
      Airbender.NativeInitializationSorted.addressValue (proof.initialization.main.rows i) ≤ addressValue values.oneBeforeLast := by
  obtain ⟨first,last⟩ := full_endpoints embed memory pc gamma accepted
  have order := (NativeInitializationSortedProofs.full_order embed memory pc gamma accepted.scalar).1
  intro i bound
  rw [← first,← last,record_address,record_address]
  exact ⟨order 0 i (by omega) bound,order i (scalar16Layout.traceLength-2) (by omega) (by decide +kernel)⟩

theorem strict_terminal {R : Type} [Field R] (embed : F →+* R)
    (memory : MemoryKeyChallenges R) (pc : PCChallenges R) (gamma : R)
    {proof : Airbender.NativeScalar16Arguments.Proof R} {values : PublicValues}
    (accepted : Accepted embed memory pc gamma proof values)
    (i : Nat) (bound : i < scalar16Layout.traceLength-2)
    (nonpadding : ¬ PaddingRecord (proof.initialization.main.rows i)) :
    Airbender.NativeInitializationSorted.addressValue (proof.initialization.main.rows i) < addressValue values.oneBeforeLast := by
  rw [← endpoint accepted.oneBeforeLast,record_address]
  exact (NativeInitializationSortedProofs.full_order embed memory pc gamma accepted.scalar).2
    i (scalar16Layout.traceLength-2) bound (by decide +kernel) nonpadding

end Airbender.NativeInitializationBoundaryProofs
