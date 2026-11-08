import Airbender.Review.Circuits.ReducedMachine.Scalar16LookupTheorems
import Tests.NativeScalar16Arguments

namespace Airbender.Tests.NativePhysicalScalar16Setup
open Airbender.NativePhysicalScalar16Setup Airbender.NativePhysicalScalar16SetupProofs
open Airbender.NativeScalar16Arguments Airbender.ReducedMachine.Native
set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false
private noncomputable def data : Proof F := Airbender.Tests.NativeScalar16Arguments.observed

theorem actual_geometry : scalar16Layout.traceLength-1 = 8388607 ∧ scalar16Layout.setup.index = 0 := by decide +kernel

theorem actual_prefix : ordinaryValue 0 = 0 ∧ ordinaryValue 65535 = 65535 := by
  constructor <;> rw [ordinary_value] <;> decide +kernel

theorem complete_zero_tail : ∀ i, 65536 ≤ i → ordinaryValue i = 0 := ordinary_tail

theorem last_ordinary_zero : normalizedValue 8388606 = 0 := by
  rw [normalized_ordinary _ (by decide),ordinary_tail _ (by decide)]

theorem literal_membership : table.Contains #[] #v[(0 : F)] ∧ table.Contains #[] #v[(65535 : F)] :=
  ⟨(membership 0).mpr (by decide +kernel),(membership 65535).mpr (by decide +kernel)⟩

theorem wide_value_rejected : ¬ table.Contains #[] #v[(70000 : F)] := by
  intro member
  have bound := (membership 70000).mp member
  exact (by decide +kernel : ¬ (70000 : F).val < 65536) bound

theorem full_column_sum :
    (∑ i ∈ Finset.range scalar16Layout.traceLength,normalizedValue i) = 0 := normalized_sum

theorem closed_last : normalizedValue (scalar16Layout.traceLength-1) = 32767 := normalized_terminal

theorem source_normalization (i : Nat) :
    Verification.normalizeLast scalar16Layout.traceLength ordinaryValue i = normalizedValue i := normalized_reference i

theorem constructed_prefix_observation : (withPublicSetup data).setup 65535 scalar16Layout.setup = 65535 := by
  rw [bound_setup,normalized_ordinary _ (by decide),ordinary_value]
  decide +kernel

theorem other_setup_and_main_retained : (withPublicSetup data).setup 65535 ⟨1⟩ = 1 ∧
    (withPublicSetup data).initialization = data.initialization ∧
    (withPublicSetup data).witness = data.witness ∧ (withPublicSetup data).polynomial = data.polynomial := by
  refine ⟨?_,rfl,rfl,rfl⟩
  exact bound_other_setup data _ ⟨1⟩ (by decide)
end Airbender.Tests.NativePhysicalScalar16Setup
