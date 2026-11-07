import Airbender.Review.Circuits.ReducedMachine.InitializationOrderingTheorems
import Airbender.Proofs.ReducedMachine.NativeCSRPositiveWitness

namespace Airbender.Tests.NativeInitializationOrdering
open Airbender.NativeInitializationOrdering Airbender.NativeInitializationOrderingProofs
open Airbender.ReducedMachine.Native Airbender.ReducedMachine.NativeMainAuxiliary
open Airbender.ReducedMachine.NativeMemoryBoundary Airbender.Blake2Worker.Native
set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false

private abbrev csr := Airbender.ReducedMachine.NativeCSRPositiveWitness.assignment

theorem actual_geometry : importedConstraintsArgumentColumns.addressAux = #v[122,123] ∧
    importedConstraintsArgumentColumns.addressBorrows = #v[124,125] ∧
    callerAuxiliaryLayout.traceLength-2 = 8388606 := ⟨geometry.2.1,geometry.2.2⟩

theorem one_outer_scaling : lowTerm (2 : F) 17 18 0 1 = 131070 ∧
    highTerm (2 : F) 12 7 3 1 0 = 2 := by decide +kernel

/-- Complete existing BODY controls; no new full physical/global proof witness. -/
theorem complete_body_controls (active : Bool) :
    (remainder (csr active))[0].val < 65536 ∧ (remainder (csr active))[1].val < 65536 ∧
    ((borrows (csr active))[0] = 0 ∨ (borrows (csr active))[0] = 1) ∧
    ((borrows (csr active))[1] = 0 ∨ (borrows (csr active))[1] = 1) :=
  body_controls (Airbender.ReducedMachine.NativeCSRPositiveWitness.body active)

theorem complete_body_adjacent_observations : AdjacentAccepted (csr true) (csr false) ∧
    address (csr true) = address (csr false) ∧ PaddingRecord (csr true) := by
  refine ⟨⟨by decide +kernel,by decide +kernel⟩,by decide +kernel,?_⟩
  intro column member
  have columns : initializationColumns = [126,127,128,129,130,131] :=
    Airbender.ReducedMachine.NativeMainAuxiliaryProofs.initialization_geometry.2.2.2
  rw [columns] at member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

private def repeated17 (column : Nat) : F := if column = 126 then 17 else 0

/-- Ordering SLICE alone permits equal nonzero addresses; the checked padding
    polynomial is essential. Neither slice asserts accepted native body/global. -/
theorem ordering_slice_repeat : AdjacentAccepted repeated17 repeated17 :=
  ⟨by decide +kernel,by decide +kernel⟩

theorem native_padding_rejects_slice_repeat :
    processingMaskTerm (1 : F) (repeated17 125) (repeated17 126) ≠ 0 := by decide +kernel

private def wideSlice (column : Nat) : F :=
  if column = 126 then 1 else if column = 127 then 2147483646 else
    if column = 122 then 1 else if column = 123 then 65535 else if column = 125 then 1 else 0

/-- A RAW ordering/padding SLICE with wide address is not full native acceptance.
    It prevents accidentally claiming address ranges from these components. -/
theorem raw_wide_slice_limit : AdjacentAccepted wideSlice (fun _ => 0) ∧
    (address wideSlice)[1].val ≥ 65536 ∧ (remainder wideSlice)[0].val < 65536 ∧
      (remainder wideSlice)[1].val < 65536 := by
  exact ⟨⟨by decide +kernel,by decide +kernel⟩,by decide +kernel,by decide +kernel,by decide +kernel⟩

theorem last_two_not_compared : ¬ callerAuxiliaryLayout.traceLength-2 < callerAuxiliaryLayout.traceLength-2 := by decide +kernel

theorem complete_conditional_token_exclusion {R : Type} [Field R] (embed : F →+* R)
    (memory : MemoryKeyChallenges R) (pc : PCChallenges R) {proof : MainProof R}
    (accepted : Airbender.NativeInitializationOrdering.Accepted embed memory pc proof)
    (i : Nat) (bound : i < callerAuxiliaryLayout.traceLength-2)
    (same : (Airbender.NativeMemoryTokens.encodeKey (initializationKey (proof.rows i) true)).address =
      (Airbender.NativeMemoryTokens.encodeKey (initializationKey (proof.rows (i+1)) true)).address) :
    PaddingRecord (proof.rows i) := native_initialization_token_duplicates embed memory pc accepted i bound same

end Airbender.Tests.NativeInitializationOrdering
