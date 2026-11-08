import Airbender.Review.Circuits.ReducedMachine.InitializationSortedTheorems
import Tests.NativeInitializationOrdering

namespace Airbender.Tests.NativeInitializationSorted
open Airbender.NativeInitializationSorted Airbender.NativeInitializationSortedProofs
open Airbender.NativeInitializationOrdering Airbender.ReducedMachine.Native
open Airbender.ReducedMachine.NativeMainAuxiliary Airbender.ReducedMachine.NativeMemoryBoundary
open Airbender.Blake2Worker.Native
set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false

private def row (lo hi remLo remHi bitLo bitHi : F) (column : Nat) : F :=
  if column = 126 then lo else if column = 127 then hi else
    if column = 122 then remLo else if column = 123 then remHi else
      if column = 124 then bitLo else if column = 125 then bitHi else 0

/-- SOURCE SLICES, not accepted complete body/aux/global/physical witnesses. -/
theorem low_limb_carry_direction :
    AdjacentAccepted (row 1 0 65535 65535 1 1) (row 2 0 0 0 0 0) ∧
    addressValue (row 1 0 65535 65535 1 1) < addressValue (row 2 0 0 0 0 0) := by
  exact ⟨⟨by decide +kernel,by decide +kernel⟩,by decide +kernel⟩

theorem radix_boundary_direction :
    AdjacentAccepted (row 65535 0 65535 65535 0 1) (row 0 1 0 0 0 0) ∧
    addressValue (row 65535 0 65535 65535 0 1) = 65535 ∧
    addressValue (row 0 1 0 0 0 0) = 65536 := by
  exact ⟨⟨by decide +kernel,by decide +kernel⟩,by decide +kernel,by decide +kernel⟩

/-- Full RV32 radix words may exceed M31. No whole-word field cast is used. -/
theorem full_rv32_comparison :
    (borrows (row 65534 65535 65535 65535 1 1))[1] = 1 ∧
    addressValue (row 65534 65535 65535 65535 1 1) = 4294967294 ∧
    addressValue (row 65535 65535 0 0 0 0) = 4294967295 ∧
    AdjacentAccepted (row 65534 65535 65535 65535 1 1) (row 65535 65535 0 0 0 0) := by
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,
    ⟨by decide +kernel,by decide +kernel⟩⟩

/-- Descending source ordering alone is possible; actual padding rejects its
    zero high-borrow together with the nonzero current address. -/
theorem descending_padding_rejection :
    AdjacentAccepted (row 2 0 1 0 0 0) (row 1 0 0 0 0 0) ∧
    processingMaskTerm (1 : F) (row 2 0 1 0 0 0 125) (row 2 0 1 0 0 0 126) ≠ 0 := by
  exact ⟨⟨by decide +kernel,by decide +kernel⟩,by decide +kernel⟩

theorem unsigned_wrap_rejected_by_padding :
    AdjacentAccepted (row 65535 65535 65535 65535 0 0) (row 0 0 0 0 0 0) ∧
    processingMaskTerm (1 : F) (row 65535 65535 65535 65535 0 0 125)
      (row 65535 65535 65535 65535 0 0 127) ≠ 0 := by
  exact ⟨⟨by decide +kernel,by decide +kernel⟩,by decide +kernel⟩

/-- Complete unchanged CSR BODY, plus its actual zero initialization record.
    This is still weaker than complete source/aux/global acceptance. -/
theorem complete_body_repeated_padding (active : Bool) :
    FlatOperation.ConstraintsHoldFlat (Verification.environment (Airbender.ReducedMachine.NativeCSRPositiveWitness.assignment active))
      (importedConstraints Airbender.ReducedMachine.NativeRuntimePool.table) ∧
    addressValue (Airbender.ReducedMachine.NativeCSRPositiveWitness.assignment active) = 0 ∧
    PaddingRecord (Airbender.ReducedMachine.NativeCSRPositiveWitness.assignment active) := by
  refine ⟨Airbender.ReducedMachine.NativeCSRPositiveWitness.body active,?_⟩
  cases active <;> exact ⟨by decide +kernel,by
    intro column member
    have columns := Airbender.ReducedMachine.NativeMainAuxiliaryProofs.initialization_geometry.2.2.2
    rw [columns] at member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel⟩

private def values (i : Nat) : Nat := if i < 2 then 0 else if i = 2 then 17 else if i = 3 then 23 else 29
private theorem small_adjacent : ∀ i, i + 1 < 5 →
    values i ≤ values (i + 1) ∧ (¬ i < 2 → values i < values (i + 1)) := by
  intro i bound
  have upper : i < 4 := by omega
  interval_cases i <;> decide +kernel

/-- Abstract finite-sequence controls only; no native full-domain witness. -/
theorem nonadjacent_strict_growth : values 2 < values 4 :=
  (sequence_order (padding := fun i => i < 2) small_adjacent).2 2 4 (by decide) (by decide) (by decide)

theorem repeated_zero_padding_retained : values 0 = values 1 ∧ values 0 ≤ values 3 :=
  ⟨by decide +kernel,(sequence_order (padding := fun i => i < 2) small_adjacent).1 0 3 (by decide) (by decide)⟩

theorem compared_and_observed_domains : scalar16Layout.traceLength-2 = 8388606 ∧
    scalar16Layout.traceLength-1 = 8388607 ∧
    8388606 < scalar16Layout.traceLength-1 ∧ ¬ 8388606 < scalar16Layout.traceLength-2 := by decide +kernel

theorem complete_conditional_sorted {R : Type} [Field R] (embed : F →+* R)
    (memory : MemoryKeyChallenges R) (pc : PCChallenges R) (gamma : R)
    {proof : Airbender.NativeScalar16Arguments.Proof R}
    (accepted : Airbender.NativeScalar16Lookups.Accepted embed memory pc gamma proof)
    (i j : Nat) (order : i < j) (bound : j < scalar16Layout.traceLength-1)
    (nonpadding : ¬ PaddingRecord (proof.initialization.main.rows i)) :
    addressValue (proof.initialization.main.rows i) < addressValue (proof.initialization.main.rows j) :=
  (native_initialization_sorted embed memory pc gamma accepted).2 i j order bound nonpadding

theorem complete_conditional_unique {R : Type} [Field R] (embed : F →+* R)
    (memory : MemoryKeyChallenges R) (pc : PCChallenges R) (gamma : R)
    {proof : Airbender.NativeScalar16Arguments.Proof R}
    (accepted : Airbender.NativeScalar16Lookups.Accepted embed memory pc gamma proof)
    (i j : Nat) (ib : i < scalar16Layout.traceLength-1) (jb : j < scalar16Layout.traceLength-1)
    (ip : ¬ PaddingRecord (proof.initialization.main.rows i)) (jp : ¬ PaddingRecord (proof.initialization.main.rows j))
    (same : addressValue (proof.initialization.main.rows i) = addressValue (proof.initialization.main.rows j)) : i = j :=
  nonpadding_unique embed memory pc gamma accepted i j ib jb ip jp same

end Airbender.Tests.NativeInitializationSorted
