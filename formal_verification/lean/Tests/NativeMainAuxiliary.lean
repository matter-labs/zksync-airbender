import Airbender.Review.Circuits.ReducedMachine.MainAuxiliaryTheorems

namespace Airbender.Tests.NativeMainAuxiliary
open Verification Airbender.ReducedMachine.Native Airbender.ReducedMachine.NativeMemoryBoundary
open Airbender.ReducedMachine.NativeMainAuxiliary Airbender.Blake2Worker Airbender.Blake2Worker.Native
set_option autoImplicit false
abbrev F := ZMod mersenne31Modulus

private theorem map_pair (w : Nat → F) (a b : Nat) :
    (#v[a,b] : Vector Nat 2).map w = #v[w a,w b] := by
  apply Vector.ext
  intro i hi
  have cases : i = 0 ∨ i = 1 := by omega
  rcases cases with rfl | rfl <;> simp

theorem actual_chain_slots : callerAuxiliaryLayout.memory = #[⟨96⟩,⟨100⟩,⟨104⟩] ∧
    callerAuxiliaryLayout.state.start = 108 ∧ callerAuxiliaryLayout.masking.start = 112 ∧
    callerAuxiliaryLayout.initialization.start = 116 ∧ callerAuxiliaryLayout.grandProduct.start = 120 := by decide +kernel

theorem actual_initialization_fields : initializationColumns = [126,127,128,129,130,131] ∧
    importedConstraintsArgumentColumns.addressBorrows[1] = 125 := by decide +kernel

theorem readonly_refresh_retained (w : Nat → F) :
    (mainMemoryKey w 0 true).value = (mainMemoryKey w 0 false).value ∧
    (mainMemoryKey w 0 true).time = #v[w 2,w 3] ∧
    (mainMemoryKey w 0 false).time = #v[w 132,w 133] := by
  constructor
  · rfl
  constructor
  · change #v[w 2+0,w 3] = _
    rw [add_zero]
  · change (#v[132,133] : Vector Nat 2).map w = _
    exact map_pair w 132 133

theorem unmasked_third_write (w : Nat → F) :
    (mainMemoryKey w 2 true).value = #v[w 43,w 44] ∧
    (mainMemoryKey w 2 false).value = #v[w 41,w 42] ∧
    (mainMemoryKey w 2 true).time = #v[w 2+2,w 3] := ⟨rfl,rfl,rfl⟩

theorem raw_register_indicator (w : Nat → F) :
    (mainMemoryKey w 1 false).address = ⟨w 88,w 39,w 40⟩ := rfl

theorem state_fields_retained (w : Nat → F) :
    mainPCKey w false = ⟨#v[w 0,w 1],#v[w 2,w 3]⟩ ∧
    mainPCKey w true = ⟨#v[w 13,w 14],#v[w 15,w 16]⟩ := by
  constructor
  · change (⟨(#v[0,1] : Vector Nat 2).map w,(#v[2,3] : Vector Nat 2).map w⟩ : PCKey) = _
    rw [map_pair,map_pair]
  · change (⟨(#v[13,14] : Vector Nat 2).map w,(#v[15,16] : Vector Nat 2).map w⟩ : PCKey) = _
    rw [map_pair,map_pair]

theorem initialization_unmasked (w : Nat → F) :
    (initializationKey w true).address = ⟨0,w 126,w 127⟩ ∧
    (initializationKey w true).value = #v[0,0] ∧ (initializationKey w true).time = #v[0,0] ∧
    (initializationKey w false).value = #v[w 128,w 129] ∧
    (initializationKey w false).time = #v[w 130,w 131] := by
  refine ⟨rfl,rfl,rfl,?_,?_⟩
  · change (#v[128,129] : Vector Nat 2).map w = _
    exact map_pair w 128 129
  · change (#v[130,131] : Vector Nat 2).map w = _
    exact map_pair w 130 131

theorem active_mask_slice (previous : F) : permutationMaskTerm 1 1 previous previous = 0 := by
  simp [permutationMaskTerm]

theorem inactive_mask_slice (previous : F) : permutationMaskTerm 1 0 previous 1 = 0 := by
  simp [permutationMaskTerm]

theorem nonboolean_mask_slice : permutationMaskTerm (1 : F) 2 3 5 = 0 := by decide +kernel

theorem scaling_boundary : permutationMaskTerm (2 : F) 1 3 3 ≠ 0 := by decide +kernel

theorem native_execute_domain {R : Type} [Field R] (embed : F →+* R)
    (memory : MemoryKeyChallenges R) (pc : PCChallenges R)
    {w : Nat → F} {aux : QuarticColumn → R} {next : R}
    (accepted : RowAccepted embed memory pc w aux next) : w 4 = 0 ∨ w 4 = 1 :=
  Airbender.ReducedMachine.NativeMainAuxiliaryProofs.execute_boolean embed memory pc accepted

theorem native_mask_choice {R : Type} [Field R] (embed : F →+* R)
    (memory : MemoryKeyChallenges R) (pc : PCChallenges R)
    {w : Nat → F} {aux : QuarticColumn → R} {next : R}
    (accepted : RowAccepted embed memory pc w aux next) :
    maskedWrite embed memory pc w = if w 4 = 1 then mainWrite embed memory pc w else mainRead embed memory pc w :=
  Airbender.ReducedMachine.NativeMainAuxiliaryProofs.mask_choice embed memory pc accepted

theorem complete_conditional_padding {R : Type} [Field R] (embed : F →+* R)
    (memory : MemoryKeyChallenges R) (pc : PCChallenges R)
    {w : Nat → F} {aux : QuarticColumn → R} {next : R}
    (accepted : RowAccepted embed memory pc w aux next) :
    w importedConstraintsArgumentColumns.addressBorrows[1] = 0 →
      ∀ column ∈ initializationColumns, w column = 0 :=
  Airbender.ReducedMachine.NativeMainAuxiliaryProofs.initialization_padding embed memory pc accepted

theorem complete_conditional_main {R : Type} [Field R] (embed : F →+* R)
    (memory : MemoryKeyChallenges R) (pc : PCChallenges R) {proof : MainProof R}
    (accepted : Accepted embed memory pc proof) :
    proof.grandClaim*mainRowsProduct embed memory pc proof false = mainRowsProduct embed memory pc proof true :=
  main_auxiliary_product embed memory pc accepted

theorem complete_conditional_global {Setup R : Type} [Field R] (embed : F →+* R)
    (memory : MemoryKeyChallenges R) (processor : ProcessorChallenges R) (pc : PCChallenges R)
    (config : WorkerConfiguration Setup) {mains : List (MainProof R)} {batch : WorkerBatch Setup R}
    {inputs : PublicBoundary} {inverse : BoundaryInverses R}
    (accepted : MainWorkerAccepted embed memory processor pc config mains batch inputs inverse) :
    registerProduct embed memory registerInitialKey * pcArgument embed pc initialPCKey *
      mainBatchProduct embed memory pc mains true * workerBatchProduct embed memory batch true =
      registerProduct embed memory (registerFinalKey inputs) * pcArgument embed pc (finalPCKey inputs) *
      mainBatchProduct embed memory pc mains false * workerBatchProduct embed memory batch false :=
  unified_main_worker_memory_balance embed memory processor pc config accepted

end Airbender.Tests.NativeMainAuxiliary
