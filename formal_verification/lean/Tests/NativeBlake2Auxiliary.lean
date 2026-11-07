import Airbender.Review.Circuits.Blake2Worker.AuxiliaryTheorems

namespace Airbender.Tests.NativeBlake2Auxiliary
open Verification Airbender.Blake2Worker Airbender.Blake2Worker.Native Airbender.Blake2Worker.AuxiliaryArtifact
set_option autoImplicit false

abbrev F := ZMod mersenne31Modulus

theorem full_source : auxiliaryLayoutSourceBytes = constraintsSourceBytes := AuxiliaryProofs.same_source

theorem separate_geometry : auxiliaryLayout.processing.start = 1064 ∧
    auxiliaryLayout.width = 1244 ∧ auxiliaryLayout.extensionOffset = 44 ∧
    auxiliaryLayout.grandProduct.start = 1240 := by decide +kernel

theorem last_memory_slot : (memoryAuxiliaryColumn ⟨42,by decide⟩).start = 1236 := by decide +kernel

theorem all_quartic_slots (slot : Fin 43) : (memoryAuxiliaryColumn slot).start % 4 = 0 ∧
    (memoryAuxiliaryColumn slot).start+4 ≤ auxiliaryLayout.grandProduct.start :=
  (AuxiliaryProofs.memory_columns slot).2

theorem ordinary_domain : constraintsABI.traceLength-1 = 1048575 := by decide +kernel

theorem literal_worker_kind_outside_scaling :
    processorArgument (RingHom.id F) ⟨0,0,0,0⟩ (fun _ => 0) 2 = 1991 := by
  simp [processorArgument]

theorem inactive_denominator_not_unit : processorAuxiliaryTerm (0 : F) 0 1 7 = 0 := by
  simp [processorAuxiliaryTerm]

theorem zero_scaling_is_weaker : processorAuxiliaryTerm (3 : F) 1 0 9 = 0 := by
  simp [processorAuxiliaryTerm]

theorem bad_active_processor_aux : processorAuxiliaryTerm (1 : F) 1 1 0 ≠ 0 := by
  decide +kernel

theorem memory_step_zero_factor_boundary : memoryAuxiliaryTerm (1 : F) 1 7 0 0 = 0 ∧ (7 : F) ≠ 1 := by
  decide +kernel

theorem grand_initial_boundary : grandBoundaryTerm (1 : F) 0 1 ≠ 0 := by decide +kernel

theorem grand_terminal_preserves_claim : grandBoundaryTerm (1 : F) 7 7 = 0 ∧
    grandBoundaryTerm (1 : F) 7 1 ≠ 0 := by decide +kernel

theorem chain_positive :
    (30 : F)*(∏ i ∈ Finset.range 3, (fun _ : Nat => (1 : F)) i) =
      ∏ i ∈ Finset.range 3, (fun i => if i = 0 then (2 : F) else if i = 1 then 3 else 5) i := by
  decide +kernel

theorem complete_row_balance {R : Type} [CommRing R] (embed : F →+* R)
    (memory : MemoryKeyChallenges R) (processor : ProcessorChallenges R)
    {w : Nat → F} {aux : QuarticColumn → R} {next : R}
    (accepted : AuxiliaryRowAccepted embed memory processor w aux next) :
    next * memoryKeyProduct embed memory w false = aux auxiliaryLayout.grandProduct * memoryKeyProduct embed memory w true :=
  (auxiliary_row_balance embed memory processor accepted).grand

end Airbender.Tests.NativeBlake2Auxiliary
