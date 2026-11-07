import Airbender.Review.Circuits.ReducedMachine.MemoryBoundaryTheorems

namespace Airbender.Tests.NativeMemoryBoundary
open Verification Airbender.Blake2Worker Airbender.Blake2Worker.Native
open Airbender.ReducedMachine.NativeMemoryBoundary
set_option autoImplicit false

abbrev F := ZMod mersenne31Modulus

private def memory : MemoryKeyChallenges F := ⟨0,0,0,0,0,0,0⟩
private def pc : PCChallenges F := ⟨1,0,0,0⟩
private def refreshedBoundary : PublicBoundary :=
  ⟨fun index => ⟨0,#v[if index.val = 0 then 7 else 0,0]⟩,0,#v[0,0]⟩

theorem all_registers_retained : ((List.finRange 32).map registerInitialKey).length = 32 := by simp

theorem full_rv32_value_split : publicWord 4294967295 = #v[65535,65535] := by decide +kernel

theorem word_split_before_field_reduction : publicWord 2147483647 = #v[65535,32767] ∧
    (2147483647 : F) = 0 := by decide +kernel

theorem initial_pc_timestamp_four : initialPCKey.time = #v[4,0] ∧ initialPCKey.pc = #v[0,0] := by decide +kernel

theorem register_initial_time_zero : (registerInitialKey 0).time = #v[0,0] := rfl

theorem x0_refresh_time_retained : (registerFinalKey refreshedBoundary 0).time = #v[7,0] := by decide +kernel

theorem readonly_x0_value_check_only : BoundaryAccepted (RingHom.id F) memory pc refreshedBoundary ⟨1,1⟩ := by
  constructor
  · rfl
  · decide +kernel
  · decide +kernel

theorem native_register_factor_roles {R : Type} [CommRing R] (embed : F →+* R)
    (ch : MemoryKeyChallenges R) (index : Fin 32) :
    memoryKeyArgument embed ch (registerInitialKey index) =
      1 + ch.addressLow*embed (index.val : F) + ch.gamma :=
  Airbender.ReducedMachine.NativeMemoryBoundaryProofs.initial_register_factor embed ch index

theorem native_pc_low_unscaled : pcArgument (RingHom.id F) (⟨0,0,0,0⟩ : PCChallenges F)
    ⟨#v[17,5],#v[7,9]⟩ = 17 := by decide +kernel

theorem register_pole_rejected (inputs : PublicBoundary) (inverse : BoundaryInverses F)
    (zero : registerProduct (RingHom.id F) memory (registerFinalKey inputs) = 0) :
    ¬ BoundaryAccepted (RingHom.id F) memory pc inputs inverse := by
  intro accepted
  exact (Airbender.ReducedMachine.NativeMemoryBoundaryProofs.boundary_nonzero _ _ _ accepted).1 zero

theorem pc_pole_rejected (inputs : PublicBoundary) (inverse : BoundaryInverses F)
    (zero : pcArgument (RingHom.id F) pc (finalPCKey inputs) = 0) :
    ¬ BoundaryAccepted (RingHom.id F) memory pc inputs inverse := by
  intro accepted
  exact (Airbender.ReducedMachine.NativeMemoryBoundaryProofs.boundary_nonzero _ _ _ accepted).2 zero

theorem scalar_product_not_matching : ([2,3] : List F).prod = ([1,6] : List F).prod ∧
    ([2,3] : List F) ≠ [1,6] := by decide +kernel

theorem complete_conditional_worker_product {Setup R : Type} [Field R]
    (embed : F →+* R) (ch : MemoryKeyChallenges R) (processor : ProcessorChallenges R)
    (config : WorkerConfiguration Setup) {batch : WorkerBatch Setup R}
    (accepted : ConfiguredWorkersAccepted embed ch processor config batch) :
    (batch.outputs.map fun output => output.proof.memoryClaim).prod * workerBatchProduct embed ch batch false =
      workerBatchProduct embed ch batch true :=
  Airbender.ReducedMachine.NativeMemoryBoundaryProofs.worker_products embed ch processor config accepted

theorem complete_conditional_global_balance {Setup R : Type} [Field R]
    (embed : F →+* R) (ch : MemoryKeyChallenges R) (processor : ProcessorChallenges R)
    (state : PCChallenges R) (config : WorkerConfiguration Setup)
    {mains : List R} {batch : WorkerBatch Setup R} {inputs : PublicBoundary} {inverse : BoundaryInverses R}
    (accepted : UnifiedMemoryAccepted embed ch processor state config mains batch inputs inverse) :
    mains.prod * registerProduct embed ch registerInitialKey * pcArgument embed state initialPCKey *
      workerBatchProduct embed ch batch true =
      registerProduct embed ch (registerFinalKey inputs) * pcArgument embed state (finalPCKey inputs) *
      workerBatchProduct embed ch batch false :=
  unified_worker_memory_balance embed ch processor state config accepted

end Airbender.Tests.NativeMemoryBoundary
