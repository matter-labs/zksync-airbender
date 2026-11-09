import Airbender.Review.Trace.Families.ReducedMachine.InactiveMainTheorems

namespace Airbender.Tests.NativeInactiveMain
open Airbender.NativeInactiveMain Airbender.NativeInactiveMainProofs
open Airbender.ReducedMachine Airbender.ReducedMachine.Native Airbender.ReducedMachine.NativeMainAuxiliary
open Airbender.ReducedMachine.NativeMemoryBoundary Airbender.Blake2Worker.Native
set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false
abbrev TestF := ZMod mersenne31Modulus
def w : Nat → TestF := NativeCSRPositiveWitness.assignment false

theorem complete_ordinary_domain : callerAuxiliaryLayout.traceLength-1 = 8388607 := by decide +kernel

theorem generic_chain_retains_two_steps : chain (fun _ => (1 : TestF)) (fun n => if n=0 then 3 else 5) 2 = 15 := by
  decide +kernel

theorem inactive_request_positive : w 4 = 0 ∧ csrRequest w = ⟨1,1991,some 0,3⟩ :=
  NativeCSRBodyPaddingProofs.observations false

theorem complete_body_retained : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
    (importedConstraints NativeRuntimePool.table) := NativeCSRPositiveWitness.body false

theorem raw_alias_timestamps_retained :
    (mainMemoryKey w 0 false).time = #v[0,0] ∧ (mainMemoryKey w 1 false).time = #v[4,0] ∧
    (mainMemoryKey w 2 false).time = #v[5,0] ∧ (mainMemoryKey w 2 true).time = #v[6,0] := by decide +kernel

theorem sample_domain_nonempty {R : Type} [Field R] (embed : TestF →+* R) :
    Nonpoles embed sampleMemory samplePC (sampleCaller embed) w := sample_nonpoles embed

theorem all_memory_rows {R : Type} [Field R] (embed : TestF →+* R)
    (decoder : Airbender.ReducedMachine.NativeDecoderArguments.Challenges R) :
    Accepted embed sampleMemory samplePC (proof embed sampleMemory samplePC (sampleCaller embed) w) :=
  (sample_realizes embed decoder).2.2.1

theorem same_constant_rows {R : Type} [Field R] (embed : TestF →+* R) (i : Nat) :
    (proof embed sampleMemory samplePC (sampleCaller embed) w).rows i = w := rfl

theorem grand_claim_one {R : Type} [Field R] (embed : TestF →+* R) :
    (proof embed sampleMemory samplePC (sampleCaller embed) w).grandClaim = 1 := rfl

theorem all_caller_relations {R : Type} [Field R] (embed : TestF →+* R)
    (decoder : Airbender.ReducedMachine.NativeDecoderArguments.Challenges R) :
    ∀ i < callerAuxiliaryLayout.traceLength-1,
    callerAuxiliaryTerm 1 (csrStageThreeArgument embed (sampleCaller embed) 1 w) (embed (csrRequest w).multiplicity)
      ((proof embed sampleMemory samplePC (sampleCaller embed) w).auxiliary i callerAuxiliaryLayout.request) = 0 :=
  (sample_realizes embed decoder).2.2.2.1

theorem all_decoder_relations {R : Type} [Field R] (embed : TestF →+* R)
    (decoder : Airbender.ReducedMachine.NativeDecoderArguments.Challenges R) :
    ∀ i < decoderAuxiliaryLayout.traceLength-1,
    Airbender.ReducedMachine.NativeDecoderArguments.RowAccepted embed decoder w
      ((proof embed sampleMemory samplePC (sampleCaller embed) w).auxiliary i) :=
  (sample_realizes embed decoder).2.2.2.2

theorem initialization_pole_kept :
    memoryKeyArgument (RingHom.id TestF) sampleMemory (initializationKey w false) = 0 ∧
    memoryKeyArgument (RingHom.id TestF) sampleMemory (initializationKey w true) = 0 := by
  simp [memoryKeyArgument,sampleMemory,initializationKey]

theorem decoder_pole_kept :
    Airbender.ReducedMachine.NativeDecoderArguments.argument (RingHom.id TestF) ⟨Vector.replicate 9 0,0⟩ 1 w = 0 := by
  have low : (decoderQuery w)[0] = (0 : TestF) := by decide +kernel
  simp [Airbender.ReducedMachine.NativeDecoderArguments.argument,low]

theorem caller_pole_rejected (acc : TestF) : callerAuxiliaryTerm 1 0 1 acc ≠ 0 := by
  simp [callerAuxiliaryTerm]

theorem corrupt_inactive_mask_rejected (previous : TestF) : permutationMaskTerm 1 0 previous 0 ≠ 0 := by
  simp [permutationMaskTerm]

theorem corrupt_grand_rejected : grandProductTerm (1 : TestF) 1 1 0 ≠ 0 := by decide +kernel

theorem exact_full_request_sum {R : Type} [Field R] (embed : TestF →+* R) :
    (∑ i ∈ Finset.range (callerAuxiliaryLayout.traceLength-1),
      (proof embed sampleMemory samplePC (sampleCaller embed) w).auxiliary i callerAuxiliaryLayout.request) =
      (8388607 : R)*(csrStageThreeArgument embed (sampleCaller embed) 1 w)⁻¹ :=
  request_sum embed sampleMemory samplePC (sampleCaller embed) w

theorem request_sum_not_zero {R : Type} [Field R] (embed : TestF →+* R) :
    (∑ i ∈ Finset.range (callerAuxiliaryLayout.traceLength-1),
      (proof embed sampleMemory samplePC (sampleCaller embed) w).auxiliary i callerAuxiliaryLayout.request) ≠ 0 :=
  request_sum_nonzero embed sampleMemory samplePC (sampleCaller embed) w (sample_nonpoles embed)

theorem zero_claim_completion_rejected {R : Type} [Field R] (embed : TestF →+* R)
    (polynomial : Polynomial R) (omega : R) :
    ¬ CallerDelegationAccepted embed (sampleCaller embed)
      ⟨(proof embed sampleMemory samplePC (sampleCaller embed) w).rows,
       (proof embed sampleMemory samplePC (sampleCaller embed) w).auxiliary,polynomial,omega,0⟩ :=
  no_zero_claim embed sampleMemory samplePC (sampleCaller embed) w (sample_nonpoles embed) polynomial omega

theorem full_fixture : ∃ row, Fixture row := native_inactive_main_components
end Airbender.Tests.NativeInactiveMain
