import Airbender.Proofs.ReducedMachine.NativeCallerSumCompletion
import Airbender.Proofs.ReducedMachine.NativePhysicalDecoderSetup
import Airbender.Review.Trace.Families.ReducedMachine.DecoderTableCompletion

namespace Airbender.NativeDecoderTableCompletionProofs
open Airbender.NativeInactiveMain Airbender.NativeDecoderTableCompletion
open Airbender.ReducedMachine Airbender.ReducedMachine.Native
open Airbender.ReducedMachine.NativeMainAuxiliary Airbender.ReducedMachine.NativeMemoryBoundary
open Airbender.Blake2Worker Airbender.Blake2Worker.Native
set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false

/-- Generic polynomial construction before any actual domain sampling. -/
theorem zero_difference {R : Type} [Field R] {n : Nat} {omega : R}
    (positive : 0 < n) (primitive : IsPrimitiveRoot omega n) :
    NativeDecoderTableArguments.DifferencePolynomialAccepted n omega (0 : Polynomial R) (fun _ => 0) := by
  refine ⟨positive,primitive,?_,?_,dvd_zero _⟩
  · simpa only [Polynomial.natDegree_zero] using positive
  · intro _ _
    simp only [Polynomial.eval_zero]

theorem same_main {Kind R : Type} [Field R] (publicSetup : Trace.SparseDecoderSetup Kind)
    (main : NativeMainArguments.Proof R) (witness : Nat → DecoderWitnessColumn → F)
    (setup : Nat → DecoderSetupColumn → F) :
    (withPublicDecoder publicSetup main witness setup).main = main := rfl

theorem zero_multiplicity {Kind R : Type} [Field R] (publicSetup : Trace.SparseDecoderSetup Kind)
    (main : NativeMainArguments.Proof R) (witness : Nat → DecoderWitnessColumn → F)
    (setup : Nat → DecoderSetupColumn → F) (i : Nat) :
    (withPublicDecoder publicSetup main witness setup).witness i decoderTableLayout.multiplicity = 0 := by
  simp [withPublicDecoder,NativePhysicalDecoderSetup.withPublicSetup]

theorem other_witness {Kind R : Type} [Field R] (publicSetup : Trace.SparseDecoderSetup Kind)
    (main : NativeMainArguments.Proof R) (witness : Nat → DecoderWitnessColumn → F)
    (setup : Nat → DecoderSetupColumn → F) (i : Nat) (column : DecoderWitnessColumn)
    (other : column ≠ decoderTableLayout.multiplicity) :
    (withPublicDecoder publicSetup main witness setup).witness i column = witness i column := by
  simp only [withPublicDecoder,NativePhysicalDecoderSetup.withPublicSetup,if_neg other]

theorem public_query {Kind R : Type} [Field R] (publicSetup : Trace.SparseDecoderSetup Kind)
    (main : NativeMainArguments.Proof R) (witness : Nat → DecoderWitnessColumn → F)
    (setup : Nat → DecoderSetupColumn → F) (i : Nat) :
    NativeDecoderTableArguments.setupQuery (withPublicDecoder publicSetup main witness setup) i =
      NativePhysicalDecoderSetup.normalizedRow publicSetup i :=
  NativePhysicalDecoderSetupProofs.bound_decoder_query publicSetup _ i

theorem other_setup {Kind R : Type} [Field R] (publicSetup : Trace.SparseDecoderSetup Kind)
    (main : NativeMainArguments.Proof R) (witness : Nat → DecoderWitnessColumn → F)
    (setup : Nat → DecoderSetupColumn → F) (i : Nat) (column : DecoderSetupColumn)
    (outside : ¬ (decoderTableLayout.setupStart ≤ column.index ∧ column.index < decoderTableLayout.setupStart+10)) :
    (withPublicDecoder publicSetup main witness setup).setup i column = setup i column :=
  NativePhysicalDecoderSetupProofs.bound_other_columns publicSetup _ i column outside

theorem zero_polynomial {Kind R : Type} [Field R] (publicSetup : Trace.SparseDecoderSetup Kind)
    (main : NativeMainArguments.Proof R) (witness : Nat → DecoderWitnessColumn → F)
    (setup : Nat → DecoderSetupColumn → F) :
    (withPublicDecoder publicSetup main witness setup).polynomial = 0 := rfl

theorem same_omega {Kind R : Type} [Field R] (publicSetup : Trace.SparseDecoderSetup Kind)
    (main : NativeMainArguments.Proof R) (witness : Nat → DecoderWitnessColumn → F)
    (setup : Nat → DecoderSetupColumn → F) :
    (withPublicDecoder publicSetup main witness setup).omega = main.omega := rfl

theorem table {Kind R : Type} [Field R] (embed : F →+* R)
    (decoder : NativeDecoderArguments.Challenges R) (publicSetup : Trace.SparseDecoderSetup Kind)
    (main : NativeMainArguments.Proof R) (witness : Nat → DecoderWitnessColumn → F)
    (setup : Nat → DecoderSetupColumn → F)
    (zeros : ∀ i, main.memory.auxiliary i decoderTableLayout.tableMultiplicity = 0 ∧
      main.memory.auxiliary i decoderTableLayout.access = 0)
    (primitive : IsPrimitiveRoot main.omega decoderTableLayout.traceLength) :
    NativeDecoderTableArguments.TableAccepted embed decoder (withPublicDecoder publicSetup main witness setup) := by
  have difference : NativeDecoderTableArguments.difference (withPublicDecoder publicSetup main witness setup) =
      (fun _ => 0) := by
    funext i
    simp only [NativeDecoderTableArguments.difference,same_main,(zeros i).1,(zeros i).2,sub_self]
  refine ⟨?_,?_⟩
  · intro i _
    rw [zero_multiplicity]
    simp only [same_main,(zeros i).1,NativeDecoderArguments.accessTerm,map_zero,mul_zero,sub_self]
  · have polynomial := zero_difference (by decide : 0 < decoderTableLayout.traceLength) primitive
    simpa only [zero_polynomial,same_omega,difference] using polynomial

theorem original_zero_columns {R : Type} [Field R] (embed : F →+* R) (memory : MemoryKeyChallenges R)
    (pc : PCChallenges R) (ch : CSRArgumentChallenges R) (w : Nat → F) :
    NativeInactiveMainProofs.auxiliary embed memory pc ch w decoderTableLayout.tableMultiplicity = 0 ∧
    NativeInactiveMainProofs.auxiliary embed memory pc ch w decoderTableLayout.access = 0 := by
  simp [NativeInactiveMainProofs.auxiliary,decoderTableLayout]

theorem normalized_zero_columns {R : Type} [Field R] (embed : F →+* R) (memory : MemoryKeyChallenges R)
    (pc : PCChallenges R) (ch : CSRArgumentChallenges R) (w : Nat → F)
    (main : NativeMainArguments.Proof R)
    (same : main.memory = Airbender.NativeCallerSumCompletion.normalizedMemory
      (NativeInactiveMainProofs.proof embed memory pc ch w)) (i : Nat) :
    main.memory.auxiliary i decoderTableLayout.tableMultiplicity = 0 ∧
    main.memory.auxiliary i decoderTableLayout.access = 0 := by
  rw [same]
  simp only [Airbender.NativeCallerSumCompletion.normalizedMemory]
  rw [NativeCallerSumCompletionProofs.other_column _ _ _ (by decide +kernel),
    NativeCallerSumCompletionProofs.other_column _ _ _ (by decide +kernel)]
  exact original_zero_columns embed memory pc ch w

theorem fixture : ∃ w, NativeDecoderTableCompletion.Fixture w := by
  let w := NativeCSRPositiveWitness.assignment false
  refine ⟨w,(NativeCSRBodyPaddingProofs.observations false).1,
    (NativeCSRBodyPaddingProofs.observations false).2,?_⟩
  intro Kind R _ embed memory pc ch decoder nonpoles omega primitive publicSetup witness setup
  let base := NativeInactiveMainProofs.proof embed memory pc ch w
  have old : Realizes embed memory pc ch decoder w base :=
    NativeInactiveMainProofs.realizes embed memory pc ch decoder (NativeCSRPositiveWitness.body false)
      (by rfl) (by
        intro column member
        rw [NativeMainAuxiliaryProofs.initialization_geometry.2.2.2] at member
        simp only [List.mem_cons,List.mem_nil_iff,or_false] at member
        rcases member with rfl|rfl|rfl|rfl|rfl|rfl <;> decide +kernel)
      (congrArg CSRRequest.multiplicity (NativeCSRBodyPaddingProofs.observations false).2) nonpoles
  obtain ⟨main,caller⟩ := NativeCallerSumCompletionProofs.complete embed memory pc ch decoder old omega primitive
  have tableAccepted := table embed decoder publicSetup main witness setup
    (normalized_zero_columns embed memory pc ch w main caller.normalized)
    (by rw [caller.domain]; exact primitive)
  have nonzero : main.delegationClaim ≠ 0 := by
    rw [caller.claim]
    exact NativeInactiveMainProofs.request_sum_nonzero embed memory pc ch w nonpoles
  refine ⟨base,main,⟨?_,tableAccepted⟩,?_,nonzero,?_⟩
  · rw [same_main]
    exact caller
  · rw [caller.claim]
    exact NativeInactiveMainProofs.request_sum embed memory pc ch w
  · exact Airbender.Delegation.SumCompletionProofs.not_constant caller.caller.sumPolynomial nonzero
end Airbender.NativeDecoderTableCompletionProofs
