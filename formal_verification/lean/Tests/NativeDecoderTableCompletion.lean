import Airbender.Review.Trace.Families.ReducedMachine.DecoderTableCompletionTheorems

namespace Airbender.Tests.NativeDecoderTableCompletion
open Airbender.NativeInactiveMain Airbender.NativeDecoderTableCompletion Airbender.NativeDecoderTableCompletionProofs
open Airbender.ReducedMachine Airbender.ReducedMachine.Native
open Airbender.ReducedMachine.NativeMainAuxiliary Airbender.ReducedMachine.NativeMemoryBoundary
open Airbender.Blake2Worker Airbender.Blake2Worker.Native
set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false
abbrev TestF := ZMod mersenne31Modulus

theorem actual_geometry : decoderTableLayout.multiplicity.index = 9 ∧
    decoderTableLayout.access.start = 72 ∧ decoderTableLayout.tableMultiplicity.start = 88 ∧
    decoderTableLayout.traceLength = 8388608 := by decide +kernel

theorem body_nine_is_original_csr : NativeCSRPositiveWitness.assignment false 9 = (1991 : TestF) := by decide +kernel

theorem complete_body_kept : FlatOperation.ConstraintsHoldFlat
    (Verification.environment (NativeCSRPositiveWitness.assignment false)) (importedConstraints NativeRuntimePool.table) :=
  NativeCSRPositiveWitness.body false

theorem same_complete_main {Kind R : Type} [Field R] (publicSetup : Trace.SparseDecoderSetup Kind)
    (main : NativeMainArguments.Proof R) (witness : Nat → DecoderWitnessColumn → TestF)
    (setup : Nat → DecoderSetupColumn → TestF) :
    (withPublicDecoder publicSetup main witness setup).main = main := same_main publicSetup main witness setup

theorem zero_physical_multiplicity_every_index {Kind R : Type} [Field R] (publicSetup : Trace.SparseDecoderSetup Kind)
    (main : NativeMainArguments.Proof R) (witness : Nat → DecoderWitnessColumn → TestF)
    (setup : Nat → DecoderSetupColumn → TestF) (i : Nat) :
    (withPublicDecoder publicSetup main witness setup).witness i decoderTableLayout.multiplicity = 0 :=
  zero_multiplicity publicSetup main witness setup i

theorem other_physical_witness_retained {Kind R : Type} [Field R] (publicSetup : Trace.SparseDecoderSetup Kind)
    (main : NativeMainArguments.Proof R) (witness : Nat → DecoderWitnessColumn → TestF)
    (setup : Nat → DecoderSetupColumn → TestF) (i : Nat) :
    (withPublicDecoder publicSetup main witness setup).witness i ⟨3⟩ = witness i ⟨3⟩ :=
  other_witness publicSetup main witness setup i _ (by decide +kernel)

theorem other_physical_setup_retained {Kind R : Type} [Field R] (publicSetup : Trace.SparseDecoderSetup Kind)
    (main : NativeMainArguments.Proof R) (witness : Nat → DecoderWitnessColumn → TestF)
    (setup : Nat → DecoderSetupColumn → TestF) (i : Nat) :
    (withPublicDecoder publicSetup main witness setup).setup i ⟨0⟩ = setup i ⟨0⟩ :=
  other_setup publicSetup main witness setup i _ (by decide +kernel)

theorem every_public_query_bound {Kind R : Type} [Field R] (publicSetup : Trace.SparseDecoderSetup Kind)
    (main : NativeMainArguments.Proof R) (witness : Nat → DecoderWitnessColumn → TestF)
    (setup : Nat → DecoderSetupColumn → TestF) (i : Nat) :
    NativeDecoderTableArguments.setupQuery (withPublicDecoder publicSetup main witness setup) i =
      NativePhysicalDecoderSetup.normalizedRow publicSetup i := public_query publicSetup main witness setup i

theorem ordinary_public_rows_kept {Kind R : Type} [Field R] (publicSetup : Trace.SparseDecoderSetup Kind)
    (main : NativeMainArguments.Proof R) (witness : Nat → DecoderWitnessColumn → TestF)
    (setup : Nat → DecoderSetupColumn → TestF) (i : Nat) (small : i < decoderTableLayout.traceLength-1) :
    NativeDecoderTableArguments.setupQuery (withPublicDecoder publicSetup main witness setup) i =
      NativePhysicalDecoderSetup.ordinaryRow publicSetup i := by
  rw [public_query,NativePhysicalDecoderSetupProofs.normalized_ordinary publicSetup i small]

theorem public_physical_tail_kept {Kind R : Type} [Field R] (publicSetup : Trace.SparseDecoderSetup Kind)
    (main : NativeMainArguments.Proof R) (witness : Nat → DecoderWitnessColumn → TestF)
    (setup : Nat → DecoderSetupColumn → TestF) (i : Nat) (small : i < decoderTableLayout.traceLength-1)
    (tail : NativePhysicalDecoderSetup.sliceSize publicSetup ≤ i) :
    NativeDecoderTableArguments.setupQuery (withPublicDecoder publicSetup main witness setup) i = Vector.replicate 10 (-1) := by
  rw [ordinary_public_rows_kept publicSetup main witness setup i small]
  exact NativePhysicalDecoderSetupProofs.tail_row publicSetup i tail

theorem reserved_public_setup_normalized {Kind R : Type} [Field R] (publicSetup : Trace.SparseDecoderSetup Kind)
    (main : NativeMainArguments.Proof R) (witness : Nat → DecoderWitnessColumn → TestF)
    (setup : Nat → DecoderSetupColumn → TestF) (column : Fin 10) :
    (NativeDecoderTableArguments.setupQuery (withPublicDecoder publicSetup main witness setup)
      (decoderTableLayout.traceLength-1))[column.val] =
      -(∑ i ∈ Finset.range (decoderTableLayout.traceLength-1), (NativePhysicalDecoderSetup.ordinaryRow publicSetup i)[column.val]) := by
  rw [public_query]
  exact NativePhysicalDecoderSetupProofs.normalized_terminal publicSetup column

theorem independent_decoder_polynomial_zero {Kind R : Type} [Field R] (publicSetup : Trace.SparseDecoderSetup Kind)
    (main : NativeMainArguments.Proof R) (witness : Nat → DecoderWitnessColumn → TestF)
    (setup : Nat → DecoderSetupColumn → TestF) :
    (withPublicDecoder publicSetup main witness setup).polynomial = 0 := zero_polynomial publicSetup main witness setup

theorem same_caller_domain {Kind R : Type} [Field R] (publicSetup : Trace.SparseDecoderSetup Kind)
    (main : NativeMainArguments.Proof R) (witness : Nat → DecoderWitnessColumn → TestF)
    (setup : Nat → DecoderSetupColumn → TestF) :
    (withPublicDecoder publicSetup main witness setup).omega = main.omega := same_omega publicSetup main witness setup

theorem zero_multiplicity_pole_kept : NativeDecoderArguments.accessTerm (1 : TestF) 0 0 7 = 0 := by decide +kernel

theorem nonzero_multiplicity_pole_rejected (aux : TestF) : NativeDecoderArguments.accessTerm 1 0 1 aux ≠ 0 := by
  simp [NativeDecoderArguments.accessTerm]

theorem generic_two_point_zero_difference : NativeDecoderTableArguments.DifferencePolynomialAccepted
    2 (-1 : ℚ) 0 (fun _ => 0) := zero_difference (by decide) (IsPrimitiveRoot.neg_one 0 (by decide))

theorem generic_one_point_zero_difference : NativeDecoderTableArguments.DifferencePolynomialAccepted
    1 (1 : ℚ) 0 (fun _ => 0) := zero_difference (by decide) (IsPrimitiveRoot.one_right_iff.mpr rfl)

theorem actual_old_decoder_columns_zero {R : Type} [Field R] (embed : TestF →+* R) (memory : MemoryKeyChallenges R)
    (pc : PCChallenges R) (ch : CSRArgumentChallenges R) (w : Nat → TestF) :
    NativeInactiveMainProofs.auxiliary embed memory pc ch w decoderTableLayout.tableMultiplicity = 0 ∧
    NativeInactiveMainProofs.auxiliary embed memory pc ch w decoderTableLayout.access = 0 := original_zero_columns embed memory pc ch w

theorem complete_table_without_decoder_nonpoles {Kind R : Type} [Field R] (embed : TestF →+* R)
    (decoder : NativeDecoderArguments.Challenges R) (publicSetup : Trace.SparseDecoderSetup Kind)
    (main : NativeMainArguments.Proof R) (witness : Nat → DecoderWitnessColumn → TestF)
    (setup : Nat → DecoderSetupColumn → TestF)
    (zeros : ∀ i, main.memory.auxiliary i decoderTableLayout.tableMultiplicity = 0 ∧
      main.memory.auxiliary i decoderTableLayout.access = 0)
    (primitive : IsPrimitiveRoot main.omega decoderTableLayout.traceLength) :
    NativeDecoderTableArguments.TableAccepted embed decoder (withPublicDecoder publicSetup main witness setup) :=
  table embed decoder publicSetup main witness setup zeros primitive

theorem full_fixture : ∃ w, NativeDecoderTableCompletion.Fixture w := native_inactive_decoder_table_completion
end Airbender.Tests.NativeDecoderTableCompletion
