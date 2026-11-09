import Airbender.Review.Trace.Families.ReducedMachine.ScalarTableCompletionTheorems

namespace Airbender.Tests.NativeScalarTableCompletion
open Airbender.NativeInactiveMain Airbender.NativeScalarTableCompletion Airbender.NativeScalarTableCompletionProofs
open Airbender.ReducedMachine Airbender.ReducedMachine.Native
open Airbender.ReducedMachine.NativeMainAuxiliary Airbender.ReducedMachine.NativeMemoryBoundary
open Airbender.Blake2Worker Airbender.Blake2Worker.Native
set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false
abbrev TestF := ZMod mersenne31Modulus

theorem actual_typed_geometry : scalar16Layout.multiplicity.index = 7 ∧
    scalar16Layout.tableAccumulator.start = 76 ∧ scalar16Layout.setup.index = 0 := by decide +kernel

theorem actual_query_amount : queryAmount.val = 83886070 := by decide +kernel

theorem zero_challenge_amount {R : Type} [Field R] : amount (0 : R) = 0 := by simp [amount]

theorem nonzero_challenge_amount {R : Type} [Field R] (gamma : R) (nonzero : gamma ≠ 0) :
    amount gamma = queryAmount := by simp [amount,nonzero]

theorem physical_multiplicity_is_not_body_seven : NativeCSRPositiveWitness.assignment false 7 = (0 : TestF) ∧
    amount (1 : TestF) = 83886070 := by
  constructor
  · decide +kernel
  · rw [nonzero_challenge_amount _ (by decide +kernel)]
    decide +kernel

theorem spike_first : spike (3 : TestF) 0 = 3 := by decide +kernel

theorem full_spike_sum (value : TestF) : (∑ i ∈ Finset.range 2,spike value i) = value := spike_sum 2 (by decide) value

theorem actual_first_difference : rawDifference (1 : TestF) 0 = 83886060 := by
  change (8388607 : TestF)*(10/1) - 10/1 = 83886060
  decide +kernel

theorem actual_later_difference : rawDifference (1 : TestF) 1 = -10 := by simp [rawDifference,spike]

theorem zero_challenge_difference {R : Type} [Field R] (i : Nat) : rawDifference (0 : R) i = 0 := by
  simp [rawDifference,spike]

theorem ordinary_pair_unchanged {R : Type} [Field R] (gamma : R) (base : MainProof R) {i : Nat}
    (small : i < scalar16Layout.traceLength-1) :
    (NativeCallerSumCompletion.normalizedMemory (normalizedMemory gamma base)).auxiliary i
      scalar16Layout.initializationAccumulator = 2/gamma := pair_ordinary gamma base small _ (by decide +kernel)

theorem actual_reserved_pair {R : Type} [Field R] (gamma : R) (base : MainProof R) :
    normalizedAuxiliary gamma base (scalar16Layout.traceLength-1) scalar16Layout.initializationAccumulator =
      -(((scalar16Layout.traceLength-1 : Nat) : R)*(2/gamma)) := pair_terminal gamma base _ (by decide +kernel)

theorem actual_reserved_table {R : Type} [Field R] (gamma : R) (base : MainProof R) :
    normalizedAuxiliary gamma base (scalar16Layout.traceLength-1) scalar16Layout.tableAccumulator =
      -(((scalar16Layout.traceLength-1 : Nat) : R)*(10/gamma)) := table_terminal gamma base

theorem all_six_column_sums_zero {R : Type} [Field R] (gamma : R) (base : MainProof R)
    (column : QuarticColumn) (scalar : ScalarColumn column) :
    (∑ i ∈ Finset.range scalar16Layout.traceLength,normalizedAuxiliary gamma base i column) = 0 :=
  normalized_column_sum gamma base column scalar

theorem caller_aux_retained {R : Type} [Field R] (gamma : R) (base : MainProof R) (i : Nat) :
    normalizedAuxiliary gamma base i callerAuxiliaryLayout.request = base.auxiliary i callerAuxiliaryLayout.request :=
  other_column gamma base i _ (by decide +kernel)

theorem grand_aux_retained {R : Type} [Field R] (gamma : R) (base : MainProof R) (i : Nat) :
    normalizedAuxiliary gamma base i callerAuxiliaryLayout.grandProduct = base.auxiliary i callerAuxiliaryLayout.grandProduct :=
  other_column gamma base i _ (by decide +kernel)

theorem both_decoder_aux_retained {R : Type} [Field R] (gamma : R) (base : MainProof R) (i : Nat) :
    normalizedAuxiliary gamma base i decoderTableLayout.access = base.auxiliary i decoderTableLayout.access ∧
    normalizedAuxiliary gamma base i decoderTableLayout.tableMultiplicity = base.auxiliary i decoderTableLayout.tableMultiplicity :=
  ⟨other_column gamma base i _ (by decide +kernel),other_column gamma base i _ (by decide +kernel)⟩

theorem every_ordinary_table_equation {R : Type} [Field R] (embed : TestF →+* R) (gamma : R)
    (base : MainProof R) (i : Nat) (small : i < scalar16Layout.traceLength-1) :
    NativeScalar16Arguments.tableTerm 1 gamma (embed (NativePhysicalScalar16Setup.normalizedValue i))
      (embed (spike (amount gamma) i))
      ((NativeCallerSumCompletion.normalizedMemory (normalizedMemory gamma base)).auxiliary i scalar16Layout.tableAccumulator) = 0 :=
  table_row embed gamma base i small

theorem zero_multiplicity_pole_retained (accumulator : TestF) :
    NativeScalar16Arguments.tableTerm 1 0 0 0 accumulator = 0 := by simp [NativeScalar16Arguments.tableTerm]

theorem nonzero_multiplicity_pole_rejected : NativeScalar16Arguments.tableTerm (1 : TestF) 0 0 83886070 0 ≠ 0 := by decide +kernel

theorem wrong_positive_accumulator_rejected : NativeScalar16Arguments.tableTerm (1 : TestF) 1 0 0 1 ≠ 0 := by decide +kernel

theorem actual_setup_pole_retained (accumulator : TestF) :
    NativeScalar16Arguments.tableTerm 1 (-1) (NativePhysicalScalar16Setup.normalizedValue 1) 0 accumulator = 0 := by
  have value : NativePhysicalScalar16Setup.normalizedValue 1 = 1 := by
    rw [NativePhysicalScalar16SetupProofs.normalized_ordinary 1 (by decide),NativePhysicalScalar16SetupProofs.ordinary_value,if_pos (by decide)]
    rfl
  rw [value]
  simp [NativeScalar16Arguments.tableTerm]

theorem same_actual_main {R : Type} [Field R] (gamma : R) (main : NativeMainArguments.Proof R)
    (base : Nat → BaseAuxiliaryColumn → TestF) (witness : Nat → Scalar16WitnessColumn → TestF)
    (setup : Nat → Scalar16SetupColumn → TestF) (p : Polynomial R) (omega : R) :
    (scalarView gamma main base witness setup p omega).initialization.main = main.memory := rfl

theorem other_physical_witness_retained {R : Type} [Field R] (gamma : R) (main : NativeMainArguments.Proof R)
    (base : Nat → BaseAuxiliaryColumn → TestF) (witness : Nat → Scalar16WitnessColumn → TestF)
    (setup : Nat → Scalar16SetupColumn → TestF) (p : Polynomial R) (omega : R) (i : Nat) :
    (scalarView gamma main base witness setup p omega).witness i ⟨8⟩ = witness i ⟨8⟩ := rfl

theorem actual_public_setup_bound {R : Type} [Field R] (gamma : R) (main : NativeMainArguments.Proof R)
    (base : Nat → BaseAuxiliaryColumn → TestF) (witness : Nat → Scalar16WitnessColumn → TestF)
    (setup : Nat → Scalar16SetupColumn → TestF) (p : Polynomial R) (omega : R) (i : Nat) :
    (scalarView gamma main base witness setup p omega).setup i scalar16Layout.setup =
      NativePhysicalScalar16Setup.normalizedValue i := NativePhysicalScalar16SetupProofs.bound_setup _ i

theorem other_physical_setup_retained {R : Type} [Field R] (gamma : R) (main : NativeMainArguments.Proof R)
    (base : Nat → BaseAuxiliaryColumn → TestF) (witness : Nat → Scalar16WitnessColumn → TestF)
    (setup : Nat → Scalar16SetupColumn → TestF) (p : Polynomial R) (omega : R) (i : Nat) :
    (scalarView gamma main base witness setup p omega).setup i ⟨1⟩ = setup i ⟨1⟩ := rfl

theorem genuine_actual_polynomial_samples {R : Type} [Field R] (embed : TestF →+* R) (gamma omega : R)
    (primitive : IsPrimitiveRoot omega scalar16Layout.traceLength) :
    ∃ p : Polynomial R, ∀ i < scalar16Layout.traceLength,
      p.eval (omega ^ i) = Verification.normalizeLast scalar16Layout.traceLength (rawDifference gamma) i := by
  obtain ⟨p,accepted⟩ := polynomial embed gamma omega primitive
  exact ⟨p,accepted.samples⟩

theorem full_joint_fixture : ∃ w, NativeScalarTableCompletion.Fixture w := native_inactive_scalar_table_completion
end Airbender.Tests.NativeScalarTableCompletion
