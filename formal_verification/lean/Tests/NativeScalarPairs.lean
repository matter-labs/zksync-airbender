import Airbender.Review.Trace.Families.ReducedMachine.ScalarPairsTheorems

namespace Airbender.Tests.NativeScalarPairs
open Airbender.NativeInactiveMain Airbender.NativeScalarPairs Airbender.NativeScalarPairsProofs
open Airbender.ReducedMachine Airbender.ReducedMachine.Native
open Airbender.ReducedMachine.NativeMainAuxiliary Airbender.ReducedMachine.NativeMemoryBoundary
open Airbender.Blake2Worker Airbender.Blake2Worker.Native
set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false
abbrev TestF := ZMod mersenne31Modulus

theorem actual_five_pair_columns :
    PairColumn ⟨12⟩ ∧ PairColumn ⟨16⟩ ∧ PairColumn ⟨20⟩ ∧ PairColumn ⟨24⟩ ∧ PairColumn ⟨28⟩ := by decide +kernel

theorem all_actual_body_queries (active : Bool) (slot : Fin 4) :
    NativeScalar16Arguments.bodyPair (NativeCSRPositiveWitness.assignment active) slot = #v[0,0] := body_pairs_zero active slot

theorem actual_initialization_queries (active : Bool) :
    NativeInitializationOrdering.address (NativeCSRPositiveWitness.assignment active) = #v[0,0] ∧
    NativeInitializationOrdering.remainder (NativeCSRPositiveWitness.assignment active) = #v[0,0] ∧
    NativeInitializationOrdering.borrows (NativeCSRPositiveWitness.assignment active) = #v[0,0] := initialization_zero active

theorem typed_base_four_is_not_execute : NativeCSRPositiveWitness.assignment true 4 = (1 : TestF) ∧
    products (fun _ => (7 : TestF)) ⟨4⟩ = 0 := by decide +kernel

theorem five_products_constructed (base : BaseAuxiliaryColumn → TestF) (slot : Fin 5) :
    products base ⟨slot.val⟩ = 0 := by
  apply if_pos
  exact slot.isLt

theorem other_base_retained (base : BaseAuxiliaryColumn → TestF) : products base ⟨5⟩ = base ⟨5⟩ :=
  products_other base _ (by decide)

theorem caller_aux_retained {R : Type} [Field R] (gamma : R) (aux : QuarticColumn → R) :
    pairAuxiliary gamma aux callerAuxiliaryLayout.request = aux callerAuxiliaryLayout.request := kept gamma aux _ (by decide +kernel)

theorem grand_aux_retained {R : Type} [Field R] (gamma : R) (aux : QuarticColumn → R) :
    pairAuxiliary gamma aux callerAuxiliaryLayout.grandProduct = aux callerAuxiliaryLayout.grandProduct := kept gamma aux _ (by decide +kernel)

theorem decoder_access_retained {R : Type} [Field R] (gamma : R) (aux : QuarticColumn → R) :
    pairAuxiliary gamma aux decoderTableLayout.access = aux decoderTableLayout.access := kept gamma aux _ (by decide +kernel)

theorem decoder_table_retained {R : Type} [Field R] (gamma : R) (aux : QuarticColumn → R) :
    pairAuxiliary gamma aux decoderTableLayout.tableMultiplicity = aux decoderTableLayout.tableMultiplicity := kept gamma aux _ (by decide +kernel)

theorem zero_challenge_constructed : NativeInitializationRange.rationalTerm (1 : TestF) 0 0 0 0 (2/0) = 0 :=
  zero_pair_rational 0

theorem positive_challenge_constructed : NativeInitializationRange.rationalTerm (1 : TestF) 1 0 0 0 2 = 0 := by decide +kernel

theorem wrong_positive_accumulator_rejected : NativeInitializationRange.rationalTerm (1 : TestF) 1 0 0 0 0 ≠ 0 := by decide +kernel

theorem zero_challenge_pole_still_free (accumulator : TestF) :
    NativeInitializationRange.rationalTerm 1 0 0 0 0 accumulator = 0 := by simp [NativeInitializationRange.rationalTerm]

theorem all_body_pair_source_equations {R : Type} [Field R] (embed : TestF →+* R) (gamma : R)
    (aux : QuarticColumn → R) (base : BaseAuxiliaryColumn → TestF) (active : Bool) (slot : Fin 4) :
    NativeScalar16Arguments.BodyPairAccepted embed gamma (NativeCSRPositiveWitness.assignment active)
      (products base) (pairAuxiliary gamma aux) slot := body_pair embed gamma aux base active slot

theorem extra_initialization_pair {R : Type} [Field R] (embed : TestF →+* R) (gamma : R)
    (aux : QuarticColumn → R) (base : BaseAuxiliaryColumn → TestF) (active : Bool) :
    NativeInitializationRange.PairAccepted embed gamma (NativeCSRPositiveWitness.assignment active)
      (products base) (pairAuxiliary gamma aux) := initialization_pair embed gamma aux base active

theorem actual_adjacent_ordering (active : Bool) : NativeInitializationOrdering.AdjacentAccepted
    (NativeCSRPositiveWitness.assignment active) (NativeCSRPositiveWitness.assignment active) := adjacent active

theorem all_five_pair_sum {R : Type} [Field R] (gamma : R) (base : MainProof R) (i : Nat) :
    observedPairSum (NativeCallerSumCompletion.normalizedMemory (pairMemory gamma base)) i = 10/gamma := observed_pair_sum gamma base i

theorem positive_complete_pair_sum (base : MainProof TestF) :
    (∑ i ∈ Finset.range (scalar16Layout.traceLength-1),
      observedPairSum (NativeCallerSumCompletion.normalizedMemory (pairMemory 1 base)) i) = 83886070 := by
  rw [observed_pair_total]
  change (8388607 : TestF)*(10/1) = 83886070
  decide +kernel

theorem zero_challenge_complete_pair_sum {R : Type} [Field R] (base : MainProof R) :
    (∑ i ∈ Finset.range (scalar16Layout.traceLength-1),
      observedPairSum (NativeCallerSumCompletion.normalizedMemory (pairMemory 0 base)) i) = 0 := by
  rw [observed_pair_total]
  simp

theorem caller_sum_retained {R : Type} [Field R] (gamma : R) (base : MainProof R) :
    NativeCallerSumCompletion.requestSum (pairMemory gamma base) = NativeCallerSumCompletion.requestSum base := request_sum_kept gamma base

theorem all_old_components_retained {R : Type} [Field R] (embed : TestF →+* R) (memory : MemoryKeyChallenges R)
    (pc : PCChallenges R) (ch : CSRArgumentChallenges R) (decoder : NativeDecoderArguments.Challenges R) (gamma : R)
    {w : Nat → TestF} {base : MainProof R} (old : Realizes embed memory pc ch decoder w base) :
    Realizes embed memory pc ch decoder w (pairMemory gamma base) := preserves embed memory pc ch decoder gamma old

theorem reserved_pair_is_not_yet_normalized (base : MainProof TestF) :
    (NativeCallerSumCompletion.normalizedMemory (pairMemory 1 base)).auxiliary
      (scalar16Layout.traceLength-1) scalar16Layout.initializationAccumulator = 2 := by
  simpa using normalized_accumulator (1 : TestF) base (scalar16Layout.traceLength-1)
    scalar16Layout.initializationAccumulator (by decide +kernel)

theorem full_joint_fixture : ∃ w, NativeScalarPairs.Fixture w := native_inactive_scalar_pairs
end Airbender.Tests.NativeScalarPairs
