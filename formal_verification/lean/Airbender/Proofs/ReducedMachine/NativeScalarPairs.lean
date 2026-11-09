import Airbender.Proofs.ReducedMachine.NativeDecoderTableCompletion
import Airbender.Proofs.ReducedMachine.NativeScalar16Arguments
import Airbender.Review.Trace.Families.ReducedMachine.ScalarPairs

namespace Airbender.NativeScalarPairsProofs
open Airbender.NativeInactiveMain Airbender.ReducedMachine Airbender.ReducedMachine.Native
open Airbender.ReducedMachine.NativeMainAuxiliary Airbender.ReducedMachine.NativeMemoryBoundary
open Airbender.Blake2Worker Airbender.Blake2Worker.Native
set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false

open Airbender.NativeScalarPairs

theorem zero_pair_rational {R : Type} [Field R] (gamma : R) :
    NativeInitializationRange.rationalTerm 1 gamma 0 0 0 (2/gamma) = 0 := by
  by_cases zero : gamma = 0
  · simp [NativeInitializationRange.rationalTerm,zero]
  · dsimp only [NativeInitializationRange.rationalTerm]
    field_simp
    ring

theorem kept {R : Type} [Field R] (gamma : R) (aux : QuarticColumn → R)
    (column : QuarticColumn) (other : ¬ PairColumn column) : pairAuxiliary gamma aux column = aux column :=
  if_neg other

theorem row {R : Type} [Field R] (embed : F →+* R) (memory : MemoryKeyChallenges R)
    (pc : PCChallenges R) (gamma : R) {w : Nat → F} {aux : QuarticColumn → R} {next : R}
    (old : RowAccepted embed memory pc w aux next) :
    RowAccepted embed memory pc w (pairAuxiliary gamma aux) next := by
  refine ⟨old.body,?_,?_,?_,old.padding,?_,?_⟩
  · intro slot
    have previous := old.memorySteps slot
    fin_cases slot <;> simpa [mainChainValue,pairAuxiliary,PairColumn,callerAuxiliaryLayout]
      using previous
  · simpa [mainChainValue,pairAuxiliary,PairColumn,callerAuxiliaryLayout] using old.state
  · simpa [pairAuxiliary,PairColumn,callerAuxiliaryLayout] using old.masking
  · simpa [pairAuxiliary,PairColumn,callerAuxiliaryLayout] using old.initialization
  · simpa [pairAuxiliary,PairColumn,callerAuxiliaryLayout] using old.grand

theorem preserves {R : Type} [Field R] (embed : F →+* R) (memory : MemoryKeyChallenges R)
    (pc : PCChallenges R) (ch : CSRArgumentChallenges R)
    (decoder : NativeDecoderArguments.Challenges R) (gamma : R)
    {w : Nat → F} {base : MainProof R} (old : Realizes embed memory pc ch decoder w base) :
    Realizes embed memory pc ch decoder w (pairMemory gamma base) := by
  refine ⟨old.1,old.2.1,⟨?_,?_,?_⟩,?_,?_⟩
  · intro i small
    change RowAccepted embed memory pc (base.rows i) (pairAuxiliary gamma (base.auxiliary i))
      (pairAuxiliary gamma (base.auxiliary (i+1)) callerAuxiliaryLayout.grandProduct)
    rw [kept _ _ _ (by decide +kernel)]
    exact row embed memory pc gamma (old.2.2.1.rows i small)
  · change grandBoundaryTerm 1 (pairAuxiliary gamma (base.auxiliary 0) callerAuxiliaryLayout.grandProduct) 1 = 0
    rw [kept _ _ _ (by decide +kernel)]
    exact old.2.2.1.first
  · change grandBoundaryTerm 1 (pairAuxiliary gamma (base.auxiliary (callerAuxiliaryLayout.traceLength-1)) callerAuxiliaryLayout.grandProduct) base.grandClaim = 0
    rw [kept _ _ _ (by decide +kernel)]
    exact old.2.2.1.last
  · intro i small
    change callerAuxiliaryTerm 1 (csrStageThreeArgument embed ch 1 (base.rows i))
      (embed (csrRequest (base.rows i)).multiplicity)
      (pairAuxiliary gamma (base.auxiliary i) callerAuxiliaryLayout.request) = 0
    rw [kept _ _ _ (by decide +kernel)]
    exact old.2.2.2.1 i small
  · intro i small
    refine ⟨(old.2.2.2.2 i small).body,?_⟩
    change NativeDecoderArguments.accessTerm 1 (NativeDecoderArguments.argument embed decoder 1 (base.rows i))
      (embed (base.rows i importedConstraintsTraceColumns.execute))
      (pairAuxiliary gamma (base.auxiliary i) decoderAuxiliaryLayout.access) = 0
    rw [kept _ _ _ (by decide +kernel)]
    exact (old.2.2.2.2 i small).access

theorem body_pairs_zero (active : Bool) (slot : Fin 4) :
    NativeScalar16Arguments.bodyPair (NativeCSRPositiveWitness.assignment active) slot = #v[0,0] := by
  cases active <;> fin_cases slot <;> decide +kernel

theorem initialization_zero (active : Bool) :
    NativeInitializationOrdering.address (NativeCSRPositiveWitness.assignment active) = #v[0,0] ∧
    NativeInitializationOrdering.remainder (NativeCSRPositiveWitness.assignment active) = #v[0,0] ∧
    NativeInitializationOrdering.borrows (NativeCSRPositiveWitness.assignment active) = #v[0,0] := by
  cases active <;> decide +kernel

theorem body_pair {R : Type} [Field R] (embed : F →+* R) (gamma : R)
    (aux : QuarticColumn → R) (base : BaseAuxiliaryColumn → F) (active : Bool) (slot : Fin 4) :
    NativeScalar16Arguments.BodyPairAccepted embed gamma (NativeCSRPositiveWitness.assignment active)
      (products base) (pairAuxiliary gamma aux) slot := by
  have atProduct : products base (NativeScalar16Arguments.bodyProduct slot) = 0 := by
    apply if_pos
    fin_cases slot <;> decide +kernel
  have atAccumulator : pairAuxiliary gamma aux (NativeScalar16Arguments.bodyAccumulator slot) = 2/gamma := by
    unfold pairAuxiliary
    apply if_pos
    fin_cases slot <;> decide +kernel
  constructor
  · rw [body_pairs_zero,atProduct]
    simp [NativeInitializationRange.productTerm]
  · rw [body_pairs_zero,atProduct,atAccumulator]
    simpa using zero_pair_rational gamma

theorem products_other (base : BaseAuxiliaryColumn → F) (column : BaseAuxiliaryColumn) (large : 5 ≤ column.index) :
    products base column = base column := if_neg (by omega)

theorem initialization_pair {R : Type} [Field R] (embed : F →+* R) (gamma : R)
    (aux : QuarticColumn → R) (base : BaseAuxiliaryColumn → F) (active : Bool) :
    NativeInitializationRange.PairAccepted embed gamma (NativeCSRPositiveWitness.assignment active)
      (products base) (pairAuxiliary gamma aux) := by
  have atProduct : products base initializationRangeLayout.product = 0 := if_pos (by decide +kernel)
  have atAccumulator : pairAuxiliary gamma aux initializationRangeLayout.accumulator = 2/gamma :=
    if_pos (by decide +kernel)
  constructor
  · rw [(initialization_zero active).1,atProduct]
    simp [NativeInitializationRange.productTerm]
  · rw [(initialization_zero active).1,atProduct,atAccumulator]
    simpa using zero_pair_rational gamma

theorem adjacent (active : Bool) : NativeInitializationOrdering.AdjacentAccepted
    (NativeCSRPositiveWitness.assignment active) (NativeCSRPositiveWitness.assignment active) := by
  obtain ⟨address,remainder,borrows⟩ := initialization_zero active
  constructor <;> simp [NativeInitializationOrdering.lowTerm,NativeInitializationOrdering.highTerm,address,remainder,borrows]

theorem body_column (slot : Fin 4) : PairColumn (NativeScalar16Arguments.bodyAccumulator slot) := by
  fin_cases slot <;> decide +kernel

theorem normalized_accumulator {R : Type} [Field R] (gamma : R) (base : MainProof R) (i : Nat)
    (column : QuarticColumn) (pair : PairColumn column) :
    (NativeCallerSumCompletion.normalizedMemory (pairMemory gamma base)).auxiliary i column = 2/gamma := by
  have other : column ≠ callerAuxiliaryLayout.request := by
    intro same
    rw [same] at pair
    exact (by decide +kernel : ¬ PairColumn callerAuxiliaryLayout.request) pair
  change NativeCallerSumCompletion.normalizedAuxiliary (pairMemory gamma base) i column = _
  rw [NativeCallerSumCompletionProofs.other_column _ _ _ other]
  exact if_pos pair

/-- Entire generic finite observation sum before the concrete native domain. -/
theorem sum_kept {R : Type} [Field R] (n : Nat) (gamma : R) (aux : Nat → QuarticColumn → R)
    (column : QuarticColumn) (other : ¬ PairColumn column) :
    (∑ i ∈ Finset.range n, pairAuxiliary gamma (aux i) column) = ∑ i ∈ Finset.range n, aux i column := by
  apply Finset.sum_congr rfl
  intro i _
  exact kept gamma (aux i) column other

theorem request_sum_kept {R : Type} [Field R] (gamma : R) (base : MainProof R) :
    NativeCallerSumCompletion.requestSum (pairMemory gamma base) = NativeCallerSumCompletion.requestSum base := by
  simpa only [NativeCallerSumCompletion.requestSum,pairMemory] using
    sum_kept (callerAuxiliaryLayout.traceLength-1) gamma base.auxiliary callerAuxiliaryLayout.request (by decide +kernel)

theorem observed_pair_sum {R : Type} [Field R] (gamma : R) (base : MainProof R) (i : Nat) :
    observedPairSum (NativeCallerSumCompletion.normalizedMemory (pairMemory gamma base)) i = 10/gamma := by
  have columns : ∀ slot : Fin 4,
      (NativeCallerSumCompletion.normalizedMemory (pairMemory gamma base)).auxiliary i
        (NativeScalar16Arguments.bodyAccumulator slot) = 2/gamma :=
    fun slot => normalized_accumulator gamma base i _ (body_column slot)
  unfold observedPairSum
  simp_rw [columns]
  rw [normalized_accumulator _ _ _ _ (by decide +kernel)]
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero]
  ring

theorem observed_pair_total {R : Type} [Field R] (gamma : R) (base : MainProof R) :
    (∑ i ∈ Finset.range (scalar16Layout.traceLength-1),
      observedPairSum (NativeCallerSumCompletion.normalizedMemory (pairMemory gamma base)) i) =
      ((scalar16Layout.traceLength-1 : Nat) : R)*(10/gamma) := by
  simp_rw [observed_pair_sum]
  exact NativeInactiveMainProofs.constant_sum _ _

theorem fixture : ∃ w, NativeScalarPairs.Fixture w := by
  let w := NativeCSRPositiveWitness.assignment false
  refine ⟨w,(NativeCSRBodyPaddingProofs.observations false).1,
    (NativeCSRBodyPaddingProofs.observations false).2,?_⟩
  intro Kind R _ embed memory pc ch decoder nonpoles gamma omega primitive publicSetup witness setup base
  let original := NativeInactiveMainProofs.proof embed memory pc ch w
  have old : Realizes embed memory pc ch decoder w original :=
    NativeInactiveMainProofs.realizes embed memory pc ch decoder (NativeCSRPositiveWitness.body false)
      (by rfl) (by
        intro column member
        rw [NativeMainAuxiliaryProofs.initialization_geometry.2.2.2] at member
        simp only [List.mem_cons,List.mem_nil_iff,or_false] at member
        rcases member with rfl|rfl|rfl|rfl|rfl|rfl <;> decide +kernel)
      (congrArg CSRRequest.multiplicity (NativeCSRBodyPaddingProofs.observations false).2) nonpoles
  let before := pairMemory gamma original
  have enriched := preserves embed memory pc ch decoder gamma old
  obtain ⟨main,caller⟩ := NativeCallerSumCompletionProofs.complete embed memory pc ch decoder enriched omega primitive
  have zeros : ∀ i, main.memory.auxiliary i decoderTableLayout.tableMultiplicity = 0 ∧
      main.memory.auxiliary i decoderTableLayout.access = 0 := by
    intro i
    rw [caller.normalized]
    simp only [NativeCallerSumCompletion.normalizedMemory]
    rw [NativeCallerSumCompletionProofs.other_column _ _ _ (by decide +kernel),
      NativeCallerSumCompletionProofs.other_column _ _ _ (by decide +kernel)]
    change pairAuxiliary gamma (original.auxiliary i) decoderTableLayout.tableMultiplicity = 0 ∧
      pairAuxiliary gamma (original.auxiliary i) decoderTableLayout.access = 0
    rw [kept _ _ _ (by decide +kernel),kept _ _ _ (by decide +kernel)]
    exact NativeDecoderTableCompletionProofs.original_zero_columns embed memory pc ch w
  have tables := NativeDecoderTableCompletionProofs.table embed decoder publicSetup main witness setup zeros
    (by rw [caller.domain]; exact primitive)
  have initialization : NativeInitializationRange.Accepted embed memory pc gamma
      ⟨main.memory,fun i => products (base i)⟩ := by
    refine ⟨⟨caller.components.2.2.1,?_⟩,?_⟩
    · intro i _
      rw [caller.components.1]
      exact adjacent false
    · intro i _
      rw [caller.normalized]
      change NativeInitializationRange.PairAccepted embed gamma w (products (base i))
        ((NativeCallerSumCompletion.normalizedMemory (pairMemory gamma original)).auxiliary i)
      have source := initialization_pair embed gamma (original.auxiliary i) (base i) false
      refine ⟨source.product,?_⟩
      rw [normalized_accumulator _ _ _ _ (by decide +kernel)]
      have rational := source.rational
      rw [show pairAuxiliary gamma (original.auxiliary i) initializationRangeLayout.accumulator = 2/gamma from if_pos (by decide +kernel)] at rational
      exact rational
  have bodies : ∀ i < scalar16Layout.traceLength-1, ∀ slot : Fin 4,
      NativeScalar16Arguments.BodyPairAccepted embed gamma (main.memory.rows i)
        (products (base i)) (main.memory.auxiliary i) slot := by
    intro i _ slot
    rw [caller.normalized]
    change NativeScalar16Arguments.BodyPairAccepted embed gamma w (products (base i))
      ((NativeCallerSumCompletion.normalizedMemory (pairMemory gamma original)).auxiliary i) slot
    have source := body_pair embed gamma (original.auxiliary i) (base i) false slot
    refine ⟨source.product,?_⟩
    rw [normalized_accumulator _ _ _ _ (body_column slot)]
    have rational := source.rational
    rw [show pairAuxiliary gamma (original.auxiliary i) (NativeScalar16Arguments.bodyAccumulator slot) = 2/gamma from if_pos (body_column slot)] at rational
    exact rational
  have nonzero : main.delegationClaim ≠ 0 := by
    rw [caller.claim,request_sum_kept]
    exact NativeInactiveMainProofs.request_sum_nonzero embed memory pc ch w nonpoles
  refine ⟨before,main,⟨⟨?_,tables⟩,?_,?_⟩,?_,nonzero,?_⟩
  · rw [NativeDecoderTableCompletionProofs.same_main]
    exact caller
  · simpa only [NativeDecoderTableCompletionProofs.same_main] using initialization
  · simpa only [NativeDecoderTableCompletionProofs.same_main] using bodies
  · rw [caller.claim,request_sum_kept]
    exact NativeInactiveMainProofs.request_sum embed memory pc ch w
  · exact Airbender.Delegation.SumCompletionProofs.not_constant caller.caller.sumPolynomial nonzero

end Airbender.NativeScalarPairsProofs
