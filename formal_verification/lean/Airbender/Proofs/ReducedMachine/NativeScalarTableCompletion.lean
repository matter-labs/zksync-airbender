import Airbender.Proofs.ReducedMachine.NativeScalarPairs
import Airbender.Proofs.ReducedMachine.NativePhysicalScalar16Setup
import Airbender.Review.Trace.Families.ReducedMachine.ScalarTableCompletion

namespace Airbender.NativeScalarTableCompletionProofs
open Airbender.NativeInactiveMain Airbender.ReducedMachine Airbender.ReducedMachine.Native
open Airbender.ReducedMachine.NativeMainAuxiliary Airbender.ReducedMachine.NativeMemoryBoundary
open Airbender.Blake2Worker Airbender.Blake2Worker.Native Airbender.NativeScalarTableCompletion
set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false

theorem spike_sum {R : Type} [AddCommMonoid R] (n : Nat) (positive : 0 < n) (value : R) :
    (∑ i ∈ Finset.range n,spike value i) = value := by
  rw [Finset.sum_eq_single 0]
  · exact if_pos rfl
  · intro i _ other
    exact if_neg other
  · intro absent
    exact False.elim (absent (Finset.mem_range.mpr positive))

theorem difference_total {R : Type} [Field R] (n : Nat) (positive : 0 < n) (value : R) :
    (∑ i ∈ Finset.range n,(spike ((n : R)*value) i - value)) = 0 := by
  rw [Finset.sum_sub_distrib,spike_sum n positive,NativeInactiveMainProofs.constant_sum,sub_self]

theorem normalized_difference {R : Type} [AddCommGroup R] (n : Nat) (table : Nat → R)
    (body : Fin 4 → Nat → R) (initialization : Nat → R) (i : Nat) :
    Verification.normalizeLast n (fun j => table j - ((∑ slot : Fin 4,body slot j) + initialization j)) i =
      Verification.normalizeLast n table i -
        ((∑ slot : Fin 4,Verification.normalizeLast n (body slot) i)+Verification.normalizeLast n initialization i) := by
  by_cases last : i = n-1
  · simp only [Verification.normalizeLast,if_pos last,Finset.sum_sub_distrib,Finset.sum_add_distrib]
    rw [Finset.sum_comm]
    simp only [Finset.sum_neg_distrib]
    abel
  · simp only [Verification.normalizeLast,if_neg last]

theorem ordinary {R : Type} [Field R] (gamma : R) (base : MainProof R) {i : Nat}
    (small : i < scalar16Layout.traceLength-1) :
    normalizedAuxiliary gamma base i = rawAuxiliary gamma
      (spike (((scalar16Layout.traceLength-1 : Nat) : R)*(10/gamma)) i) (base.auxiliary i) := by
  funext column
  unfold normalizedAuxiliary
  split
  · exact Verification.NormalizeLastProofs.ordinary _ small
  · rfl

theorem other_column {R : Type} [Field R] (gamma : R) (base : MainProof R) (i : Nat)
    (column : QuarticColumn) (other : ¬ ScalarColumn column) :
    normalizedAuxiliary gamma base i column = base.auxiliary i column := by
  simp only [ScalarColumn,not_or] at other
  rw [normalizedAuxiliary,if_neg (by exact fun h => h.elim other.1 other.2)]
  rw [rawAuxiliary,if_neg other.2,NativeScalarPairsProofs.kept gamma _ _ other.1]

theorem row {R : Type} [Field R] (embed : F →+* R) (memory : MemoryKeyChallenges R)
    (pc : PCChallenges R) (gamma value : R) {w : Nat → F} {aux : QuarticColumn → R} {next : R}
    (old : RowAccepted embed memory pc w aux next) :
    RowAccepted embed memory pc w (rawAuxiliary gamma value aux) next := by
  have paired := NativeScalarPairsProofs.row embed memory pc gamma old
  refine ⟨old.body,?_,?_,?_,old.padding,?_,?_⟩
  · intro slot
    have previous := paired.memorySteps slot
    fin_cases slot <;> simpa [mainChainValue,rawAuxiliary,callerAuxiliaryLayout,scalar16Layout] using previous
  · simpa [mainChainValue,rawAuxiliary,callerAuxiliaryLayout,scalar16Layout] using paired.state
  · simpa [rawAuxiliary,callerAuxiliaryLayout,scalar16Layout] using paired.masking
  · simpa [rawAuxiliary,callerAuxiliaryLayout,scalar16Layout] using paired.initialization
  · simpa [rawAuxiliary,callerAuxiliaryLayout,scalar16Layout] using paired.grand

theorem preserves {R : Type} [Field R] (embed : F →+* R) (memory : MemoryKeyChallenges R)
    (pc : PCChallenges R) (ch : CSRArgumentChallenges R) (decoder : NativeDecoderArguments.Challenges R)
    (gamma : R) {w : Nat → F} {base : MainProof R} (old : Realizes embed memory pc ch decoder w base) :
    Realizes embed memory pc ch decoder w (normalizedMemory gamma base) := by
  refine ⟨old.1,old.2.1,⟨?_,?_,?_⟩,?_,?_⟩
  · intro i small
    change RowAccepted embed memory pc (base.rows i) (normalizedAuxiliary gamma base i)
      (normalizedAuxiliary gamma base (i+1) callerAuxiliaryLayout.grandProduct)
    rw [ordinary gamma base small,other_column _ _ _ _ (by decide +kernel)]
    exact row embed memory pc gamma _ (old.2.2.1.rows i small)
  · change grandBoundaryTerm 1 (normalizedAuxiliary gamma base 0 callerAuxiliaryLayout.grandProduct) 1 = 0
    rw [other_column _ _ _ _ (by decide +kernel)]
    exact old.2.2.1.first
  · change grandBoundaryTerm 1 (normalizedAuxiliary gamma base (callerAuxiliaryLayout.traceLength-1)
      callerAuxiliaryLayout.grandProduct) base.grandClaim = 0
    rw [other_column _ _ _ _ (by decide +kernel)]
    exact old.2.2.1.last
  · intro i small
    change callerAuxiliaryTerm 1 (csrStageThreeArgument embed ch 1 (base.rows i))
      (embed (csrRequest (base.rows i)).multiplicity) (normalizedAuxiliary gamma base i callerAuxiliaryLayout.request) = 0
    rw [other_column _ _ _ _ (by decide +kernel)]
    exact old.2.2.2.1 i small
  · intro i small
    refine ⟨(old.2.2.2.2 i small).body,?_⟩
    change NativeDecoderArguments.accessTerm 1 (NativeDecoderArguments.argument embed decoder 1 (base.rows i))
      (embed (base.rows i importedConstraintsTraceColumns.execute))
      (normalizedAuxiliary gamma base i decoderAuxiliaryLayout.access) = 0
    rw [other_column _ _ _ _ (by decide +kernel)]
    exact (old.2.2.2.2 i small).access

theorem normalized_column {R : Type} [Field R] (gamma : R) (base : MainProof R) (i : Nat)
    (column : QuarticColumn) (scalar : ScalarColumn column) :
    normalizedAuxiliary gamma base i column = Verification.normalizeLast scalar16Layout.traceLength
      (fun j => rawAuxiliary gamma (spike (((scalar16Layout.traceLength-1 : Nat) : R)*(10/gamma)) j)
        (base.auxiliary j) column) i := if_pos scalar

theorem pair_column {R : Type} [Field R] (gamma : R) (base : MainProof R) (i : Nat)
    (column : QuarticColumn) (pair : NativeScalarPairs.PairColumn column) :
    normalizedAuxiliary gamma base i column =
      Verification.normalizeLast scalar16Layout.traceLength (fun _ => 2/gamma) i := by
  have different : column ≠ scalar16Layout.tableAccumulator := by
    intro same
    rw [same] at pair
    exact (by decide +kernel : ¬ NativeScalarPairs.PairColumn scalar16Layout.tableAccumulator) pair
  rw [normalized_column _ _ _ _ (Or.inl pair)]
  apply congrArg (fun f : Nat → R => Verification.normalizeLast scalar16Layout.traceLength f i)
  funext j
  rw [rawAuxiliary,if_neg different,NativeScalarPairs.pairAuxiliary,if_pos pair]

theorem table_column {R : Type} [Field R] (gamma : R) (base : MainProof R) (i : Nat) :
    normalizedAuxiliary gamma base i scalar16Layout.tableAccumulator =
      Verification.normalizeLast scalar16Layout.traceLength
        (spike (((scalar16Layout.traceLength-1 : Nat) : R)*(10/gamma))) i := by
  rw [normalized_column _ _ _ _ (Or.inr rfl)]
  rfl

theorem amount_embedding {R : Type} [Field R] [DecidableEq R] (embed : F →+* R) (gamma : R) :
    embed (amount gamma) = (if gamma = 0 then 0 else ((scalar16Layout.traceLength-1 : Nat) : R)*10) := by
  classical
  by_cases zero : gamma = 0
  · simp [amount,zero]
  · simp only [amount,if_neg zero,queryAmount]
    rw [map_natCast,Nat.cast_mul,Nat.cast_ofNat]

theorem setup_zero : NativePhysicalScalar16Setup.normalizedValue 0 = 0 := by
  rw [NativePhysicalScalar16SetupProofs.normalized_ordinary 0 (by decide),NativePhysicalScalar16SetupProofs.ordinary_value,if_pos (by decide)]
  rfl

end Airbender.NativeScalarTableCompletionProofs

namespace Airbender.NativeScalarTableCompletionProofs
open Airbender.NativeInactiveMain Airbender.ReducedMachine Airbender.ReducedMachine.Native
open Airbender.ReducedMachine.NativeMainAuxiliary Airbender.ReducedMachine.NativeMemoryBoundary
open Airbender.Blake2Worker Airbender.Blake2Worker.Native Airbender.NativeScalarTableCompletion
set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false

theorem after_caller {R : Type} [Field R] (gamma : R) (base : MainProof R) (i : Nat)
    (column : QuarticColumn) (scalar : ScalarColumn column) :
    (NativeCallerSumCompletion.normalizedMemory (normalizedMemory gamma base)).auxiliary i column =
      normalizedAuxiliary gamma base i column := by
  have other : column ≠ callerAuxiliaryLayout.request := by
    intro same
    rw [same] at scalar
    exact (by decide +kernel : ¬ ScalarColumn callerAuxiliaryLayout.request) scalar
  exact NativeCallerSumCompletionProofs.other_column _ _ _ other

theorem pair_ordinary {R : Type} [Field R] (gamma : R) (base : MainProof R) {i : Nat}
    (small : i < scalar16Layout.traceLength-1) (column : QuarticColumn) (pair : NativeScalarPairs.PairColumn column) :
    (NativeCallerSumCompletion.normalizedMemory (normalizedMemory gamma base)).auxiliary i column = 2/gamma := by
  rw [after_caller _ _ _ _ (Or.inl pair),pair_column _ _ _ _ pair]
  exact Verification.NormalizeLastProofs.ordinary _ small

theorem table_ordinary {R : Type} [Field R] (gamma : R) (base : MainProof R) {i : Nat}
    (small : i < scalar16Layout.traceLength-1) :
    (NativeCallerSumCompletion.normalizedMemory (normalizedMemory gamma base)).auxiliary i scalar16Layout.tableAccumulator =
      spike (((scalar16Layout.traceLength-1 : Nat) : R)*(10/gamma)) i := by
  rw [after_caller _ _ _ _ (Or.inr rfl),table_column]
  exact Verification.NormalizeLastProofs.ordinary _ small

theorem difference_samples {R : Type} [Field R] (gamma : R) (base : MainProof R) (i : Nat) :
    (NativeCallerSumCompletion.normalizedMemory (normalizedMemory gamma base)).auxiliary i scalar16Layout.tableAccumulator-
      NativeScalarPairs.observedPairSum (NativeCallerSumCompletion.normalizedMemory (normalizedMemory gamma base)) i =
        Verification.normalizeLast scalar16Layout.traceLength (rawDifference gamma) i := by
  change _-((∑ slot : Fin 4, _)+_) = _
  rw [after_caller _ _ _ _ (Or.inr rfl),table_column]
  have bodies : ∀ slot : Fin 4,
      (NativeCallerSumCompletion.normalizedMemory (normalizedMemory gamma base)).auxiliary i
        (NativeScalar16Arguments.bodyAccumulator slot) =
      Verification.normalizeLast scalar16Layout.traceLength (fun _ => 2/gamma) i := by
    intro slot
    rw [after_caller _ _ _ _ (Or.inl (NativeScalarPairsProofs.body_column slot))]
    exact pair_column gamma base i _ (NativeScalarPairsProofs.body_column slot)
  simp_rw [bodies]
  rw [after_caller _ _ _ _ (Or.inl (by decide +kernel)),pair_column _ _ _ _ (by decide +kernel)]
  rw [← normalized_difference]
  apply congrArg (fun f : Nat → R => Verification.normalizeLast scalar16Layout.traceLength f i)
  funext j
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,rawDifference]
  ring

theorem polynomial {R : Type} [Field R] (embed : F →+* R) (gamma omega : R)
    (primitive : IsPrimitiveRoot omega scalar16Layout.traceLength) :
    ∃ p, NativeDecoderTableArguments.DifferencePolynomialAccepted scalar16Layout.traceLength omega p
      (Verification.normalizeLast scalar16Layout.traceLength (rawDifference gamma)) := by
  obtain ⟨p,accepted⟩ := Delegation.SumCompletionProofs.normalized_completion
    (by decide : 0 < scalar16Layout.traceLength) primitive
    (NativeCallerSumCompletionProofs.domain_nonzero embed) (rawDifference gamma)
  have total : (∑ i ∈ Finset.range (scalar16Layout.traceLength-1),rawDifference gamma i) = 0 :=
    difference_total _ (by decide) (10/gamma)
  rw [total] at accepted
  refine ⟨p,accepted.positive,accepted.primitive,accepted.degree,accepted.samples,?_⟩
  simpa only [zero_mul,Polynomial.C_0,mul_zero,add_zero] using accepted.boundary

theorem table_row {R : Type} [Field R] (embed : F →+* R) (gamma : R) (base : MainProof R)
    (i : Nat) (small : i < scalar16Layout.traceLength-1) :
    NativeScalar16Arguments.tableTerm 1 gamma (embed (NativePhysicalScalar16Setup.normalizedValue i))
      (embed (spike (amount gamma) i))
      ((NativeCallerSumCompletion.normalizedMemory (normalizedMemory gamma base)).auxiliary i scalar16Layout.tableAccumulator) = 0 := by
  classical
  rw [table_ordinary _ _ small]
  by_cases first : i = 0
  · subst i
    rw [setup_zero]
    simp [spike,NativeScalar16Arguments.tableTerm]
    rw [amount_embedding]
    by_cases zero : gamma = 0
    · simp [zero]
    · rw [if_neg zero]
      field_simp
      ring
  · simp [spike,first,NativeScalar16Arguments.tableTerm]

end Airbender.NativeScalarTableCompletionProofs

namespace Airbender.NativeScalarTableCompletionProofs
open Airbender.NativeInactiveMain Airbender.ReducedMachine Airbender.ReducedMachine.Native
open Airbender.ReducedMachine.NativeMainAuxiliary Airbender.ReducedMachine.NativeMemoryBoundary
open Airbender.Blake2Worker Airbender.Blake2Worker.Native Airbender.NativeScalarTableCompletion
set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false

theorem sum_kept {R : Type} [Field R] (n : Nat) (gamma : R) (base : MainProof R)
    (column : QuarticColumn) (other : ¬ ScalarColumn column) :
    (∑ i ∈ Finset.range n,normalizedAuxiliary gamma base i column) =
      ∑ i ∈ Finset.range n,base.auxiliary i column := by
  apply Finset.sum_congr rfl
  intro i _
  exact other_column gamma base i column other

theorem request_sum_kept {R : Type} [Field R] (gamma : R) (base : MainProof R) :
    NativeCallerSumCompletion.requestSum (normalizedMemory gamma base) = NativeCallerSumCompletion.requestSum base := by
  simpa only [NativeCallerSumCompletion.requestSum,normalizedMemory] using
    sum_kept (callerAuxiliaryLayout.traceLength-1) gamma base callerAuxiliaryLayout.request (by decide +kernel)

theorem fixture : ∃ w, NativeScalarTableCompletion.Fixture w := by
  let w := NativeCSRPositiveWitness.assignment false
  refine ⟨w,(NativeCSRBodyPaddingProofs.observations false).1,
    (NativeCSRBodyPaddingProofs.observations false).2,?_⟩
  intro Kind R _ embed memory pc ch decoder nonpoles gamma omega primitive publicSetup decoderWitness decoderSetup base witness setup
  let original := NativeInactiveMainProofs.proof embed memory pc ch w
  have old : Realizes embed memory pc ch decoder w original :=
    NativeInactiveMainProofs.realizes embed memory pc ch decoder (NativeCSRPositiveWitness.body false)
      (by rfl) (by
        intro column member
        rw [NativeMainAuxiliaryProofs.initialization_geometry.2.2.2] at member
        simp only [List.mem_cons,List.mem_nil_iff,or_false] at member
        rcases member with rfl|rfl|rfl|rfl|rfl|rfl <;> decide +kernel)
      (congrArg CSRRequest.multiplicity (NativeCSRBodyPaddingProofs.observations false).2) nonpoles
  let before := normalizedMemory gamma original
  have enriched := preserves embed memory pc ch decoder gamma old
  obtain ⟨main,caller⟩ := NativeCallerSumCompletionProofs.complete embed memory pc ch decoder enriched omega primitive
  have pairAt (i : Nat) (small : i < scalar16Layout.traceLength-1) (column : QuarticColumn)
      (pair : NativeScalarPairs.PairColumn column) : main.memory.auxiliary i column = 2/gamma := by
    rw [caller.normalized]
    exact pair_ordinary gamma original small column pair
  have zeros : ∀ i, main.memory.auxiliary i decoderTableLayout.tableMultiplicity = 0 ∧
      main.memory.auxiliary i decoderTableLayout.access = 0 := by
    intro i
    rw [caller.normalized]
    simp only [NativeCallerSumCompletion.normalizedMemory]
    rw [NativeCallerSumCompletionProofs.other_column _ _ _ (by decide +kernel),
      NativeCallerSumCompletionProofs.other_column _ _ _ (by decide +kernel)]
    change normalizedAuxiliary gamma original i decoderTableLayout.tableMultiplicity = 0 ∧
      normalizedAuxiliary gamma original i decoderTableLayout.access = 0
    rw [other_column _ _ _ _ (by decide +kernel),other_column _ _ _ _ (by decide +kernel)]
    exact NativeDecoderTableCompletionProofs.original_zero_columns embed memory pc ch w
  have tables := NativeDecoderTableCompletionProofs.table embed decoder publicSetup main decoderWitness decoderSetup zeros
    (by rw [caller.domain]; exact primitive)
  have initialization : NativeInitializationRange.Accepted embed memory pc gamma
      ⟨main.memory,fun i => NativeScalarPairs.products (base i)⟩ := by
    refine ⟨⟨caller.components.2.2.1,?_⟩,?_⟩
    · intro i _
      rw [caller.components.1]
      exact NativeScalarPairsProofs.adjacent false
    · intro i small
      rw [caller.components.1]
      have source := NativeScalarPairsProofs.initialization_pair embed gamma (original.auxiliary i) (base i) false
      refine ⟨source.product,?_⟩
      rw [pairAt i small _ (by decide +kernel)]
      have rational := source.rational
      rw [show NativeScalarPairs.pairAuxiliary gamma (original.auxiliary i) initializationRangeLayout.accumulator = 2/gamma from if_pos (by decide +kernel)] at rational
      exact rational
  have bodies : ∀ i < scalar16Layout.traceLength-1, ∀ slot : Fin 4,
      NativeScalar16Arguments.BodyPairAccepted embed gamma (main.memory.rows i)
        (NativeScalarPairs.products (base i)) (main.memory.auxiliary i) slot := by
    intro i small slot
    rw [caller.components.1]
    have source := NativeScalarPairsProofs.body_pair embed gamma (original.auxiliary i) (base i) false slot
    refine ⟨source.product,?_⟩
    rw [pairAt i small _ (NativeScalarPairsProofs.body_column slot)]
    have rational := source.rational
    rw [show NativeScalarPairs.pairAuxiliary gamma (original.auxiliary i) (NativeScalar16Arguments.bodyAccumulator slot) = 2/gamma from if_pos (NativeScalarPairsProofs.body_column slot)] at rational
    exact rational
  obtain ⟨p,poly⟩ := polynomial embed gamma omega primitive
  have fullScalar : NativeScalar16Arguments.Accepted embed memory pc gamma (scalarView gamma main base witness setup p omega) := by
    refine ⟨initialization,bodies,?_,?_⟩
    · intro i small
      change NativeScalar16Arguments.tableTerm 1 gamma (embed (NativePhysicalScalar16Setup.normalizedValue i))
        (embed (spike (amount gamma) i)) (main.memory.auxiliary i scalar16Layout.tableAccumulator) = 0
      rw [caller.normalized]
      exact table_row embed gamma original i small
    · refine ⟨poly.positive,poly.primitive,poly.degree,?_,poly.boundary⟩
      intro i small
      change p.eval (omega ^ i) = main.memory.auxiliary i scalar16Layout.tableAccumulator - NativeScalarPairs.observedPairSum main.memory i
      rw [poly.samples i small]
      rw [caller.normalized]
      exact (difference_samples gamma original i).symm
  have nonzero : main.delegationClaim ≠ 0 := by
    rw [caller.claim,request_sum_kept]
    exact NativeInactiveMainProofs.request_sum_nonzero embed memory pc ch w nonpoles
  refine ⟨before,main,p,⟨⟨⟨?_,tables⟩,?_,?_⟩,?_⟩,?_,nonzero,?_⟩
  · rw [NativeDecoderTableCompletionProofs.same_main]
    exact caller
  · simpa only [NativeDecoderTableCompletionProofs.same_main] using initialization
  · simpa only [NativeDecoderTableCompletionProofs.same_main] using bodies
  · simpa only [NativeDecoderTableCompletionProofs.same_main] using fullScalar
  · rw [caller.claim,request_sum_kept]
    exact NativeInactiveMainProofs.request_sum embed memory pc ch w
  · exact Delegation.SumCompletionProofs.not_constant caller.caller.sumPolynomial nonzero

theorem pair_terminal {R : Type} [Field R] (gamma : R) (base : MainProof R)
    (column : QuarticColumn) (pair : NativeScalarPairs.PairColumn column) :
    normalizedAuxiliary gamma base (scalar16Layout.traceLength-1) column =
      -(((scalar16Layout.traceLength-1 : Nat) : R)*(2/gamma)) := by
  rw [pair_column _ _ _ _ pair,Verification.NormalizeLastProofs.terminal,NativeInactiveMainProofs.constant_sum]

theorem table_terminal {R : Type} [Field R] (gamma : R) (base : MainProof R) :
    normalizedAuxiliary gamma base (scalar16Layout.traceLength-1) scalar16Layout.tableAccumulator =
      -(((scalar16Layout.traceLength-1 : Nat) : R)*(10/gamma)) := by
  rw [table_column,Verification.NormalizeLastProofs.terminal,spike_sum _ (by decide)]

theorem normalized_column_sum {R : Type} [Field R] (gamma : R) (base : MainProof R)
    (column : QuarticColumn) (scalar : ScalarColumn column) :
    (∑ i ∈ Finset.range scalar16Layout.traceLength,normalizedAuxiliary gamma base i column) = 0 := by
  simp_rw [normalized_column gamma base _ column scalar]
  exact Verification.NormalizeLastProofs.domain_sum (by decide) _

end Airbender.NativeScalarTableCompletionProofs
