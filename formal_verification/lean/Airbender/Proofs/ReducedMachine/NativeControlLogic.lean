import Airbender.Review.Trace.Families.ReducedMachine.ControlLogic
import Airbender.Proofs.ReducedMachine.NativeControlArithmetic
import Airbender.Proofs.ReducedMachine.NativeBitwiseDecodedResult
import Airbender.Proofs.ReducedMachine.NativeComparisonDecodedResult
import Airbender.Proofs.ReducedMachine.NativeBitwiseOperand

namespace Airbender.NativeControlLogicProofs
open Airbender.NativeWorkerSnapshot Airbender.NativeControlHistory
open Airbender.NativeControlLogic Airbender.ReducedMachine Airbender.ReducedMachine.Native
open Airbender.Trace Airbender.Blake2Worker.Native Airbender.ReducedMachine.NativeMemoryBoundary
set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false

private def bitwiseMode (mode : BitwiseMode) : UnifiedMode := Sum.inl (Sum.inr (Sum.inr (Sum.inl mode)))
private def comparisonMode (mode : ComparisonMode) : UnifiedMode := Sum.inl (Sum.inr (Sum.inr (Sum.inr (Sum.inl mode))))

theorem bitwise_projection {instruction : SailRV32.instruction} {data : DecoderData BitwiseMode}
    (fields : bitwiseDecoderFields instruction = some data) :
    unifiedDecoderFields instruction = some (data.mapFamily bitwiseMode) := by
  unfold bitwiseDecoderFields at fields
  split at fields
  all_goals first
    | (solve | cases fields)
    | (simp only [bitwiseFields,Option.some.injEq] at fields
       subst data
       rfl)

theorem comparison_projection {instruction : SailRV32.instruction} {data : DecoderData ComparisonMode}
    (fields : comparisonDecoderFields instruction = some data) :
    unifiedDecoderFields instruction = some (data.mapFamily comparisonMode) := by
  unfold comparisonDecoderFields at fields
  split at fields
  all_goals first
    | (solve | cases fields)
    | (simp only [comparisonFields,Option.some.injEq] at fields
       subst data
       rfl)

theorem bitwise_body {w : Nat → F} {entry : BitwiseProgramEntry}
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints NativeRuntimePool.table))
    (fields : bitwiseDecoderFields entry.instruction = some entry.data) (query : decoderQuery w = entry.query) :
    FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints NativeFixed.table) := by
  exact Airbender.NativeDecodedQueryDomainProofs.fixed_body (entry := entry.mapFamily bitwiseMode) holds
    (bitwise_projection fields) query

theorem comparison_body {w : Nat → F} {entry : ComparisonProgramEntry}
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints NativeRuntimePool.table))
    (fields : comparisonDecoderFields entry.instruction = some entry.data) (query : decoderQuery w = entry.query) :
    FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints NativeFixed.table) := by
  exact Airbender.NativeDecodedQueryDomainProofs.fixed_body (entry := entry.mapFamily comparisonMode) holds
    (comparison_projection fields) query

theorem bitwise_result {w : Nat → F} {entry : BitwiseProgramEntry}
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints NativeRuntimePool.table))
    (fields : bitwiseDecoderFields entry.instruction = some entry.data) (query : decoderQuery w = entry.query) : BitwiseResult w entry := by
  have actual := (NativeBitwiseResultProofs.decoded_result (bitwise_body holds fields query) fields query).2.2.2
  have operand := NativeBitwiseOperandProofs.entry_selected_operand holds fields query
  have ref : entry.data.family.result (sourceWord w).toBitVec (operandWord w).toBitVec = bitwiseReference w entry := by
    rw [operand]
    simp only [bitwiseReference,(Airbender.NativeControlArithmeticProofs.read_words w).1,(Airbender.NativeControlArithmeticProofs.read_words w).2]
    split <;> rfl
  unfold BitwiseResult
  rw [Airbender.NativeControlArithmeticProofs.write_word,actual,ref]

theorem comparison_result {w : Nat → F} {entry : ComparisonProgramEntry}
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints NativeRuntimePool.table))
    (fields : comparisonDecoderFields entry.instruction = some entry.data) (query : decoderQuery w = entry.query)
    (left : (Airbender.NativeMainDependencies.read w 0).word.Bounded)
    (right : (Airbender.NativeMainDependencies.read w 1).word.Bounded) : ComparisonResult w entry := by
  have source : (sourceWord w).Bounded := by rwa [← (Airbender.NativeControlArithmeticProofs.read_words w).1]
  have register : (registerOperandWord w).Bounded := by rwa [← (Airbender.NativeControlArithmeticProofs.read_words w).2]
  have actual := (NativeComparisonResultProofs.decoded_result (comparison_body holds fields query) fields query source register).2
  have operand := NativeComparisonOperandProofs.entry_selected_operand holds fields query
  have ref : entry.data.family.result (sourceWord w).toBitVec (operandWord w).toBitVec = comparisonReference w entry := by
    rw [operand]
    simp only [comparisonReference,(Airbender.NativeControlArithmeticProofs.read_words w).1,(Airbender.NativeControlArithmeticProofs.read_words w).2]
    split <;> rfl
  unfold ComparisonResult
  rw [Airbender.NativeControlArithmeticProofs.write_word,actual,ref]

theorem comparison_high {w : Nat → F} {entry : ComparisonProgramEntry} (actual : ComparisonResult w entry) :
    (limbs (Airbender.NativeMainDependencies.write w 2)).2 = 0 := by
  have high := congrArg Arithmetic.Word.hi actual
  change (limbs (Airbender.NativeMainDependencies.write w 2)).2 = _ at high
  rw [high]
  simp only [comparisonReference,ComparisonMode.result]
  split_ifs <;> rfl

theorem on_path {Setup R : Type} [Field R] {proofs : List (Airbender.NativeInitializationBatch.Proof R)}
    {workers : WorkerBatch Setup R} {inputs : PublicBoundary} {path : List Token}
    (history : History proofs workers inputs path) {row : Airbender.NativeMixedMemoryOrder.MainRow}
    (member : row ∈ Airbender.NativeMixedMemoryOrder.mainRows proofs)
    (address : (Airbender.NativeMainDependencies.read row.assignment 2).address = Airbender.NativeControlHistory.address) :
    (Airbender.NativeMainDependencies.read row.assignment 2,Airbender.NativeMainDependencies.write row.assignment 2) ∈ path.zip path.tail := by
  have actual : (Airbender.NativeMainDependencies.read row.assignment 2,Airbender.NativeMainDependencies.write row.assignment 2) ∈ row.memorySteps := by
    cases row with
    | mk family w =>
      cases family
      apply List.mem_map.mpr
      exact ⟨importedConstraintsMemoryPorts[2],by change _ ∈ importedConstraintsMemoryPorts.toList; simp [importedConstraintsMemoryPorts],rfl⟩
  have step : (Airbender.NativeMainDependencies.read row.assignment 2,Airbender.NativeMainDependencies.write row.assignment 2) ∈
      Airbender.NativeMemoryRoots.steps proofs workers := by
    apply List.mem_append_left
    exact List.mem_flatMap.mpr ⟨row,member,actual⟩
  exact history.ports.mem_iff.mpr (List.mem_filter.mpr ⟨step,by simpa only [decide_eq_true_eq] using address⟩)

theorem from_prior {Setup R : Type} [Field R] {batch : Airbender.NativeMainDecoder.Batch R}
    {workers : WorkerBatch Setup R} {inputs : PublicBoundary} {before : Reference.RiscV.Sail.State}
    {publicSetup : SparseDecoderSetup Airbender.NativeCallerDecoder.Mode}
    (prior : Airbender.NativeControlArithmetic.Effects before publicSetup batch workers inputs)
    (bodies : ∀ row ∈ Airbender.NativeMixedMemoryOrder.mainRows batch.main.proofs,
      FlatOperation.ConstraintsHoldFlat (Verification.environment row.assignment) (importedConstraints NativeRuntimePool.table)) :
    Airbender.NativeControlLogic.Effects before publicSetup batch workers inputs := by
  have words : Airbender.NativeMixedWordBounds.Effects batch workers inputs :=
    prior.prior.prior.prior.prior.prior.prior.prior.prior.prior.prior.words
  refine ⟨prior,?_,?_,?_⟩
  · intro row member entry fields query
    exact bitwise_result (bodies row member) fields query
  · intro row member entry fields query
    have actual := comparison_result (bodies row member) fields query
      (Airbender.NativeControlArithmeticProofs.main_reads words member 0) (Airbender.NativeControlArithmeticProofs.main_reads words member 1)
    exact ⟨actual,comparison_high actual⟩
  · obtain ⟨path,history,origins,csr,arithmetic⟩ := prior.path
    refine ⟨path,history,origins,csr,arithmetic,?_,?_⟩
    · intro row member entry fields query rd
      apply on_path history member
      have route := NativeBitwisePortProofs.register_addresses (bodies row member) fields query 2
      change importedConstraintsMemoryPorts[2].address.code row.assignment = _
      exact route.trans (by simp [rd,Airbender.Trace.Cell.addressCode])
    · intro row member entry fields query rd
      apply on_path history member
      have route := NativeComparisonPortProofs.register_addresses (bodies row member) fields query 2
      change importedConstraintsMemoryPorts[2].address.code row.assignment = _
      exact route.trans (by simp [rd,Airbender.Trace.Cell.addressCode])

theorem counted {Setup R : Type} [Field R]
    (publicSetup : SparseDecoderSetup Airbender.NativeCallerDecoder.Mode)
    (embed : F →+* R) (memory : MemoryKeyChallenges R) (ch : CSRArgumentChallenges R)
    (pc : PCChallenges R) (gamma : R)
    (decoder : Airbender.ReducedMachine.NativeDecoderArguments.Challenges R) (config : WorkerConfiguration Setup)
    {batch : Airbender.NativeMainDecoder.Batch R} {workers : WorkerBatch Setup R}
    {inputs : PublicBoundary} {inverse : BoundaryInverses R}
    (accepted : Airbender.NativeMainDecoder.SourceAccepted publicSetup embed memory ch pc gamma decoder config batch workers inputs inverse)
    {before : Reference.RiscV.Sail.State} {count : Nat}
    (image : Airbender.NativeCallerDecoder.setupImage before count 20 = some publicSetup)
    (lookups : Airbender.NativeMainDecoder.LogicalLookups publicSetup batch)
    (identity : Airbender.NativeDelegationSupport.SourceIdentity batch.main.proofs workers) :
    Airbender.NativeControlLogic.Effects before publicSetup batch workers inputs := by
  have prior := Airbender.NativeControlArithmeticProofs.counted publicSetup embed memory ch pc gamma decoder config accepted image lookups identity
  have components := Airbender.NativeMemoryHistoryProofs.components embed memory ch pc gamma config accepted.counted.component
  have body := Airbender.NativeMainStateHistoryProofs.selected_body embed memory pc _ components
  apply from_prior prior
  intro row member
  have holds := body row member
  cases row with
  | mk family w => cases family; exact holds
end Airbender.NativeControlLogicProofs
