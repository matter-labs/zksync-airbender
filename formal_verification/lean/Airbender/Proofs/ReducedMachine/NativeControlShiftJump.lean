import Airbender.Review.Trace.Families.ReducedMachine.ControlShiftJump
import Airbender.Proofs.ReducedMachine.NativeControlLogic
import Airbender.Proofs.ReducedMachine.NativeShiftResult
import Airbender.Proofs.ReducedMachine.NativeShiftOperand
import Airbender.Proofs.ReducedMachine.NativeJumpReturn
import Airbender.Proofs.ReducedMachine.NativeJumpPorts

namespace Airbender.NativeControlShiftJumpProofs
open Airbender.NativeWorkerSnapshot Airbender.NativeControlHistory Airbender.NativeControlLogic
open Airbender.NativeControlShiftJump Airbender.ReducedMachine Airbender.ReducedMachine.Native
open Airbender.Trace Airbender.Blake2Worker.Native Airbender.ReducedMachine.NativeMemoryBoundary
set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false

private def shiftMode (mode : ShiftMode) : UnifiedMode := Sum.inl (Sum.inl mode)

theorem shift_projection {instruction : SailRV32.instruction} {data : DecoderData ShiftMode}
    (fields : shiftDecoderFields instruction = some data) :
    unifiedDecoderFields instruction = some (data.mapFamily shiftMode) := by
  unfold unifiedDecoderFields supportedDecoderFields
  rw [fields]
  rfl

theorem shift_body {w : Nat → F} {entry : ShiftProgramEntry}
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints NativeRuntimePool.table))
    (fields : shiftDecoderFields entry.instruction = some entry.data) (query : decoderQuery w = entry.query) :
    FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints NativeFixed.table) := by
  exact Airbender.NativeDecodedQueryDomainProofs.fixed_body (entry := entry.mapFamily shiftMode) holds
    (shift_projection fields) query

theorem shift_result {w : Nat → F} {entry : ShiftProgramEntry}
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints NativeRuntimePool.table))
    (fields : shiftDecoderFields entry.instruction = some entry.data) (query : decoderQuery w = entry.query)
    (bound : (Airbender.NativeMainDependencies.read w 0).word.Bounded) : ShiftResult w entry := by
  have source : (sourceWord w).Bounded := by rwa [← (Airbender.NativeControlArithmeticProofs.read_words w).1]
  have actual := (NativeShiftResultProofs.decoded_result (shift_body holds fields query) fields query source).2
  have operand := NativeShiftOperandProofs.entry_selected_operand holds fields query
  have ref : entry.data.family.result (sourceWord w).toBitVec
      ((operandWord w).toBitVec.extractLsb' 0 5).toNat = shiftReference w entry := by
    rw [operand]
    simp only [shiftReference,(Airbender.NativeControlArithmeticProofs.read_words w).1,(Airbender.NativeControlArithmeticProofs.read_words w).2]
    split <;> rfl
  unfold ShiftResult
  rw [Airbender.NativeControlArithmeticProofs.write_word,actual,ref]

theorem jump_result {w : Nat → F} {entry : JumpProgramEntry}
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints NativeRuntimePool.table))
    (fields : jumpDecoderFields entry.instruction = some entry.data) (query : decoderQuery w = entry.query)
    (aligned : (initialPCWord w).lo % 4 = 0) : JumpResult w entry := by
  have actual := (NativeJumpReturnProofs.candidate_result holds fields query aligned).2
  have canonical := Airbender.Trace.Proofs.native_query_pc_word (by decide : Arithmetic.limbBase < mersenne31Modulus) query
  change initialPCWord w = Arithmetic.Word.ofBitVec entry.pc at canonical
  unfold JumpResult
  rw [Airbender.NativeControlArithmeticProofs.write_word,actual,canonical,Arithmetic.Word.ofBitVec_roundtrip]

theorem public_alignment {R : Type} [Field R] {batch : Airbender.NativeMainDecoder.Batch R}
    {before : Reference.RiscV.Sail.State} {count : Nat}
    {publicSetup : SparseDecoderSetup Airbender.NativeCallerDecoder.Mode}
    (image : Airbender.NativeCallerDecoder.setupImage before count 20 = some publicSetup)
    (sources : Airbender.NativeMainDecoder.PublicSources Airbender.NativeCallerDecoder.decoderFields before publicSetup batch)
    {row : Airbender.NativeMixedMemoryOrder.MainRow} (member : row ∈ Airbender.NativeMixedMemoryOrder.mainRows batch.main.proofs) :
    (initialPCWord row.assignment).lo % 4 = 0 := by
  obtain ⟨entry,present,_,query⟩ := Airbender.NativeControlOriginProofs.main_sources sources row member
  have canonical := Airbender.Trace.Proofs.native_query_pc_word (by decide : Arithmetic.limbBase < mersenne31Modulus) query
  change initialPCWord row.assignment = Arithmetic.Word.ofBitVec entry.pc at canonical
  rw [canonical]
  exact (Airbender.Trace.Proofs.run_sparse_setup_sources image present).2

theorem from_prior {Setup R : Type} [Field R] {batch : Airbender.NativeMainDecoder.Batch R}
    {workers : WorkerBatch Setup R} {inputs : PublicBoundary} {before : Reference.RiscV.Sail.State}
    {publicSetup : SparseDecoderSetup Airbender.NativeCallerDecoder.Mode}
    (prior : Airbender.NativeControlLogic.Effects before publicSetup batch workers inputs)
    (bodies : ∀ row ∈ Airbender.NativeMixedMemoryOrder.mainRows batch.main.proofs,
      FlatOperation.ConstraintsHoldFlat (Verification.environment row.assignment) (importedConstraints NativeRuntimePool.table))
    (aligned : ∀ row ∈ Airbender.NativeMixedMemoryOrder.mainRows batch.main.proofs, (initialPCWord row.assignment).lo % 4 = 0) :
    Airbender.NativeControlShiftJump.Effects before publicSetup batch workers inputs := by
  have words : Airbender.NativeMixedWordBounds.Effects batch workers inputs :=
    prior.prior.prior.prior.prior.prior.prior.prior.prior.prior.prior.prior.words
  refine ⟨prior,?_,?_,?_⟩
  · intro row member entry fields query
    exact shift_result (bodies row member) fields query (Airbender.NativeControlArithmeticProofs.main_reads words member 0)
  · intro row member entry fields query
    exact jump_result (bodies row member) fields query (aligned row member)
  · obtain ⟨path,history,origins,csr,arithmetic,bitwise,comparison⟩ := prior.path
    refine ⟨path,history,origins,csr,arithmetic,bitwise,comparison,?_,?_⟩
    · intro row member entry fields query rd
      apply Airbender.NativeControlLogicProofs.on_path history member
      have route := NativeShiftPortProofs.register_addresses (bodies row member) fields query 2
      change importedConstraintsMemoryPorts[2].address.code row.assignment = _
      exact route.trans (by simp [rd,Airbender.Trace.Cell.addressCode])
    · intro row member entry fields query rd
      apply Airbender.NativeControlLogicProofs.on_path history member
      have route := NativeJumpPortProofs.register_addresses (bodies row member) fields query 2
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
    Airbender.NativeControlShiftJump.Effects before publicSetup batch workers inputs := by
  have prior := Airbender.NativeControlLogicProofs.counted publicSetup embed memory ch pc gamma decoder config accepted image lookups identity
  have components := Airbender.NativeMemoryHistoryProofs.components embed memory ch pc gamma config accepted.counted.component
  have body := Airbender.NativeMainStateHistoryProofs.selected_body embed memory pc _ components
  have sources := Airbender.NativeMainDecoderProofs.public_sources publicSetup embed memory ch pc gamma decoder config accepted image lookups
  apply from_prior prior
  · intro row member
    have holds := body row member
    cases row with
    | mk family w => cases family; exact holds
  · intro row member
    exact public_alignment image sources member
end Airbender.NativeControlShiftJumpProofs
