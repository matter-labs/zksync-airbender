import Airbender.Review.Trace.Families.ReducedMachine.ControlLoad
import Airbender.Proofs.ReducedMachine.NativeControlShiftJump
import Airbender.Proofs.ReducedMachine.NativeWordMemoryDecodedResult

namespace Airbender.NativeControlLoadProofs
open Airbender.NativeWorkerSnapshot Airbender.NativeControlHistory Airbender.NativeControlLogic
open Airbender.NativeControlLoad Airbender.ReducedMachine Airbender.ReducedMachine.Native
open Airbender.Trace Airbender.Blake2Worker.Native Airbender.ReducedMachine.NativeMemoryBoundary
set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false

theorem projection {instruction : SailRV32.instruction} {data : DecoderData WordMemoryMode}
    (fields : wordMemoryDecoderFields instruction = some data) :
    unifiedDecoderFields instruction = some (data.mapFamily Sum.inr) := by
  unfold wordMemoryDecoderFields at fields
  split at fields
  all_goals first
    | (solve | cases fields)
    | (simp only [wordMemoryFields,Option.some.injEq] at fields
       subst data
       rfl)

theorem fixed_body {w : Nat → F} {entry : WordMemoryProgramEntry}
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints NativeRuntimePool.table))
    (fields : wordMemoryDecoderFields entry.instruction = some entry.data) (query : decoderQuery w = entry.query) :
    FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints NativeFixed.table) := by
  exact Airbender.NativeDecodedQueryDomainProofs.fixed_body (entry := entry.mapFamily Sum.inr) holds (projection fields) query

theorem rd12_load {entry : WordMemoryProgramEntry}
    (fields : wordMemoryDecoderFields entry.instruction = some entry.data) (rd : entry.data.rd = 12) :
    entry.data.family = false := by
  have unused := NativeWordMemoryDecoderProofs.unused_registers fields
  cases mode : entry.data.family
  · rfl
  · simp only [mode,if_true] at unused
    rw [rd] at unused
    exact False.elim ((by decide : ¬ (12 : BitVec 5) = 0) unused)

theorem result {w : Nat → F} {entry : WordMemoryProgramEntry}
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints NativeRuntimePool.table))
    (fields : wordMemoryDecoderFields entry.instruction = some entry.data) (query : decoderQuery w = entry.query)
    (load : entry.data.family = false) (bound : (Airbender.NativeMainDependencies.read w 0).word.Bounded) : LoadResult w entry := by
  have fixed := fixed_body holds fields query
  have source : (sourceWord w).Bounded := by rwa [← (Airbender.NativeControlArithmeticProofs.read_words w).1]
  have address := NativeWordMemoryResultProofs.effective_address fixed fields query source
  have exactAddress : wordMemoryAddressWord w = addressReference w entry := by
    simpa only [addressReference,(Airbender.NativeControlArithmeticProofs.read_words w).1] using address
  have decoded := NativeWordMemoryDecoderProofs.decoded_fields fields query
  have mask : w 12 = (wordMemoryMask false : F) := by simpa only [load] using decoded.mask
  have aligned := (NativeWordMemoryShapeProofs.load_address fixed mask).2.1
  have second : wordMemorySecondWord w = (Airbender.NativeMainDependencies.read w 1).word := by
    rw [(Airbender.NativeControlArithmeticProofs.read_words w).2]
    rfl
  have reference : wordMemoryLoadWord w = loadReference w entry := by
    unfold wordMemoryLoadWord loadReference
    rw [exactAddress,second]
  have written := NativeWordMemoryResultProofs.written_result fixed fields query
  have actual : (Airbender.NativeMainDependencies.write w 2).word = wordMemoryWrittenWord w := by
    rw [Airbender.NativeControlArithmeticProofs.write_word]
    rfl
  refine ⟨exactAddress,?_,?_⟩
  · rwa [← exactAddress]
  · rw [actual,written,wordMemoryResult,load,reference]
    rfl

theorem from_prior {Setup R : Type} [Field R] {batch : Airbender.NativeMainDecoder.Batch R}
    {workers : WorkerBatch Setup R} {inputs : PublicBoundary} {before : Reference.RiscV.Sail.State}
    {publicSetup : SparseDecoderSetup Airbender.NativeCallerDecoder.Mode}
    (prior : Airbender.NativeControlShiftJump.Effects before publicSetup batch workers inputs)
    (bodies : ∀ row ∈ Airbender.NativeMixedMemoryOrder.mainRows batch.main.proofs,
      FlatOperation.ConstraintsHoldFlat (Verification.environment row.assignment) (importedConstraints NativeRuntimePool.table)) :
    Airbender.NativeControlLoad.Effects before publicSetup batch workers inputs := by
  have words : Airbender.NativeMixedWordBounds.Effects batch workers inputs :=
    prior.prior.prior.prior.prior.prior.prior.prior.prior.prior.prior.prior.prior.words
  refine ⟨prior,?_,?_⟩
  · intro row member entry fields query load
    exact result (bodies row member) fields query load (Airbender.NativeControlArithmeticProofs.main_reads words member 0)
  · obtain ⟨path,history,origins,csr,arithmetic,bitwise,comparison,shifts,jumps⟩ := prior.path
    refine ⟨path,history,origins,csr,arithmetic,bitwise,comparison,shifts,jumps,?_⟩
    intro row member entry fields query rd
    apply Airbender.NativeControlLogicProofs.on_path history member
    have load := rd12_load fields rd
    have route := NativeWordMemoryPortProofs.addresses (fixed_body (bodies row member) fields query) fields query 2
    change importedConstraintsMemoryPorts[2].address.code row.assignment = _
    exact route.trans (by simp [wordMemoryPortCells,load,rd,Airbender.Trace.Cell.addressCode])

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
    Airbender.NativeControlLoad.Effects before publicSetup batch workers inputs := by
  have prior := Airbender.NativeControlShiftJumpProofs.counted publicSetup embed memory ch pc gamma decoder config accepted image lookups identity
  have components := Airbender.NativeMemoryHistoryProofs.components embed memory ch pc gamma config accepted.counted.component
  have body := Airbender.NativeMainStateHistoryProofs.selected_body embed memory pc _ components
  apply from_prior prior
  intro row member
  have holds := body row member
  cases row with
  | mk family w => cases family; exact holds
end Airbender.NativeControlLoadProofs
