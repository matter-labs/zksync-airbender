import Airbender.Review.Trace.Families.ReducedMachine.ControlArithmetic
import Airbender.Proofs.ReducedMachine.NativeControlCSR
import Airbender.Proofs.ReducedMachine.NativeArithmeticDecodedResult

namespace Airbender.NativeControlArithmeticProofs
open Airbender.NativeWorkerSnapshot Airbender.NativeControlHistory
open Airbender.NativeControlArithmetic Airbender.ReducedMachine Airbender.ReducedMachine.Native
open Airbender.Trace Airbender.Blake2Worker.Native Airbender.ReducedMachine.NativeMemoryBoundary
set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false

theorem read_words (w : Nat → F) :
    (Airbender.NativeMainDependencies.read w 0).word = sourceWord w ∧
    (Airbender.NativeMainDependencies.read w 1).word = registerOperandWord w := by
  constructor
  · change (⟨(Nat.unpair (Nat.pair (w 35).val (w 36).val)).1,(Nat.unpair (Nat.pair (w 35).val (w 36).val)).2⟩ : Arithmetic.Word) = _
    rw [Nat.unpair_pair]
    rfl
  · change (⟨(Nat.unpair (Nat.pair (w 37).val (w 38).val)).1,(Nat.unpair (Nat.pair (w 37).val (w 38).val)).2⟩ : Arithmetic.Word) = _
    rw [Nat.unpair_pair]
    rfl

theorem write_word (w : Nat → F) : (Airbender.NativeMainDependencies.write w 2).word = writtenWord w := by
  change (⟨(limbs (Airbender.NativeMainDependencies.write w 2)).1,(limbs (Airbender.NativeMainDependencies.write w 2)).2⟩ : Arithmetic.Word) = _
  rw [Airbender.NativeControlCSRProofs.write_limbs]
  simp [writtenWord,rdWrite,NativePortProofs.write_columns,WordColumns.evaluate]

theorem result {w : Nat → F} {entry : ArithmeticProgramEntry}
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints NativeRuntimePool.table))
    (fields : arithmeticDecoderFields entry.instruction = some entry.data) (query : decoderQuery w = entry.query)
    (left : (Airbender.NativeMainDependencies.read w 0).word.Bounded)
    (right : (Airbender.NativeMainDependencies.read w 1).word.Bounded) : Result w entry := by
  have source : (sourceWord w).Bounded := by rwa [← (read_words w).1]
  have register : (registerOperandWord w).Bounded := by rwa [← (read_words w).2]
  have actual := (NativeArithmeticResultProofs.decoded_result holds fields query source register).2
  have decoded := NativeArithmeticDecoderProofs.decoded_fields fields query
  have routed := NativeArithmeticFieldProofs.source holds entry.data.family decoded.mask
  have selected := congrArg (fun v : Vector F 2 => (⟨v[0].val,v[1].val⟩ : Arithmetic.Word)) routed
  have operand : operandWord w = if entry.data.family.useRegister then registerOperandWord w else arithmeticImmediateWord w := by
    cases choice : entry.data.family.useRegister <;>
      simpa [choice,operandWord,registerOperandWord,arithmeticImmediateWord,importedConstraintsMemoryPorts,WordColumns.evaluate] using selected
  have pc := Airbender.Trace.Proofs.native_query_pc_word (by decide : Arithmetic.limbBase < mersenne31Modulus) query
  change initialPCWord w = Arithmetic.Word.ofBitVec entry.pc at pc
  have immediate := NativeArithmeticDecoderProofs.immediate_word fields query
  have ref : entry.data.family.result (sourceWord w).toBitVec (operandWord w).toBitVec
      (initialPCWord w).toBitVec entry.data.immediate.toBitVec = reference w entry := by
    rw [operand,pc]
    simp only [reference,(read_words w).1,(read_words w).2,Arithmetic.Word.ofBitVec_roundtrip]
    split <;> simp_all
  unfold Result
  rw [write_word,actual,ref]

theorem rd12_limbs {w : Nat → F} {entry : ArithmeticProgramEntry}
    (actual : Result w entry) (rd : entry.data.rd = 12) :
    limbs (Airbender.NativeMainDependencies.write w 2) =
      ((Arithmetic.Word.ofBitVec (reference w entry)).lo,(Arithmetic.Word.ofBitVec (reference w entry)).hi) := by
  have word : (Airbender.NativeMainDependencies.write w 2).word = Arithmetic.Word.ofBitVec (reference w entry) := by
    simpa only [Result,rd,if_neg (by decide : (12 : BitVec 5) ≠ 0)] using actual
  exact Prod.ext (congrArg Arithmetic.Word.lo word) (congrArg Arithmetic.Word.hi word)

theorem main_reads {Setup R : Type} [Field R] {batch : Airbender.NativeMainDecoder.Batch R}
    {workers : WorkerBatch Setup R} {inputs : PublicBoundary}
    (words : Airbender.NativeMixedWordBounds.Effects batch workers inputs)
    {row : Airbender.NativeMixedMemoryOrder.MainRow}
    (member : row ∈ Airbender.NativeMixedMemoryOrder.mainRows batch.main.proofs) (slot : Fin 3) :
    (Airbender.NativeMainDependencies.read row.assignment slot).word.Bounded := by
  have edge : Airbender.NativeMixedMemoryOrder.Step batch.main.proofs workers
      (Airbender.NativeMainDependencies.read row.assignment slot) (Airbender.NativeMainDependencies.write row.assignment slot) := by
    left
    refine ⟨row,member,Airbender.NativeMainDependencies.port slot,?_,rfl,?_⟩
    · cases row with
      | mk family w =>
        cases family
        change Airbender.NativeMainDependencies.port slot ∈ importedConstraintsMemoryPorts
        fin_cases slot <;> simp [Airbender.NativeMainDependencies.port,importedConstraintsMemoryPorts]
    · cases row with
      | mk family w => cases family; rfl
  exact (words.steps _ _ edge).1

theorem main_on_path {Setup R : Type} [Field R] {proofs : List (Airbender.NativeInitializationBatch.Proof R)}
    {workers : WorkerBatch Setup R} {inputs : PublicBoundary} {path : List Token}
    (history : History proofs workers inputs path) {row : Airbender.NativeMixedMemoryOrder.MainRow}
    (member : row ∈ Airbender.NativeMixedMemoryOrder.mainRows proofs) {entry : ArithmeticProgramEntry}
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment row.assignment) (importedConstraints NativeRuntimePool.table))
    (fields : arithmeticDecoderFields entry.instruction = some entry.data) (query : row.decoderQuery = entry.query)
    (rd : entry.data.rd = 12) :
    (Airbender.NativeMainDependencies.read row.assignment 2,Airbender.NativeMainDependencies.write row.assignment 2) ∈ path.zip path.tail := by
  have route := NativeArithmeticPortProofs.register_addresses holds fields query 2
  have address : (Airbender.NativeMainDependencies.read row.assignment 2).address = Airbender.NativeControlHistory.address := by
    change importedConstraintsMemoryPorts[2].address.code row.assignment = _
    exact route.trans (by simp [rd,Airbender.Trace.Cell.addressCode])
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
    (prior : Airbender.NativeControlCSR.Effects before publicSetup batch workers inputs)
    (bodies : ∀ row ∈ Airbender.NativeMixedMemoryOrder.mainRows batch.main.proofs,
      FlatOperation.ConstraintsHoldFlat (Verification.environment row.assignment) (importedConstraints NativeRuntimePool.table)) :
    Airbender.NativeControlArithmetic.Effects before publicSetup batch workers inputs := by
  have words : Airbender.NativeMixedWordBounds.Effects batch workers inputs :=
    prior.prior.prior.prior.prior.prior.prior.prior.prior.prior.words
  refine ⟨prior,?_,?_⟩
  · intro row member entry fields query
    exact result (bodies row member) fields query (main_reads words member 0) (main_reads words member 1)
  · obtain ⟨path,history,origins,csr⟩ := prior.origins
    refine ⟨path,history,origins,csr,?_⟩
    intro row member entry fields query rd
    exact main_on_path history member (bodies row member) fields query rd

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
    Airbender.NativeControlArithmetic.Effects before publicSetup batch workers inputs := by
  have prior := Airbender.NativeControlCSRProofs.counted publicSetup embed memory ch pc gamma decoder config accepted image lookups identity
  have components := Airbender.NativeMemoryHistoryProofs.components embed memory ch pc gamma config accepted.counted.component
  have body := Airbender.NativeMainStateHistoryProofs.selected_body embed memory pc _ components
  apply from_prior prior
  intro row member
  have holds := body row member
  cases row with
  | mk family w => cases family; exact holds
end Airbender.NativeControlArithmeticProofs
