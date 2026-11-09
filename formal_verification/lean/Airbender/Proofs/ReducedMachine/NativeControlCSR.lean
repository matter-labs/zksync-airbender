import Airbender.Review.Trace.Families.ReducedMachine.ControlCSR
import Airbender.Proofs.ReducedMachine.NativeControlOrigin

namespace Airbender.NativeControlCSRProofs
open Airbender.NativeWorkerSnapshot Airbender.NativeControlHistory
open Airbender.NativeControlCSR Airbender.ReducedMachine Airbender.ReducedMachine.Native
open Airbender.Trace Airbender.Blake2Worker.Native Airbender.ReducedMachine.NativeMemoryBoundary
set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false

theorem write_limbs (w : Nat → F) : limbs (Airbender.NativeMainDependencies.write w 2) = ((w 43).val,(w 44).val) := by
  change Nat.unpair (Nat.pair (w 43).val (w 44).val) = _
  exact Nat.unpair_pair _ _

theorem key_value {w : Nat → F} {entry : CSRProgramEntry}
    (fields : csrDecoderFields entry.instruction = some entry.data) (query : decoderQuery w = entry.query) :
    (w 9).val = entry.data.immediate.lo := by
  have decoded := NativeCSRDecoderProofs.decoded_fields fields query
  have low := congrArg (fun v : Vector F 2 => v[(0 : Fin 2)]) decoded.immediate
  change w 9 = (entry.data.immediate.lo : F) at low
  rw [low,ZMod.val_natCast_of_lt (lt_trans (NativeCSRDecoderProofs.field_bounds fields).1 (by decide))]

theorem result {w : Nat → F} {entry : CSRProgramEntry}
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints NativeRuntimePool.table))
    (fields : csrDecoderFields entry.instruction = some entry.data) (query : decoderQuery w = entry.query) : CSRResult w entry := by
  have decoded := NativeCSRDecoderProofs.decoded_fields fields query
  have actual := NativeRuntimeCSRResultProofs.effects holds decoded.mask
  have key := key_value fields query
  have equation := actual.written
  rw [actual.candidate] at equation
  have low := congrArg (fun v : Vector F 2 => v[(0 : Fin 2)]) equation
  have high := congrArg (fun v : Vector F 2 => v[(1 : Fin 2)]) equation
  simp [rdWrite,NativePortProofs.write_columns,Trace.WordColumns.evaluate] at low high
  have written : limbs (Airbender.NativeMainDependencies.write w 2) =
      if entry.data.rd = 0 then (0,0) else ((w 90).val,(w 91).val) := by
    rw [write_limbs,low,high,decoded.zero]
    split <;> simp_all
  refine ⟨by simpa only [key] using actual.key,written,?_⟩
  intro delegate
  have oracle := actual.delegationZero (by simp [NativeRuntimeCSR.delegated,key,delegate])
  have zero : (w 90).val = 0 ∧ (w 91).val = 0 := by
    exact ⟨congrArg Arithmetic.Word.lo oracle,congrArg Arithmetic.Word.hi oracle⟩
  rw [written]
  split <;> simp [zero]

theorem nonzero_source {w : Nat → F} {entry : Airbender.NativeCallerDecoder.Program}
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints NativeRuntimePool.table))
    (fields : Airbender.NativeCallerDecoder.decoderFields entry.instruction = some entry.data)
    (query : decoderQuery w = entry.query)
    (nonzero : (limbs (Airbender.NativeMainDependencies.write w 2)).2 ≠ 0) : SeedSource entry := by
  rcases Airbender.NativeCallerDecoderProofs.entry_profile fields with ordinary | csr
  · obtain ⟨selected,instruction,source,_⟩ := ordinary
    left
    exact ⟨selected.data,by simpa only [← instruction] using source⟩
  · obtain ⟨selected,instruction,source,same⟩ := csr
    have actual := result holds source (query.trans same.symm)
    have key : selected.data.immediate.lo = 1984 := by
      rcases actual.key with first | second
      · exact first
      · exact False.elim (nonzero (congrArg Prod.snd (actual.clear second)))
    right
    exact ⟨selected.data,by simpa only [← instruction] using source,key⟩

theorem origin {R : Type} [Field R] {batch : Airbender.NativeMainDecoder.Batch R}
    {before : Reference.RiscV.Sail.State}
    {publicSetup : SparseDecoderSetup Airbender.NativeCallerDecoder.Mode}
    (bodies : ∀ row ∈ Airbender.NativeMixedMemoryOrder.mainRows batch.main.proofs,
      FlatOperation.ConstraintsHoldFlat (Verification.environment row.assignment) (importedConstraints NativeRuntimePool.table))
    {target : Token} (old : Airbender.NativeControlOrigin.Origin before publicSetup batch.main.proofs target) :
    Airbender.NativeControlCSR.Origin before publicSetup batch.main.proofs target := by
  obtain ⟨row,member,entry,present,source,query,rd,address,zero,nonzero,bound⟩ := old
  exact ⟨row,member,entry,present,source,query,rd,address,zero,nonzero,bound,nonzero_source (bodies row member) source.fields query nonzero⟩

theorem main_on_path {Setup R : Type} [Field R] {proofs : List (Airbender.NativeInitializationBatch.Proof R)}
    {workers : WorkerBatch Setup R} {inputs : PublicBoundary} {path : List Token}
    (history : History proofs workers inputs path) {row : Airbender.NativeMixedMemoryOrder.MainRow}
    (member : row ∈ Airbender.NativeMixedMemoryOrder.mainRows proofs) {entry : CSRProgramEntry}
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment row.assignment) (importedConstraints NativeRuntimePool.table))
    (fields : csrDecoderFields entry.instruction = some entry.data) (query : row.decoderQuery = entry.query)
    (rd : entry.data.rd = 12) :
    (Airbender.NativeMainDependencies.read row.assignment 2,Airbender.NativeMainDependencies.write row.assignment 2) ∈ path.zip path.tail := by
  have route := NativeCSRPortProofs.register_addresses holds fields query 2
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
    (prior : Airbender.NativeControlOrigin.Effects before publicSetup batch workers inputs)
    (bodies : ∀ row ∈ Airbender.NativeMixedMemoryOrder.mainRows batch.main.proofs,
      FlatOperation.ConstraintsHoldFlat (Verification.environment row.assignment) (importedConstraints NativeRuntimePool.table)) :
    Airbender.NativeControlCSR.Effects before publicSetup batch workers inputs := by
  refine ⟨prior,?_,?_,?_⟩
  · intro row member entry fields query
    exact result (bodies row member) fields query
  · obtain ⟨path,history,old⟩ := prior.origins
    refine ⟨path,history,(fun token member nonzero => origin bodies (old token member nonzero)),?_⟩
    intro row member entry fields query rd
    exact main_on_path history member (bodies row member) fields query rd
  · intro w member active nonzero
    exact origin bodies (prior.workers w member active nonzero)

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
    Airbender.NativeControlCSR.Effects before publicSetup batch workers inputs := by
  have prior := Airbender.NativeControlOriginProofs.counted publicSetup embed memory ch pc gamma decoder config accepted image lookups identity
  have components := Airbender.NativeMemoryHistoryProofs.components embed memory ch pc gamma config accepted.counted.component
  have body := Airbender.NativeMainStateHistoryProofs.selected_body embed memory pc _ components
  apply from_prior prior
  intro row member
  have holds := body row member
  cases row with
  | mk family w => cases family; exact holds
end Airbender.NativeControlCSRProofs
