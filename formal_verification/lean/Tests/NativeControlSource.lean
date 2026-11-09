import Airbender.Review.Trace.Families.ReducedMachine.ControlSourceTheorems
import Tests.NativeControlFold

namespace Airbender.Tests.NativeControlSource
open Airbender.NativeWorkerSnapshot Airbender.NativeControlHistory Airbender.NativeControlLogic
open Airbender.NativeControlLastReset Airbender.NativeControlFold Airbender.NativeControlSource
open Airbender.ReducedMachine Airbender.ReducedMachine.Native Airbender.Trace
open Airbender.Blake2Worker.Native Airbender.ReducedMachine.NativeMemoryBoundary
set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false

/-- Pure small labelled SOURCE positions; not actual accepted native rows. -/
private def labels : List (Nat × Bool) := [(42,false),(42,true),(99,false),(99,true)]
private def weight (label : Nat × Bool) : F := if label.2 then 1 else 0
private def flags (index : Fin 3) : Bool := decide (index.val ≠ 1)
private def token (time : F) : Token := ⟨address,(time,0),Nat.pair 0 1⟩

theorem original_active_indices : ∃! index : Fin labels.length, labels[index.val].1 = 42 ∧ weight labels[index.val] = 1 := by
  apply Airbender.NativeCallerPositionProofs.one_position labels Prod.fst weight 42
  unfold labels weight Airbender.NativeCallerCount.countAt
  decide +kernel

theorem equal_inactive_key_retained : labels[0].1 = labels[1].1 ∧ labels[0].2 = false ∧ labels[1].2 = true := by decide +kernel

theorem complete_source_domain : labels.length = 4 ∧ (labels.filter fun x => x.2).length = 2 := by decide +kernel

theorem wrong_membership_count_rejected : labels.count (42,true) = 1 ∧ (labels.map Prod.fst).count 42 = 2 := by decide +kernel

theorem original_partner_cardinality : Fintype.card (Fin 2) = Fintype.card {i : Fin 4 // i.val % 2 = 1} := by
  apply Airbender.NativeControlSourceProofs.matching_card (fun a b => 2 * a.val + 1 = b.val.val)
  · intro a
    let b : {i : Fin 4 // i.val % 2 = 1} := ⟨⟨2 * a.val + 1,by have := a.isLt; omega⟩,by change (2 * a.val + 1) % 2 = 1; omega⟩
    refine ⟨b,rfl,?_⟩
    intro other same
    exact Subtype.ext (Fin.ext same.symm)
  · intro b
    have odd := b.property
    have bound := b.val.isLt
    refine ⟨⟨b.val.val / 2,by omega⟩,by change 2 * (b.val.val / 2) + 1 = b.val.val; omega,?_⟩
    intro other same
    apply Fin.ext
    change other.val = b.val.val / 2
    omega

theorem empty_partner_cardinality : Fintype.card (Fin 0) = Fintype.card (Fin 0) :=
  Airbender.NativeControlSourceProofs.matching_card (fun a b => a = b)
    (fun index => Fin.elim0 index) (fun index => Fin.elim0 index)

theorem selected_flags_cardinality : countFlags flags = Fintype.card {i // flags i = true} :=
  Airbender.NativeControlSourceProofs.flags_card 3 flags

theorem selected_count_two : countFlags flags = 2 := by decide +kernel

theorem every_consecutive_original_position : pathEdge ([10,20,30,40] : List Nat) ⟨2,by decide⟩ = (30,40) := by decide +kernel

theorem edge_occurrence_position : ∃ index : Fin (([10,20,30] : List Nat).length-1), pathEdge [10,20,30] index = (20,30) :=
  Airbender.NativeControlSourceProofs.edge_position (by simp)

theorem exact_edge_injective : Function.Injective (pathEdge ([10,20,30] : List Nat)) :=
  Airbender.NativeControlSourceProofs.edge_injective id (by decide +kernel)

theorem segment_indices_injective : Function.Injective (fun index : Fin 2 =>
    edgeAt ([10,20,30] : List Nat) ⟨2,by decide⟩ index) := by
  have result := Airbender.NativeControlSourceProofs.segment_injective (path := ([10,20,30] : List Nat))
    id (by decide +kernel) ⟨2,by decide⟩ ⟨0,by decide⟩
  simpa only [Nat.zero_add] using result

theorem equal_values_distinct_raw_edges : (token 0).value = (token 1).value ∧
    (token 1).value = (token 2).value ∧ (token 0,token 1) ≠ (token 1,token 2) := by
  unfold token
  decide +kernel

theorem equal_value_workers_still_counted : countFlags (fun _ : Fin 3 => true) = 3 ∧ iterate advance 3 (0,1) = (0,1) :=
  Airbender.Tests.NativeControlFold.all_equal_value_updates_counted

theorem inactive_CSR_kept : limbs (Airbender.NativeMainDependencies.write (NativeCSRPositiveWitness.assignment false) 2) = (0,0) :=
  Airbender.Tests.NativeControlFold.inactive_CSR_kept

section
variable {Setup R : Type} [Field R] {batch : Airbender.NativeMainDecoder.Batch R}
  {workers : WorkerBatch Setup R} {inputs : PublicBoundary}
  {before : Reference.RiscV.Sail.State} {publicSetup : SparseDecoderSetup Airbender.NativeCallerDecoder.Mode}

theorem exact_source_relation (edge : Token × Token) (source : Fin (Airbender.NativeTokenLedger.workerRows workers).length) :
    SourceAt workers edge source ↔
      (Airbender.NativeTokenLedger.workerRows workers)[source.val] constraintsABI.multiplicity = 1 ∧
      edge = (read (Airbender.NativeTokenLedger.workerRows workers)[source.val] 42,
        write (Airbender.NativeTokenLedger.workerRows workers)[source.val] 42) := Iff.rfl

theorem every_segment_source_unique {nodes : List Token} (history : History batch.main.proofs workers inputs nodes)
    (target : Fin nodes.length) (start : Fin (target.val+1))
    {source : Fin (Airbender.NativeTokenLedger.workerRows workers).length}
    (present : SegmentSource workers nodes target start source) :
    ∃! index : Fin (target.val-start.val), SourceAt workers
      (edgeAt nodes target ⟨start.val + index.val,by have := index.isLt; omega⟩) source :=
  Airbender.NativeControlSourceProofs.segment_position history target start present

theorem source_count_original_bound (nodes : List Token) (target : Fin nodes.length) (start : Fin (target.val+1)) :
    sourceCount workers nodes target start ≤ (Airbender.NativeTokenLedger.workerRows workers).length :=
  Airbender.NativeControlSourceProofs.source_count_bound workers nodes target start

variable (effect : Airbender.NativeControlSource.Effects before publicSetup batch workers inputs)
include effect

theorem same_path_positions_and_counts : ∃ nodes, History batch.main.proofs workers inputs nodes ∧ Matching workers nodes ∧
    ∀ target : Fin nodes.length, ∀ start : Fin (target.val+1), workerCount workers nodes target start = sourceCount workers nodes target start := by
  obtain ⟨nodes,history,_,_,_,_,_,_,_,_,_,_,partners,counts⟩ := effect.path
  exact ⟨nodes,history,partners,counts⟩

theorem every_target_and_worker_retained : ∃ nodes, History batch.main.proofs workers inputs nodes ∧ Matching workers nodes ∧
    (∀ target : Fin nodes.length, Airbender.NativeControlFold.Outcome before publicSetup batch.main.proofs workers nodes target) ∧
    (∀ w ∈ Airbender.NativeTokenLedger.workerRows workers, w constraintsABI.multiplicity = 1 →
      ∃ target : Fin nodes.length, nodes.get target = read w 42 ∧ Airbender.NativeControlFold.Outcome before publicSetup batch.main.proofs workers nodes target) := by
  obtain ⟨nodes,history,_,_,_,_,_,_,_,_,results,positions,partners,_⟩ := effect.path
  exact ⟨nodes,history,partners,results,positions⟩

theorem all_ordinary_CSR_edges_same_path : ∃ nodes, History batch.main.proofs workers inputs nodes ∧
    Edges csrDecoderFields batch.main.proofs nodes ∧ Airbender.NativeControlArithmetic.Edges batch.main.proofs nodes ∧
    Edges bitwiseDecoderFields batch.main.proofs nodes ∧ Edges comparisonDecoderFields batch.main.proofs nodes ∧
    Edges shiftDecoderFields batch.main.proofs nodes ∧ Edges jumpDecoderFields batch.main.proofs nodes ∧
    Edges wordMemoryDecoderFields batch.main.proofs nodes ∧ Matching workers nodes := by
  obtain ⟨nodes,history,_,csr,arithmetic,bitwise,comparison,shifts,jumps,loads,_,_,partners,_⟩ := effect.path
  exact ⟨nodes,history,csr,arithmetic,bitwise,comparison,shifts,jumps,loads,partners⟩

theorem old_fold_retained : Airbender.NativeControlFold.Effects before publicSetup batch workers inputs := effect.prior

theorem old_joint_retained : Airbender.NativeJointReplay.Effects batch workers inputs :=
  Airbender.Tests.NativeControlFold.old_joint_retained effect.prior
end

theorem full_counted_source {Setup R : Type} [Field R]
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
    Airbender.NativeControlSource.Effects before publicSetup batch workers inputs :=
  Airbender.NativeControlSourceProofs.counted publicSetup embed memory ch pc gamma decoder config accepted image lookups identity
end Airbender.Tests.NativeControlSource
