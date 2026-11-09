import Airbender.Review.Trace.Families.ReducedMachine.ControlHistory
import Airbender.Proofs.ReducedMachine.NativeCallerPosition

namespace Airbender.NativeControlHistoryProofs
open Airbender.NativeControlHistory Airbender.NativeWorkerSnapshot
open Airbender.Blake2Worker.Native Airbender.ReducedMachine.NativeMemoryBoundary
set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false

/-- Exact uniqueness at a retained address, on abstract token lists. -/
theorem same_address {A K : Type} (key : A → K) {rows : List A} (unique : (rows.map key).Nodup)
    {a b : A} (am : a ∈ rows) (bm : b ∈ rows) (same : key a = key b) : a = b :=
  List.inj_on_of_nodup_map unique am bm same

theorem initial_address : initial.address = address := by rfl
theorem terminal_address (inputs : PublicBoundary) : (terminal inputs).address = address := by rfl
theorem initial_zero : limbs initial = (0,0) := by decide +kernel

theorem initial_member {R : Type} [Field R] (proofs : List (Airbender.NativeInitializationBatch.Proof R)) :
    initial ∈ Airbender.NativeInitializationSeedBoundary.initialTokens proofs := by
  apply List.mem_append_left
  exact List.mem_map.mpr ⟨12,List.mem_finRange _,rfl⟩

theorem terminal_member {R : Type} [Field R] (proofs : List (Airbender.NativeInitializationBatch.Proof R)) (inputs : PublicBoundary) :
    terminal inputs ∈ Airbender.NativeInitializationSeedBoundary.terminalTokens proofs inputs := by
  apply List.mem_append_left
  exact List.mem_map.mpr ⟨12,List.mem_finRange _,rfl⟩

theorem read_address (w : Nat → F) : (read w 42).address = address := by
  change (write w 42).address = address
  exact Airbender.NativeDelegationKeyAccountingProofs.control_address w

private theorem control_shape : (memoryAccess 42).readValue = #v[134,135] ∧
    (memoryAccess 42).writeValue = some #v[136,137] := ⟨rfl,rfl⟩

theorem read_limbs (w : Nat → F) : limbs (read w 42) = ((w 134).val,(w 135).val) := by
  change Nat.unpair (Nat.pair (keyValue w 42 false)[(0 : Fin 2)].val (keyValue w 42 false)[(1 : Fin 2)].val) = _
  rw [Nat.unpair_pair]
  simp [keyValue,control_shape.1]

theorem write_limbs (w : Nat → F) : limbs (write w 42) = ((w 136).val,(w 137).val) := by
  change Nat.unpair (Nat.pair (keyValue w 42 true)[(0 : Fin 2)].val (keyValue w 42 true)[(1 : Fin 2)].val) = _
  rw [Nat.unpair_pair]
  simp [keyValue,control_shape.1,control_shape.2]

theorem updated {w : Nat → F} (row : Airbender.NativeWorkerTransition.RowEffects w) : Updated (read w 42,write w 42) := by
  have result := Airbender.NativeWorkerTransitionProofs.control_result row.prior
  simpa only [Updated,read_limbs,write_limbs] using result

private def joint {Setup R : Type} [Field R] {batch : Airbender.NativeMainDecoder.Batch R}
    {workers : WorkerBatch Setup R} {inputs : PublicBoundary}
    (prior : Airbender.NativeCallerPosition.Effects batch workers inputs) : Airbender.NativeJointReplay.Effects batch workers inputs :=
  prior.prior.prior.prior

private def uniqueness {Setup R : Type} [Field R] {batch : Airbender.NativeMainDecoder.Batch R}
    {workers : WorkerBatch Setup R} {inputs : PublicBoundary}
    (prior : Airbender.NativeCallerPosition.Effects batch workers inputs) :
    Airbender.NativeMemoryWriteUniqueness.Effects batch.main.proofs workers inputs :=
  (joint prior).prior.prior.prior.words.prior.workers.prior.latest.unique

theorem classified {Setup R : Type} [Field R] {batch : Airbender.NativeMainDecoder.Batch R}
    {workers : WorkerBatch Setup R} {inputs : PublicBoundary}
    (prior : Airbender.NativeCallerPosition.Effects batch workers inputs) {edge : Token × Token}
    (member : edge ∈ Airbender.NativeMemoryRoots.steps batch.main.proofs workers)
    (same : edge.1.address = address) : MainEdge batch.main.proofs edge ∨
      ∃ w ∈ Airbender.NativeTokenLedger.workerRows workers, w constraintsABI.multiplicity = 1 ∧
        edge = (read w 42,write w 42) ∧ Updated edge := by
  obtain ⟨a,b⟩ := edge
  have actual := (Airbender.NativeMemoryRootsProofs.step_iff batch.main.proofs workers a b).mp member
  rcases actual with main | worker
  · obtain ⟨row,rm,port,pm,rfl,rfl⟩ := main
    left
    exact ⟨row,rm,List.mem_map.mpr ⟨port,by simpa using pm,rfl⟩⟩
  · obtain ⟨w,wm,active,slot,rfl,rfl⟩ := worker
    have equals : slot = 42 := (uniqueness prior).workerAddresses w wm active (by
      change (read w slot).address = (write w 42).address
      rw [same,Airbender.NativeDelegationKeyAccountingProofs.control_address])
    subst slot
    exact Or.inr ⟨w,wm,active,rfl,updated ((joint prior).prior.prior.transitions w wm)⟩

theorem from_prior {Setup R : Type} [Field R] {batch : Airbender.NativeMainDecoder.Batch R}
    {workers : WorkerBatch Setup R} {inputs : PublicBoundary}
    (prior : Airbender.NativeCallerPosition.Effects batch workers inputs) : Airbender.NativeControlHistory.Effects batch workers inputs := by
  have paths := (uniqueness prior).paths
  obtain ⟨sink,path,properties⟩ := paths.paths initial (initial_member batch.main.proofs)
  have equal : sink = terminal inputs := same_address Trace.MemoryToken.address paths.terminal properties.terminal
    (terminal_member batch.main.proofs inputs) (properties.address.trans (initial_address.trans (terminal_address inputs).symm))
  refine ⟨prior,path,properties.first,by simpa only [equal] using properties.last,properties.ordered,properties.distinct,?_,?_,?_⟩
  · simpa only [initial_address] using properties.ports
  · intro edge member
    have selected := List.mem_filter.mp (properties.ports.mem_iff.mp member)
    exact classified prior selected.1 (by simpa only [initial_address,decide_eq_true_eq] using selected.2)
  · intro w wm active
    have actual : Airbender.NativeMixedMemoryOrder.Step batch.main.proofs workers (read w 42) (write w 42) :=
      Or.inr ⟨w,wm,active,42,rfl,rfl⟩
    apply properties.ports.mem_iff.mpr
    apply List.mem_filter.mpr
    exact ⟨(Airbender.NativeMemoryRootsProofs.step_iff batch.main.proofs workers _ _).mpr actual,
      by simpa only [initial_address,decide_eq_true_eq] using read_address w⟩
open Airbender.Trace Airbender.ReducedMachine.Native
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
    Airbender.NativeControlHistory.Effects batch workers inputs :=
  from_prior (Airbender.NativeCallerPositionProofs.counted publicSetup embed memory ch pc gamma decoder config accepted image lookups identity)
end Airbender.NativeControlHistoryProofs
