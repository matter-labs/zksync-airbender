import Airbender.Review.Trace.Families.ReducedMachine.JointReplay
import Airbender.Proofs.ReducedMachine.NativeWorkerGroup
namespace Airbender.NativeJointReplayProofs
open Airbender.NativeJointReplay Airbender.NativeMixedReplay
set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false

theorem uniform_order {A : Type} (rank : A → Nat) (time : Nat) (items : List A)
    (same : ∀ item ∈ items, rank item = time) : items.Pairwise (fun a b => rank a ≤ rank b) := by
  induction items with
  | nil => exact .nil
  | cons first tail ih =>
    apply List.pairwise_cons.mpr
    exact ⟨fun item member => by rw [same first (by simp),same item (by simp [member])],
      ih (fun item member => same item (List.mem_cons_of_mem _ member))⟩

theorem flat_order {A G : Type} (rank : A → Nat) (edges : G → List (A × A)) (time : G → Nat)
    (groups : List G) (same : ∀ group ∈ groups, ∀ edge ∈ edges group, rank edge.2 = time group)
    (ordered : groups.Pairwise (fun a b => time a ≤ time b)) :
    (groups.flatMap edges).Pairwise (fun a b => rank a.2 ≤ rank b.2) := by
  induction groups with
  | nil => exact .nil
  | cons first tail ih =>
    have order := List.pairwise_cons.mp ordered
    apply List.pairwise_append.mpr
    refine ⟨uniform_order (fun edge => rank edge.2) (time first) (edges first) (same first (by simp)),
      ih (fun group member => same group (List.mem_cons_of_mem _ member)) order.2,?_⟩
    intro a am b bm
    obtain ⟨group,gm,bm⟩ := List.mem_flatMap.mp bm
    rw [same first (by simp) a am,same group (List.mem_cons_of_mem _ gm) b bm]
    exact order.1 group gm

/-- Split ONE flattened replay at every block boundary. Early-read progress and
    weak common-write ordering derive all common pre-state reads at every step. -/
theorem pack {A K G : Type} (key : A → K) (rank : A → Nat)
    (edges : G → List (A × A)) (time : G → Nat) (groups : List G)
    {state terminal : List A}
    (run : Replay key state (groups.flatMap edges) terminal)
    (same : ∀ group ∈ groups, ∀ edge ∈ edges group, rank edge.2 = time group)
    (progress : ∀ group ∈ groups, ∀ edge ∈ edges group, rank edge.1 < time group)
    (ordered : groups.Pairwise (fun a b => time a ≤ time b)) :
    BatchReplay key edges state groups terminal := by
  induction groups generalizing state with
  | nil => exact .done run
  | cons first tail ih =>
    have order := List.pairwise_cons.mp ordered
    have later : ∀ edge ∈ (first :: tail).flatMap edges, time first ≤ rank edge.2 := by
      intro edge member
      obtain ⟨group,gm,em⟩ := List.mem_flatMap.mp member
      rw [same group gm edge em]
      rcases List.mem_cons.mp gm with rfl | gm
      · exact Nat.le_refl _
      · exact order.1 group gm
    have reads : ∀ edge ∈ edges first, edge.1 ∈ state := by
      intro edge member
      exact Airbender.NativeWorkerSnapshotProofs.early_read key rank (time first) run later
        (List.mem_flatMap.mpr ⟨first,by simp,member⟩) (progress first (by simp) edge member)
    obtain ⟨post,block,next⟩ := Airbender.NativeWorkerSnapshotProofs.split_replay key
      (edges first) (tail.flatMap edges) run
    exact .step reads block (ih next
      (fun group member => same group (List.mem_cons_of_mem _ member))
      (fun group member => progress group (List.mem_cons_of_mem _ member)) order.2)

theorem batch_exists {A K G : Type} [DecidableEq A] (key : A → K) (rank : A → Nat)
    (edges : G → List (A × A)) (time : G → Nat) (groups : List G) (state terminal : List A)
    (unique : (state.map key).Nodup)
    (matched : (state ++ (groups.flatMap edges).map Prod.snd).Perm
      (terminal ++ (groups.flatMap edges).map Prod.fst))
    (address : ∀ edge ∈ groups.flatMap edges, key edge.1 = key edge.2)
    (same : ∀ group ∈ groups, ∀ edge ∈ edges group, rank edge.2 = time group)
    (progress : ∀ group ∈ groups, ∀ edge ∈ edges group, rank edge.1 < time group) :
    ∃ ordered, ordered.Perm groups ∧ ordered.Pairwise (fun a b => time a ≤ time b) ∧
      BatchReplay key edges state ordered terminal := by
  let ordered := groups.mergeSort (fun a b => decide (time a ≤ time b))
  have permutation : ordered.Perm groups := List.mergeSort_perm _ _
  have order : ordered.Pairwise (fun a b => time a ≤ time b) := by
    have sorted := List.pairwise_mergeSort
      (le := fun a b : G => decide (time a ≤ time b))
      (by intro a b c ab bc; simp only [decide_eq_true_eq] at *; omega)
      (by intro a b; simp only [Bool.or_eq_true,decide_eq_true_eq]; omega) groups
    simpa only [decide_eq_true_eq] using sorted
  have flat := List.Perm.flatMap_right edges permutation
  have common : ∀ group ∈ ordered, ∀ edge ∈ edges group, rank edge.2 = time group :=
    fun group member => same group (permutation.mem_iff.mp member)
  have before : ∀ group ∈ ordered, ∀ edge ∈ edges group, rank edge.1 < time group :=
    fun group member => progress group (permutation.mem_iff.mp member)
  have run := Airbender.NativeMixedReplayProofs.replay_sorted key rank (ordered.flatMap edges) state terminal unique
    (((flat.map Prod.snd).append_left state).trans
      (matched.trans ((flat.map Prod.fst).append_left terminal).symm))
    (fun edge member => address edge (flat.mem_iff.mp member))
    (by intro edge member; obtain ⟨group,gm,em⟩ := List.mem_flatMap.mp member
        rw [common group gm edge em]; exact before group gm edge em)
    (flat_order rank edges time ordered common order)
  exact ⟨ordered,permutation,order,pack key rank edges time ordered run common before order⟩
/-- Locate any selected label without changing the shared execution. -/
theorem locate {A K G : Type} (key : A → K) (edges : G → List (A × A))
    {state terminal : List A} {groups : List G}
    (run : BatchReplay key edges state groups terminal) {group : G} (member : group ∈ groups) :
    ∃ before after prior rest, groups = prior ++ group :: rest ∧
      BatchReplay key edges state prior before ∧
      (∀ edge ∈ edges group, edge.1 ∈ before) ∧ Replay key before (edges group) after ∧
      BatchReplay key edges after rest terminal := by
  induction run with
  | done _ => simp at member
  | @step state post terminal first tail reads block next ih =>
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨state,post,[],tail,rfl,.done (.done
        (Airbender.NativeMixedReplayProofs.initial_unique key block) (.refl _)),reads,block,next⟩
    · obtain ⟨before,after,prior,rest,equal,firstRun,current,lastRun⟩ := ih member
      exact ⟨before,after,first :: prior,rest,by simp only [List.cons_append,equal],
        .step reads block firstRun,current,lastRun⟩

open Airbender.NativeWorkerSnapshot Airbender.Blake2Worker.Native
open Airbender.ReducedMachine.Native Airbender.Trace Airbender.Verification
open Airbender.ReducedMachine.NativeMemoryBoundary

theorem source_flatten {Setup R : Type} [Field R]
    (proofs : List (Airbender.NativeInitializationBatch.Proof R)) (workers : WorkerBatch Setup R) :
    (groups proofs workers).flatMap edges = Airbender.NativeMemoryRoots.steps proofs workers := by
  have main (items : List (Token × Token)) :
      (items.map Group.main).flatMap edges = items := by simp [List.flatMap_map,edges]
  have worker (items : List (Nat → F)) :
      (items.flatMap (fun w => if w constraintsABI.multiplicity = 1 then [Group.worker w] else [])).flatMap edges =
      items.flatMap (fun w => if w constraintsABI.multiplicity = 1 then Airbender.NativeWorkerGroup.ports w else []) := by
    induction items with
    | nil => rfl
    | cons w tail ih =>
      by_cases h : w constraintsABI.multiplicity = 1 <;> simp [h,ih,edges]
  simp only [groups,List.flatMap_append,main,worker,Airbender.NativeMemoryRoots.steps,Airbender.NativeWorkerGroup.ports]

theorem common_write (group : Group) (edge : Token × Token) (member : edge ∈ edges group) :
    Airbender.NativeCompleteMemoryPaths.rank edge.2 = time group := by
  cases group with
  | main other =>
    have equal : edge = other := List.mem_singleton.mp member
    subst edge
    rfl
  | worker w =>
    obtain ⟨slot,_,rfl⟩ := List.mem_map.mp member
    exact Airbender.NativeWorkerSnapshotProofs.common_rank w slot

theorem worker_member {Setup R : Type} [Field R]
    (proofs : List (Airbender.NativeInitializationBatch.Proof R)) (workers : WorkerBatch Setup R)
    {w : Nat → F} (member : w ∈ Airbender.NativeTokenLedger.workerRows workers)
    (active : w constraintsABI.multiplicity = 1) : Group.worker w ∈ groups proofs workers := by
  apply List.mem_append_right
  exact List.mem_flatMap.mpr ⟨w,member,by simp [active]⟩

theorem worker_effect (w : Nat → F) {before after : List Token}
    (reads : ∀ edge ∈ edges (.worker w), edge.1 ∈ before)
    (block : Replay Trace.MemoryToken.address before (edges (.worker w)) after)
    (addresses : Function.Injective (fun slot : Fin 43 => (write w slot).address))
    (transition : Airbender.NativeWorkerTransition.RowEffects w) : WorkerEffect w before after := by
  have oldUnique := Airbender.NativeMixedReplayProofs.initial_unique Trace.MemoryToken.address block
  have newUnique := Airbender.NativeWorkerGroupProofs.terminal_unique Trace.MemoryToken.address block
  have distinct : ((edges (.worker w)).map fun edge => edge.2.address).Nodup := by
    change ((List.finRange 43).map fun slot => (write w slot).address).Nodup
    exact (List.nodup_finRange 43).map addresses
  have old : ∀ slot, read w slot ∈ before := fun slot =>
    reads _ (Airbender.NativeWorkerGroupProofs.port_member w slot)
  have fresh : ∀ slot, write w slot ∈ after := fun slot =>
    Airbender.NativeWorkerGroupProofs.writes_present Trace.MemoryToken.address block distinct _
      (Airbender.NativeWorkerGroupProofs.port_member w slot)
  refine ⟨old,oldUnique,newUnique,fresh,?_,?_,?_,Airbender.NativeWorkerGroupProofs.readonly_value w⟩
  · intro slot token present same
    exact List.inj_on_of_nodup_map newUnique present (fresh slot) same
  · intro token outside
    apply Airbender.NativeWorkerGroupProofs.frame Trace.MemoryToken.address block token
    intro edge member
    obtain ⟨slot,_,rfl⟩ := List.mem_map.mp member
    exact outside slot
  · intro oldSamples newSamples oldPresent newPresent
    have oldSame : oldSamples = read w := by
      funext slot
      exact List.inj_on_of_nodup_map oldUnique (oldPresent slot).1 (old slot) (oldPresent slot).2
    have newSame : newSamples = write w := by
      funext slot
      exact List.inj_on_of_nodup_map newUnique (newPresent slot).1 (fresh slot) (newPresent slot).2
    rw [oldSame,newSame,Airbender.NativeWorkerGroupProofs.sampled_output,
      Airbender.NativeWorkerSnapshotProofs.sampled_input]
    exact transition.result

theorem from_prior {Setup R : Type} [Field R]
    {batch : Airbender.NativeMainDecoder.Batch R} {workers : WorkerBatch Setup R} {inputs : PublicBoundary}
    (prior : Airbender.NativeWorkerGroup.Effects batch workers inputs) : Airbender.NativeJointReplay.Execution batch.main.proofs workers inputs := by
  obtain ⟨old,permutation,_,run⟩ := prior.prior.prior.replay
  have roots := prior.prior.prior.words.prior.workers.prior.latest.unique.paths.keys.addresses.roots
  have source := source_flatten batch.main.proofs workers
  have member : ∀ group ∈ groups batch.main.proofs workers, ∀ edge ∈ edges group,
      edge ∈ Airbender.NativeMemoryRoots.steps batch.main.proofs workers := by
    intro group gm edge em
    rw [← source]
    exact List.mem_flatMap.mpr ⟨group,gm,em⟩
  obtain ⟨ordered,same,order,joint⟩ := batch_exists Trace.MemoryToken.address
    Airbender.NativeCompleteMemoryPaths.rank edges time (groups batch.main.proofs workers)
    (Airbender.NativeInitializationSeedBoundary.initialTokens batch.main.proofs)
    (Airbender.NativeInitializationSeedBoundary.terminalTokens batch.main.proofs inputs)
    (Airbender.NativeMixedReplayProofs.initial_unique Trace.MemoryToken.address run)
    (by rw [source]; exact ((permutation.map Prod.snd).append_left _).symm.trans
          ((Airbender.NativeWorkerGroupProofs.balance Trace.MemoryToken.address run).trans
            ((permutation.map Prod.fst).append_left _)))
    (by intro edge em; rw [source] at em; exact Airbender.NativeCompleteMemoryPathProofs.step_address em)
    (fun group _ edge em => common_write group edge em)
    (by intro group gm edge em; rw [← common_write group edge em]
        exact Airbender.NativeCompleteMemoryPathProofs.step_rank roots.order (member group gm edge em))
  refine ⟨ordered,same,order,by simpa only [source] using List.Perm.flatMap_right edges same,joint,?_⟩
  intro w wm active
  obtain ⟨before,after,priorGroups,suffix,shape,first,reads,block,last⟩ := locate Trace.MemoryToken.address edges joint
    (same.mem_iff.mpr (worker_member batch.main.proofs workers wm active))
  exact ⟨before,after,⟨priorGroups,suffix,shape,first,block,last⟩,
    worker_effect w reads block
      (prior.prior.prior.words.prior.workers.prior.latest.unique.workerAddresses w wm active)
      (prior.prior.transitions w wm)⟩

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
    (identity : Airbender.NativeDelegationSupport.SourceIdentity batch.main.proofs workers) : Airbender.NativeJointReplay.Effects batch workers inputs := by
  have prior := Airbender.NativeWorkerGroupProofs.counted publicSetup embed memory ch pc gamma decoder config accepted image lookups identity
  exact ⟨prior,from_prior prior⟩
end Airbender.NativeJointReplayProofs
