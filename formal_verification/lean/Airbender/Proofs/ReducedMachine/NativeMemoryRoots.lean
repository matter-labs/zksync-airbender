import Airbender.Review.Circuits.ReducedMachine.MemoryRoots
import Airbender.Proofs.ReducedMachine.NativeMixedMemoryOrder

namespace Airbender.NativeMemoryRootsProofs
open Airbender.NativeMemoryRoots
open Airbender.Blake2Worker.Native Airbender.ReducedMachine.Native Airbender.ReducedMachine.NativeMemoryBoundary
set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false

/-- Generic duplicate-preserving partition before native row-domain data. -/
theorem split {A B : Type} (rows : List A) (active : A → Bool) (read write : A → List B)
    (same : ∀ row ∈ rows, active row = false → write row = read row) :
    (rows.flatMap write).Perm
      (rows.flatMap (fun row => if active row then write row else []) ++
        rows.flatMap (fun row => if active row then [] else read row)) := by
  apply Airbender.NativeInitializationLedgerProofs.split_rows
  intro row member
  cases flag : active row with
  | true => change (write row).Perm (write row ++ []); rw [List.append_nil]
  | false => change (write row).Perm (read row); rw [same row member flag]

/-- Logical memory cancellation in BOTH directions. No compressed factor is
    divided, and all copies of the common token list remain accounted for. -/
theorem cancel {A : Type} (initial terminal fullWrite fullRead activeWrite activeRead common : List A)
    (left : fullWrite.Perm (activeWrite ++ common))
    (right : fullRead.Perm (activeRead ++ common)) :
    (initial ++ fullWrite).Perm (terminal ++ fullRead) ↔
      (initial ++ activeWrite).Perm (terminal ++ activeRead) := by
  have l : (initial ++ fullWrite).Perm ((initial ++ activeWrite) ++ common) :=
    (left.append_left initial).trans (List.Perm.of_eq (List.append_assoc _ _ _).symm)
  have r : (terminal ++ fullRead).Perm ((terminal ++ activeRead) ++ common) :=
    (right.append_left terminal).trans (List.Perm.of_eq (List.append_assoc _ _ _).symm)
  constructor
  · intro matching
    have equality := Multiset.coe_eq_coe.mpr (l.symm.trans (matching.trans r))
    apply Multiset.coe_eq_coe.mp
    simpa only [← Multiset.coe_add,add_right_cancel_iff] using equality
  · intro matching
    exact l.trans ((matching.append_right common).trans r.symm)

/-- Generic well-founded seed paths. The edge list retains every occurrence;
    rank is used only in this proof and does not recode the token. -/
theorem rooted {A : Type} (initial terminal : List A) (edges : List (A × A)) (rank : A → Nat)
    (matching : (initial ++ edges.map Prod.snd).Perm (terminal ++ edges.map Prod.fst))
    (strict : ∀ edge ∈ edges, rank edge.1 < rank edge.2) :
    ∀ token ∈ edges.map Prod.fst, ∃ seed ∈ initial,
      Relation.ReflTransGen (fun a b => (a,b) ∈ edges) seed token := by
  have induction : ∀ n, ∀ token ∈ edges.map Prod.fst, rank token = n →
      ∃ seed ∈ initial, Relation.ReflTransGen (fun a b => (a,b) ∈ edges) seed token := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro token member rankEq
      rcases Airbender.NativeMemoryHistoryProofs.matched_read matching member with seed | writer
      · exact ⟨token,seed,Relation.ReflTransGen.refl⟩
      · obtain ⟨edge,present,same⟩ := List.mem_map.mp writer
        have smaller := strict edge present
        have predecessor : edge.1 ∈ edges.map Prod.fst := List.mem_map.mpr ⟨edge,present,rfl⟩
        obtain ⟨seed,inSeed,path⟩ := ih (rank edge.1) (by rw [same,rankEq] at smaller; exact smaller)
          edge.1 predecessor rfl
        exact ⟨seed,inSeed,by rw [← same]; exact path.tail present⟩
  intro token member
  exact induction (rank token) token member rfl

theorem main_projection (rows : List Airbender.NativeMixedMemoryOrder.MainRow) (write : Bool) :
    ((rows.flatMap Trace.Row.memorySteps).map (if write then Prod.snd else Prod.fst)) =
      rows.flatMap (fun row => if write then row.writes else row.reads) := by
  rw [List.map_flatMap]
  apply congrArg (fun f => rows.flatMap f)
  funext row
  cases write with
  | false => simp [Trace.Row.memorySteps,Trace.Row.reads,List.map_map]
  | true => simp [Trace.Row.memorySteps,Trace.Row.writes,List.map_map]

theorem worker_projection (w : Nat → F) (write : Bool) :
    (workerSteps w).map (if write then Prod.snd else Prod.fst) = Airbender.NativeMemoryTokens.workerTokens w write := by
  cases write <;> rfl

/-- Abstract list projection before native proof/batch/domain instantiation. -/
theorem projections (rows : List Airbender.NativeMixedMemoryOrder.MainRow) (workers : List (Nat → F)) (write : Bool) :
    ((rows.flatMap Trace.Row.memorySteps ++ workers.flatMap (fun w =>
      if w constraintsABI.multiplicity = 1 then workerSteps w else [])).map (if write then Prod.snd else Prod.fst)) =
      rows.flatMap (fun row => if write then row.writes else row.reads) ++
        workers.flatMap (fun w => if w constraintsABI.multiplicity = 1 then Airbender.NativeMemoryTokens.workerTokens w write else []) := by
  rw [List.map_append,main_projection,List.map_flatMap]
  congr 1
  apply congrArg (fun f => workers.flatMap f)
  funext w
  by_cases active : w constraintsABI.multiplicity = 1
  · rw [if_pos active,if_pos active]
    exact worker_projection w write
  · rw [if_neg active,if_neg active]
    rfl

theorem step_iff {Setup R : Type} [Field R]
    (proofs : List (Airbender.NativeInitializationBatch.Proof R)) (batch : WorkerBatch Setup R) (read write : Token) :
    (read,write) ∈ steps proofs batch ↔ Airbender.NativeMixedMemoryOrder.Step proofs batch read write := by
  constructor
  · intro member
    rcases List.mem_append.mp member with main | worker
    · obtain ⟨row,present,source⟩ := List.mem_flatMap.mp main
      obtain ⟨port,actual,same⟩ := List.mem_map.mp source
      cases same
      exact Or.inl ⟨row,present,port,by simpa using actual,rfl,rfl⟩
    · obtain ⟨w,present,source⟩ := List.mem_flatMap.mp worker
      split at source
      next active =>
        obtain ⟨slot,_,same⟩ := List.mem_map.mp source
        cases same
        exact Or.inr ⟨w,present,active,slot,rfl,rfl⟩
      next inactive => exact False.elim (List.not_mem_nil source)
  · rintro (⟨row,member,port,actual,rfl,rfl⟩ | ⟨w,member,active,slot,rfl,rfl⟩)
    · exact List.mem_append_left _ (List.mem_flatMap.mpr ⟨row,member,List.mem_map.mpr
        ⟨port,by simpa using actual,rfl⟩⟩)
    · apply List.mem_append_right
      apply List.mem_flatMap.mpr
      refine ⟨w,member,?_⟩
      rw [if_pos active]
      exact List.mem_map.mpr ⟨slot,List.mem_finRange _,rfl⟩

theorem inactive_equal {w : Nat → F} (accepted : LocalProcessingAccepted w)
    (zero : w constraintsABI.multiplicity = 0) :
    Airbender.NativeMemoryTokens.workerTokens w true = Airbender.NativeMemoryTokens.workerTokens w false := by
  have keys := (Airbender.Blake2Worker.MemoryKeyProofs.padding_keys accepted).equalKeys zero
  apply List.map_congr_left
  intro slot _
  exact congrArg Airbender.NativeMemoryTokens.encodeKey (keys slot).symm

theorem partition {Setup R : Type} [Field R]
    (proofs : List (Airbender.NativeInitializationBatch.Proof R)) (batch : WorkerBatch Setup R)
    (processing : ∀ w ∈ Airbender.NativeTokenLedger.workerRows batch, LocalProcessingAccepted w) (write : Bool) :
    (Airbender.NativeInitializationSeedBoundary.accessTokens proofs batch write).Perm
      (tokens proofs batch write ++ inactiveTokens batch) := by
  have common : ∀ w ∈ Airbender.NativeTokenLedger.workerRows batch,
      decide (w constraintsABI.multiplicity = 1) = false →
        Airbender.NativeMemoryTokens.workerTokens w write = Airbender.NativeMemoryTokens.workerTokens w false := by
    intro w member inactive
    have bit := (Airbender.Blake2Worker.ProcessingProofs.effects (processing w member).conventions).multiplicityBit
    have zero : w constraintsABI.multiplicity = 0 := bit.resolve_right (of_decide_eq_false inactive)
    cases write
    · rfl
    · exact inactive_equal (processing w member) zero
  have workers := split (Airbender.NativeTokenLedger.workerRows batch)
    (fun w => decide (w constraintsABI.multiplicity = 1))
    (fun w => Airbender.NativeMemoryTokens.workerTokens w false)
    (fun w => Airbender.NativeMemoryTokens.workerTokens w write) common
  simp only [decide_eq_true_eq] at workers
  have main := Airbender.NativeMemoryHistoryProofs.main_projection proofs write
  have projection := projections (Airbender.NativeMixedMemoryOrder.mainRows proofs)
    (Airbender.NativeTokenLedger.workerRows batch) write
  change (Airbender.NativeInitializationSeedBoundary.accessTokens proofs batch write).Perm
    (((steps proofs batch).map (if write then Prod.snd else Prod.fst)) ++ inactiveTokens batch)
  rw [show (steps proofs batch).map (if write then Prod.snd else Prod.fst) = _ from projection]
  unfold Airbender.NativeInitializationSeedBoundary.accessTokens
  rw [← main]
  exact (workers.append_left _).trans (List.Perm.of_eq (List.append_assoc _ _ _).symm)

/-- The full memory permutation iff its active ledger, with every common
    inactive token cancelled on BOTH sides. No source acceptance is weakened. -/
theorem matching_iff {Setup R : Type} [Field R]
    (proofs : List (Airbender.NativeInitializationBatch.Proof R)) (batch : WorkerBatch Setup R) (inputs : PublicBoundary)
    (processing : ∀ w ∈ Airbender.NativeTokenLedger.workerRows batch, LocalProcessingAccepted w) :
    (Airbender.NativeInitializationSeedBoundary.initialTokens proofs ++
      Airbender.NativeInitializationSeedBoundary.accessTokens proofs batch true).Perm
        (Airbender.NativeInitializationSeedBoundary.terminalTokens proofs inputs ++
          Airbender.NativeInitializationSeedBoundary.accessTokens proofs batch false) ↔
    (Airbender.NativeInitializationSeedBoundary.initialTokens proofs ++ tokens proofs batch true).Perm
      (Airbender.NativeInitializationSeedBoundary.terminalTokens proofs inputs ++ tokens proofs batch false) :=
  cancel _ _ _ _ _ _ _ (partition proofs batch processing true) (partition proofs batch processing false)

theorem effects {Setup R : Type} [Field R] (embed : F →+* R) (memory : MemoryKeyChallenges R)
    (ch : CSRArgumentChallenges R) (pc : PCChallenges R) (gamma : R) (config : WorkerConfiguration Setup)
    {proofs : List (Airbender.NativeInitializationBatch.Proof R)} {batch : WorkerBatch Setup R}
    {inputs : PublicBoundary} {inverse : BoundaryInverses R}
    (accepted : Airbender.NativeInitializationBatch.Accepted embed memory ch pc gamma config proofs batch inputs inverse)
    (identity : Airbender.NativeDelegationSupport.SourceIdentity proofs batch) : Effects proofs batch inputs := by
  have order := Airbender.NativeMixedMemoryOrderProofs.effects embed memory ch pc gamma config accepted identity
  have processing := Airbender.NativeActiveWorkerClockProofs.worker_processing embed memory ch pc gamma config accepted
  have parts := partition proofs batch processing
  have matching := (cancel _ _ _ _ _ _ _ (parts true) (parts false)).mp
    (Airbender.NativeInitializationSeedBoundaryProofs.memory_matching accepted.matching)
  have strict : ∀ edge ∈ steps proofs batch,
      (Airbender.NativeWorkerSignedClocks.value edge.1.time).toNat <
        (Airbender.NativeWorkerSignedClocks.value edge.2.time).toNat := by
    intro edge member
    have actual := (step_iff proofs batch edge.1 edge.2).mp member
    have increases := order.steps _ _ actual
    have nonnegative := order.workers.reads _ (Airbender.NativeMixedMemoryOrderProofs.step_read_member actual)
    omega
  have roots := rooted (Airbender.NativeInitializationSeedBoundary.initialTokens proofs)
    (Airbender.NativeInitializationSeedBoundary.terminalTokens proofs inputs) (steps proofs batch)
    (fun token => (Airbender.NativeWorkerSignedClocks.value token.time).toNat) matching strict
  have reads : ∀ read write, Airbender.NativeMixedMemoryOrder.Step proofs batch read write →
      ∃ seed ∈ Airbender.NativeInitializationSeedBoundary.initialTokens proofs,
        Relation.ReflTransGen (Airbender.NativeMixedMemoryOrder.Step proofs batch) seed read := by
    intro read write actual
    have member := (step_iff proofs batch read write).mpr actual
    obtain ⟨seed,inSeed,path⟩ := roots read (List.mem_map.mpr ⟨(read,write),member,rfl⟩)
    exact ⟨seed,inSeed,path.mono (fun _ _ edge => (step_iff proofs batch _ _).mp edge)⟩
  refine ⟨order,parts,matching,reads,?_⟩
  intro read write actual
  obtain ⟨seed,inSeed,path⟩ := reads read write actual
  exact ⟨seed,inSeed,path.tail actual⟩

theorem counted {Setup R : Type} [Field R] (embed : F →+* R) (memory : MemoryKeyChallenges R)
    (ch : CSRArgumentChallenges R) (pc : PCChallenges R) (gamma : R) (config : WorkerConfiguration Setup)
    {batch : Airbender.NativeMainBatch.Batch R} {workers : WorkerBatch Setup R}
    {inputs : PublicBoundary} {inverse : BoundaryInverses R}
    (accepted : Airbender.NativeMainBatch.SourceAccepted embed memory ch pc gamma config batch workers inputs inverse)
    (identity : Airbender.NativeDelegationSupport.SourceIdentity batch.proofs workers) :
    Airbender.NativeMainBatch.Effects batch ∧ Effects batch.proofs workers inputs :=
  ⟨Airbender.NativeMainBatchProofs.effects batch accepted.counter,
    effects embed memory ch pc gamma config accepted.component identity⟩
end Airbender.NativeMemoryRootsProofs
