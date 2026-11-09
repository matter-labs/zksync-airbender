import Airbender.Review.Trace.Families.ReducedMachine.ControlOrigin
import Airbender.Proofs.ReducedMachine.NativeControlHistory
import Airbender.Proofs.ReducedMachine.NativeCSRPorts

namespace Airbender.NativeControlOriginProofs
open Airbender.NativeControlHistory Airbender.NativeWorkerSnapshot
open Airbender.Blake2Worker.Native Airbender.ReducedMachine.NativeMemoryBoundary
private abbrev MainRow := Airbender.NativeMixedMemoryOrder.MainRow
set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false

theorem sampled_rows {A B : Type} (objects : List A) (samples : A → Nat → B)
    (count : Nat) (active : B → Bool) (property : B → Prop)
    (checked : ∀ object ∈ objects, ∀ i < count, active (samples object i) = true → property (samples object i)) :
    ∀ sample ∈ (objects.flatMap fun object => (List.range count).map (samples object)).filter active, property sample := by
  intro sample member
  have selected := List.mem_filter.mp member
  obtain ⟨object,present,sampled⟩ := List.mem_flatMap.mp selected.1
  obtain ⟨i,bound,rfl⟩ := List.mem_map.mp sampled
  exact checked object present i (List.mem_range.mp bound) selected.2


/-- The first departure from zero occurs at an actual adjacent edge, before the
    chosen target in the same strictly ordered path. Abstract lists only. -/
theorem zero_origin {A : Type} (value rank : A → Nat) (head : A) (tail : List A)
    (zero : value head = 0) (ordered : ((head::tail).map rank).Pairwise (· < ·))
    {target : A} (member : target ∈ head::tail) (nonzero : value target ≠ 0) :
    ∃ a b, (a,b) ∈ (head::tail).zip (head::tail).tail ∧ value a = 0 ∧ value b ≠ 0 ∧ rank b ≤ rank target := by
  induction tail generalizing head with
  | nil =>
    have same : target = head := by simpa using member
    exact False.elim (nonzero (same ▸ zero))
  | cons next rest ih =>
    rcases List.mem_cons.mp member with same | later
    · subst target; exact False.elim (nonzero zero)
    · have tailOrder : ((next::rest).map rank).Pairwise (· < ·) := (List.pairwise_cons.mp ordered).2
      by_cases nextZero : value next = 0
      · obtain ⟨a,b,edge,az,bnz,before⟩ := ih next nextZero tailOrder later
        exact ⟨a,b,List.mem_cons_of_mem _ edge,az,bnz,before⟩
      · refine ⟨head,next,by simp,zero,nextZero,?_⟩
        rcases List.mem_cons.mp later with same | further
        · subst target; exact le_refl _
        · exact Nat.le_of_lt ((List.pairwise_cons.mp tailOrder).1 (rank target) (List.mem_map.mpr ⟨target,further,rfl⟩))

private theorem port_slot (row : MainRow) (actual : Trace.MemoryPort) (member : actual ∈ row.ports) :
    ∃ slot : Fin 3, actual = Airbender.NativeMainDependencies.port slot := by
  cases row with
  | mk family w =>
    cases family
    change actual ∈ Airbender.ReducedMachine.Native.importedConstraintsMemoryPorts at member
    simp [Airbender.ReducedMachine.Native.importedConstraintsMemoryPorts] at member
    rcases member with rfl | rfl | rfl
    · exact ⟨0,rfl⟩
    · exact ⟨1,rfl⟩
    · exact ⟨2,rfl⟩

private theorem actual_write (row : MainRow) (slot : Fin 3) :
    Trace.writeToken row.columns row.assignment (Airbender.NativeMainDependencies.port slot) =
      Airbender.NativeMainDependencies.write row.assignment slot := by
  cases row with
  | mk family w => cases family; rfl

theorem third_of_change {row : MainRow} {edge : Token × Token}
    (member : edge ∈ row.memorySteps) (changed : edge.1.value ≠ edge.2.value) :
    edge = (Airbender.NativeMainDependencies.read row.assignment 2,Airbender.NativeMainDependencies.write row.assignment 2) := by
  obtain ⟨port,pm,rfl⟩ := List.mem_map.mp member
  obtain ⟨slot,rfl⟩ := port_slot row port (by simpa using pm)
  rw [actual_write] at changed ⊢
  fin_cases slot
  · exact False.elim (changed rfl)
  · exact False.elim (changed rfl)
  · rfl

theorem worker_zero (edge : Token × Token) (update : Updated edge) (zero : (limbs edge.1).2 = 0) :
    (limbs edge.2).2 = 0 := by
  rw [update.2,zero]
  rfl

theorem main_origin {Setup R : Type} [Field R] {proofs : List (Airbender.NativeInitializationBatch.Proof R)}
    {workers : WorkerBatch Setup R} {inputs : PublicBoundary} {path : List Token}
    (history : History proofs workers inputs path) {target : Token} (member : target ∈ path)
    (nonzero : (limbs target).2 ≠ 0) :
    ∃ edge ∈ path.zip path.tail, MainEdge proofs edge ∧ (limbs edge.1).2 = 0 ∧ (limbs edge.2).2 ≠ 0 ∧
      Airbender.NativeCompleteMemoryPaths.rank edge.2 ≤ Airbender.NativeCompleteMemoryPaths.rank target := by
  cases path with
  | nil => simp at member
  | cons head tail =>
    have initial : head = Airbender.NativeControlHistory.initial := Option.some.inj history.first
    have zero : (limbs head).2 = 0 := by rw [initial,Airbender.NativeControlHistoryProofs.initial_zero]
    obtain ⟨a,b,present,az,bnz,before⟩ := zero_origin (fun token : Token => (limbs token).2)
      Airbender.NativeCompleteMemoryPaths.rank head tail zero history.ordered member nonzero
    have classified := history.classified (a,b) present
    rcases classified with main | worker
    · exact ⟨(a,b),present,main,az,bnz,before⟩
    · obtain ⟨w,wm,active,same,update⟩ := worker
      exact False.elim (bnz (worker_zero (a,b) update az))
open Airbender.ReducedMachine Airbender.ReducedMachine.Native Airbender.Trace

theorem query_rd {Kind : Type} {w : Nat → F} {entry : ProgramEntry Kind}
    (query : decoderQuery w = entry.query) : (w 7).val = entry.data.rd.toNat := by
  have field := congrArg (fun q : Vector F 10 => q[(4 : Fin 10)]) query
  change w 7 = (entry.data.rd.toNat : F) at field
  rw [field,ZMod.val_natCast_of_lt (lt_trans entry.data.rd.isLt (by decide))]

theorem routed_rd {Kind : Type} {w : Nat → F} {entry : ProgramEntry Kind}
    (query : decoderQuery w = entry.query)
    (route : importedConstraintsMemoryPorts[2].address.code w = (Cell.register entry.data.rd).addressCode)
    (same : (Airbender.NativeMainDependencies.read w 2).address = address) : (w 7).val = 12 := by
  have coded : entry.data.rd.toNat = 12 := by
    have pair := congrArg (fun n => (Nat.unpair (Nat.unpair n).2).1) (route.symm.trans same)
    simpa only [Cell.addressCode,Nat.unpair_pair] using pair
  exact (query_rd query).trans coded

theorem supported_rd {w : Nat → F} {entry : SupportedProgramEntry}
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints NativeFixed.table))
    (fields : supportedDecoderFields entry.instruction = some entry.data) (query : decoderQuery w = entry.query)
    (same : (Airbender.NativeMainDependencies.read w 2).address = address) : (w 7).val = 12 := by
  rcases NativeSupportedDecoderProofs.entry_profile fields with shift | arithmetic | bitwise | comparison | branch | jump
  · obtain ⟨selected,_,_,_,source,equal⟩ := shift
    exact routed_rd (query.trans equal.symm) (NativeShiftPortProofs.register_addresses holds source (query.trans equal.symm) 2) same
  · obtain ⟨selected,_,_,_,source,equal⟩ := arithmetic
    exact routed_rd (query.trans equal.symm) (NativeArithmeticPortProofs.register_addresses holds source (query.trans equal.symm) 2) same
  · obtain ⟨selected,_,_,_,source,equal⟩ := bitwise
    exact routed_rd (query.trans equal.symm) (NativeBitwisePortProofs.register_addresses holds source (query.trans equal.symm) 2) same
  · obtain ⟨selected,_,_,_,source,equal⟩ := comparison
    exact routed_rd (query.trans equal.symm) (NativeComparisonPortProofs.register_addresses holds source (query.trans equal.symm) 2) same
  · obtain ⟨selected,_,_,_,source,equal⟩ := branch
    exact routed_rd (query.trans equal.symm) (NativeBranchPortProofs.register_addresses holds source (query.trans equal.symm) 2) same
  · obtain ⟨selected,_,_,_,source,equal⟩ := jump
    exact routed_rd (query.trans equal.symm) (NativeJumpPortProofs.register_addresses holds source (query.trans equal.symm) 2) same

theorem unified_rd {w : Nat → F} {entry : UnifiedProgramEntry}
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints NativeRuntimePool.table))
    (fields : unifiedDecoderFields entry.instruction = some entry.data) (query : decoderQuery w = entry.query)
    (same : (Airbender.NativeMainDependencies.read w 2).address = address) : (w 7).val = 12 := by
  have fixed := Airbender.NativeDecodedQueryDomainProofs.fixed_body holds fields query
  rcases NativeUnifiedDecoderProofs.entry_profile fields with ordinary | memory
  · obtain ⟨selected,_,_,_,source,_,equal⟩ := ordinary
    exact supported_rd fixed source (query.trans equal.symm) same
  · obtain ⟨selected,_,_,_,source,_,equal⟩ := memory
    have route := NativeWordMemoryPortProofs.addresses fixed source (query.trans equal.symm) 2
    cases family : selected.data.family with
    | false =>
      have register : importedConstraintsMemoryPorts[2].address.code w = (Cell.register selected.data.rd).addressCode := by
        simpa [wordMemoryPortCells,family] using route
      exact routed_rd (query.trans equal.symm) register same
    | true =>
      have space := congrArg (fun n => (Nat.unpair n).1) (route.symm.trans same)
      simp [wordMemoryPortCells,family,Cell.addressCode,Nat.unpair_pair] at space

theorem public_rd {w : Nat → F} {entry : Airbender.NativeCallerDecoder.Program}
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints NativeRuntimePool.table))
    (fields : Airbender.NativeCallerDecoder.decoderFields entry.instruction = some entry.data) (query : decoderQuery w = entry.query)
    (same : (Airbender.NativeMainDependencies.read w 2).address = address) : entry.data.rd = 12 := by
  have raw : (w 7).val = 12 := by
    rcases Airbender.NativeCallerDecoderProofs.entry_profile fields with ordinary | csr
    · obtain ⟨selected,_,source,equal⟩ := ordinary
      exact unified_rd holds source (query.trans equal.symm) same
    · obtain ⟨selected,_,source,equal⟩ := csr
      exact routed_rd (query.trans equal.symm) (NativeCSRPortProofs.register_addresses holds source (query.trans equal.symm) 2) same
  apply BitVec.eq_of_toNat_eq
  exact (query_rd query).symm.trans raw


theorem zip_members {A B : Type} {left : List A} {right : List B} {a : A} {b : B}
    (member : (a,b) ∈ left.zip right) : a ∈ left ∧ b ∈ right := by
  induction left generalizing right with
  | nil => simp at member
  | cons x xs ih =>
    cases right with
    | nil => simp at member
    | cons y ys =>
      rcases List.mem_cons.mp member with same | tail
      · have first := congrArg Prod.fst same
        have second := congrArg Prod.snd same
        exact ⟨List.mem_cons.mpr (Or.inl first),List.mem_cons.mpr (Or.inl second)⟩
      · have rest := ih tail
        exact ⟨List.mem_cons_of_mem _ rest.1,List.mem_cons_of_mem _ rest.2⟩

theorem main_sources {R : Type} [Field R] {batch : Airbender.NativeMainDecoder.Batch R}
    {before : Reference.RiscV.Sail.State} {publicSetup : SparseDecoderSetup Airbender.NativeCallerDecoder.Mode}
    (sources : Airbender.NativeMainDecoder.PublicSources Airbender.NativeCallerDecoder.decoderFields before publicSetup batch) :
    ∀ row ∈ Airbender.NativeMixedMemoryOrder.mainRows batch.main.proofs,
      ∃ entry ∈ publicSetup.program, entry.SourceWith before Airbender.NativeCallerDecoder.decoderFields ∧ row.decoderQuery = entry.query := by
  let property := fun w : Nat → F => ∃ entry ∈ publicSetup.program,
    entry.SourceWith before Airbender.NativeCallerDecoder.decoderFields ∧ decoderQuery w = entry.query
  have checked : ∀ proof ∈ batch.proofs, ∀ i < callerAuxiliaryLayout.traceLength-1,
      decide (proof.initialization.main.memory.rows i importedConstraintsTraceColumns.execute = 1) = true →
        property (proof.initialization.main.memory.rows i) := by
    intro proof member i bound active
    exact sources proof member i bound (of_decide_eq_true active)
  have sampled := sampled_rows batch.proofs (fun proof i => proof.initialization.main.memory.rows i)
    (callerAuxiliaryLayout.traceLength-1) (fun w => decide (w importedConstraintsTraceColumns.execute = 1)) property checked
  intro row member
  have list : Airbender.NativeMixedMemoryOrder.mainRows batch.main.proofs =
      (((batch.proofs.flatMap fun proof => (List.range (callerAuxiliaryLayout.traceLength-1)).map
        (fun i => proof.initialization.main.memory.rows i)).filter
        (fun w => decide (w importedConstraintsTraceColumns.execute = 1))).map (fun w => (⟨.reduced,w⟩ : MainRow))) := by
    simp only [Airbender.NativeMixedMemoryOrder.mainRows,Airbender.NativeInitializationBatch.mainProofs,
      Airbender.NativeMainDecoderProofs.main_list,Airbender.NativeMainStateHistory.rows,
      Airbender.NativeMainStateHistory.selectAssignments,Airbender.NativeTokenLedger.mainRows,List.map_map,List.flatMap_map,Function.comp_def]
  rw [list] at member
  obtain ⟨w,present,rfl⟩ := List.mem_map.mp member
  exact sampled w present

theorem origin {Setup R : Type} [Field R] {batch : Airbender.NativeMainDecoder.Batch R}
    {workers : WorkerBatch Setup R} {inputs : PublicBoundary} {before : Reference.RiscV.Sail.State}
    {publicSetup : SparseDecoderSetup Airbender.NativeCallerDecoder.Mode} {path : List Token}
    (history : History batch.main.proofs workers inputs path)
    (bodies : ∀ row ∈ Airbender.NativeMixedMemoryOrder.mainRows batch.main.proofs,
      FlatOperation.ConstraintsHoldFlat (Verification.environment row.assignment) (importedConstraints NativeRuntimePool.table))
    (sources : ∀ row ∈ Airbender.NativeMixedMemoryOrder.mainRows batch.main.proofs,
      ∃ entry ∈ publicSetup.program, entry.SourceWith before Airbender.NativeCallerDecoder.decoderFields ∧ row.decoderQuery = entry.query)
    {target : Token} (member : target ∈ path) (nonzero : (limbs target).2 ≠ 0) :
    Airbender.NativeControlOrigin.Origin before publicSetup batch.main.proofs target := by
  obtain ⟨edge,em,main,az,bnz,bound⟩ := main_origin history member nonzero
  obtain ⟨row,rm,present⟩ := main
  have changed : edge.1.value ≠ edge.2.value := by
    intro equal
    have same := congrArg (fun n => (Nat.unpair n).2) equal
    exact bnz (same.symm.trans az)
  have third := third_of_change present changed
  have same : edge.1.address = address := of_decide_eq_true (List.mem_filter.mp (history.ports.mem_iff.mp em)).2
  rw [third] at az bnz bound same
  obtain ⟨entry,entryMember,source,query⟩ := sources row rm
  exact ⟨row,rm,entry,entryMember,source,query,public_rd (bodies row rm) source.fields query same,same,az,bnz,bound⟩

theorem from_prior {Setup R : Type} [Field R] {batch : Airbender.NativeMainDecoder.Batch R}
    {workers : WorkerBatch Setup R} {inputs : PublicBoundary} {before : Reference.RiscV.Sail.State}
    {publicSetup : SparseDecoderSetup Airbender.NativeCallerDecoder.Mode}
    (prior : Airbender.NativeControlHistory.Effects batch workers inputs)
    (bodies : ∀ row ∈ Airbender.NativeMixedMemoryOrder.mainRows batch.main.proofs,
      FlatOperation.ConstraintsHoldFlat (Verification.environment row.assignment) (importedConstraints NativeRuntimePool.table))
    (sources : Airbender.NativeMainDecoder.PublicSources Airbender.NativeCallerDecoder.decoderFields before publicSetup batch) :
    Airbender.NativeControlOrigin.Effects before publicSetup batch workers inputs := by
  have fetched := main_sources sources
  obtain ⟨path,history⟩ := prior.history
  have origins := fun token member nonzero => origin history bodies fetched (target := token) member nonzero
  refine ⟨prior,⟨path,history,origins⟩,?_⟩
  intro w wm active nonzero
  apply origins (read w 42) (zip_members (history.workers w wm active)).1
  simpa only [Airbender.NativeControlHistoryProofs.read_limbs] using nonzero

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
    Airbender.NativeControlOrigin.Effects before publicSetup batch workers inputs := by
  have prior := Airbender.NativeControlHistoryProofs.counted publicSetup embed memory ch pc gamma decoder config accepted image lookups identity
  have sources := Airbender.NativeMainDecoderProofs.public_sources publicSetup embed memory ch pc gamma decoder config accepted image lookups
  have components := Airbender.NativeMemoryHistoryProofs.components embed memory ch pc gamma config accepted.counted.component
  have body := Airbender.NativeMainStateHistoryProofs.selected_body embed memory pc _ components
  apply from_prior prior ?_ sources
  intro row member
  have holds := body row member
  cases row with
  | mk family w => cases family; exact holds

end Airbender.NativeControlOriginProofs
