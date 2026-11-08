import Airbender.Review.Trace.Families.ReducedMachine.MixedWordBounds
import Airbender.Proofs.ReducedMachine.NativeDecodedMain
import Airbender.Proofs.ReducedMachine.NativeMainDependencies

namespace Airbender.NativeMixedWordBoundsProofs
open Airbender.ReducedMachine.Native Airbender.Trace Airbender.Verification
open Airbender.Blake2Worker.Native Airbender.ReducedMachine.NativeMemoryBoundary
open Airbender.NativeMainDependencies (port read write)
private abbrev F := ZMod mersenne31Modulus
private abbrev Token := Airbender.NativeMixedMemoryOrder.Token
private abbrev MainRow := Airbender.NativeMixedMemoryOrder.MainRow
set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false

/-- Generic rank closure before native data/domain instantiation. -/
theorem rank_closed {A : Type} (initial : List A) (edges : List (A × A))
    (rank : A → Nat) (property : A → Prop)
    (seeded : ∀ token ∈ initial, property token)
    (stepLaw : ∀ edge ∈ edges,
      (∀ earlier ∈ initial ++ edges.map Prod.snd, rank earlier < rank edge.2 → property earlier) → property edge.2) :
    ∀ token ∈ initial ++ edges.map Prod.snd, property token := by
  have induction : ∀ n, ∀ token ∈ initial ++ edges.map Prod.snd, rank token = n → property token := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro token member same
      rcases List.mem_append.mp member with seed | written
      · exact seeded token seed
      · obtain ⟨edge,present,rfl⟩ := List.mem_map.mp written
        apply stepLaw edge present
        intro earlier member smaller
        exact ih (rank earlier) (by omega) earlier member rfl
  intro token member
  exact induction (rank token) token member rfl

private theorem encoded_bound (key : MemoryKey) :
    (Airbender.NativeMemoryTokens.encodeKey key).word.Bounded ↔
      Airbender.NativeWorkerWriteSlices.WordBound key.value := by
  simp only [MemoryToken.word,Airbender.NativeMemoryTokens.encodeKey,Nat.unpair_pair,Arithmetic.Word.Bounded]
  change (key.value[0].val < 65536 ∧ key.value[1].val < 65536) ↔ ∀ i : Fin 2, key.value[i].val < 65536
  constructor
  · intro bounds i
    fin_cases i
    · exact bounds.1
    · exact bounds.2
  · intro bounds
    exact ⟨bounds 0,bounds 1⟩

private theorem port_member (row : MainRow) (slot : Fin 3) : port slot ∈ row.ports := by
  cases row with
  | mk family w =>
    cases family
    change port slot ∈ importedConstraintsMemoryPorts
    fin_cases slot <;> simp [port,importedConstraintsMemoryPorts]

private theorem port_slot (row : MainRow) (actual : MemoryPort) (member : actual ∈ row.ports) :
    ∃ slot : Fin 3, actual = port slot := by
  cases row with
  | mk family w =>
    cases family
    change actual ∈ importedConstraintsMemoryPorts at member
    simp [importedConstraintsMemoryPorts] at member
    rcases member with rfl | rfl | rfl
    · exact ⟨0,rfl⟩
    · exact ⟨1,rfl⟩
    · exact ⟨2,rfl⟩

private theorem offset (slot : Fin 3) : (port slot).clock.offset = slot.val := by
  fin_cases slot <;> rfl

private theorem actual_write (row : MainRow) (slot : Fin 3) :
    writeToken row.columns row.assignment (port slot) = write row.assignment slot := by
  cases row with
  | mk family w => cases family; rfl

private theorem event_order (row : MainRow) (source target : Fin 3)
    (order : ((port source).event row.columns row.assignment).1 ≤ ((port target).event row.columns row.assignment).1) :
    source.val ≤ target.val := by
  simp only [MemoryPort.event,offset] at order
  omega

/-- Entire finite sampling/filter/mapping proof before actual native domains. -/
private theorem sampled_rows {A B : Type} (objects : List A) (samples : A → Nat → B)
    (count : Nat) (active : B → Bool) (property : B → Prop)
    (checked : ∀ object ∈ objects, ∀ i < count, active (samples object i) = true → property (samples object i)) :
    ∀ sample ∈ (objects.flatMap fun object => (List.range count).map (samples object)).filter active, property sample := by
  intro sample member
  have selected := List.mem_filter.mp member
  obtain ⟨object,present,sampled⟩ := List.mem_flatMap.mp selected.1
  obtain ⟨i,bound,rfl⟩ := List.mem_map.mp sampled
  exact checked object present i (List.mem_range.mp bound) selected.2

/-- Couple the SAME counted actual rows to their derived local rules. -/
theorem main_rules {R : Type} [Field R] {batch : Airbender.NativeMainDecoder.Batch R}
    (rules : Airbender.NativeDecodedMain.Effects batch) :
    ∀ row ∈ Airbender.NativeMixedMemoryOrder.mainRows batch.main.proofs, Airbender.NativeDecodedMain.RowWriteRule row := by
  have checked : ∀ proof ∈ batch.proofs, ∀ i < callerAuxiliaryLayout.traceLength-1,
      decide (proof.initialization.main.memory.rows i importedConstraintsTraceColumns.execute = 1) = true →
        Airbender.NativeDecodedMain.RowWriteRule
          (⟨.reduced,proof.initialization.main.memory.rows i⟩ : MainRow) := by
    intro proof member i bound active
    exact rules proof member i bound (of_decide_eq_true active)
  have sampled := sampled_rows batch.proofs (fun proof i => proof.initialization.main.memory.rows i)
    (callerAuxiliaryLayout.traceLength-1) (fun w => decide (w importedConstraintsTraceColumns.execute = 1))
    (fun w => Airbender.NativeDecodedMain.RowWriteRule (⟨.reduced,w⟩ : MainRow)) checked
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

private theorem seed_bounds {R : Type} [Field R] {proofs : List (Airbender.NativeInitializationBatch.Proof R)}
    (seeds : Airbender.NativeInitializationSeedBoundary.Effects proofs) :
    ∀ token ∈ Airbender.NativeInitializationSeedBoundary.initialTokens proofs, token.word.Bounded := by
  intro token member
  rw [seeds.encoding] at member
  obtain ⟨cell,_,rfl⟩ := List.mem_map.mp member
  simp [Cell.initialToken,MemoryToken.word,Arithmetic.Word.Bounded,Arithmetic.limbBase,Arithmetic.Word.ofBitVec]

private theorem main_bound {Setup R : Type} [Field R]
    {proofs : List (Airbender.NativeInitializationBatch.Proof R)} {workers : WorkerBatch Setup R} {inputs : PublicBoundary}
    (prior : Airbender.NativeMainDependencies.Effects proofs workers inputs)
    (rules : ∀ row ∈ Airbender.NativeMixedMemoryOrder.mainRows proofs, Airbender.NativeDecodedMain.RowWriteRule row)
    {row : MainRow} (member : row ∈ Airbender.NativeMixedMemoryOrder.mainRows proofs)
    (actual : MemoryPort) (portPresent : actual ∈ row.ports)
    (earlier : ∀ token ∈ Airbender.NativeLatestReads.available proofs workers,
      Airbender.NativeCompleteMemoryPaths.rank token < Airbender.NativeCompleteMemoryPaths.rank (writeToken row.columns row.assignment actual) → token.word.Bounded) :
    (writeToken row.columns row.assignment actual).word.Bounded := by
  obtain ⟨target,rfl⟩ := port_slot row actual portPresent
  apply rules row member (port target) (port_member row target)
  intro source sourcePresent order
  obtain ⟨slot,rfl⟩ := port_slot row source sourcePresent
  apply earlier _ (prior.sources row member slot)
  rw [actual_write]
  exact prior.before row member slot target (event_order row slot target order)

private theorem worker_bound {Setup R : Type} [Field R]
    {proofs : List (Airbender.NativeInitializationBatch.Proof R)} {workers : WorkerBatch Setup R} {inputs : PublicBoundary}
    (prior : Airbender.NativeMainDependencies.Effects proofs workers inputs)
    {w : Nat → F} (member : w ∈ Airbender.NativeTokenLedger.workerRows workers)
    (active : w constraintsABI.multiplicity = 1) (slot : Fin 43)
    (earlier : ∀ token ∈ Airbender.NativeLatestReads.available proofs workers,
      Airbender.NativeCompleteMemoryPaths.rank token < Airbender.NativeCompleteMemoryPaths.rank
        (Airbender.NativeMemoryTokens.encodeKey (quotientMemoryKey w slot true)) → token.word.Bounded) :
    (Airbender.NativeMemoryTokens.encodeKey (quotientMemoryKey w slot true)).word.Bounded := by
  have edge : Airbender.NativeMixedMemoryOrder.Step proofs workers
      (Airbender.NativeWorkerClockProgress.readToken w slot)
      (Airbender.NativeMemoryTokens.encodeKey (quotientMemoryKey w slot true)) :=
    Or.inr ⟨w,member,active,slot,rfl,rfl⟩
  rcases (prior.workers.workers w member).ports slot with bounded | copy
  · exact (encoded_bound _).mpr bounded
  · have latest := prior.workers.prior.latest.reads _ _ edge
    have old := earlier _ latest.source latest.before
    have value : (Airbender.NativeMemoryTokens.encodeKey (quotientMemoryKey w slot true)).value =
        (Airbender.NativeWorkerClockProgress.readToken w slot).value := by
      change Nat.pair (keyValue w slot true)[0].val (keyValue w slot true)[1].val =
        Nat.pair (keyValue w slot false)[0].val (keyValue w slot false)[1].val
      rw [copy]
    simpa only [MemoryToken.word,value] using old

/-- Mixed initialized closure uses only already-derived sources and local rules. -/
theorem available_bounds {Setup R : Type} [Field R]
    {proofs : List (Airbender.NativeInitializationBatch.Proof R)} {workers : WorkerBatch Setup R} {inputs : PublicBoundary}
    (prior : Airbender.NativeMainDependencies.Effects proofs workers inputs)
    (seeds : Airbender.NativeInitializationSeedBoundary.Effects proofs)
    (rules : ∀ row ∈ Airbender.NativeMixedMemoryOrder.mainRows proofs, Airbender.NativeDecodedMain.RowWriteRule row) :
    ∀ token ∈ Airbender.NativeLatestReads.available proofs workers, token.word.Bounded := by
  apply rank_closed (Airbender.NativeInitializationSeedBoundary.initialTokens proofs)
    (Airbender.NativeMemoryRoots.steps proofs workers) Airbender.NativeCompleteMemoryPaths.rank
    (fun token => token.word.Bounded) (seed_bounds seeds)
  intro edge present earlier
  rcases edge with ⟨readToken,writeToken⟩
  have actual := (Airbender.NativeMemoryRootsProofs.step_iff proofs workers readToken writeToken).mp present
  rcases actual with ⟨row,member,port,portPresent,readSame,writeSame⟩ | ⟨w,member,active,slot,readSame,writeSame⟩
  · subst writeToken
    exact main_bound prior rules member port portPresent earlier
  · subst writeToken
    exact worker_bound prior member active slot earlier

private theorem active_write_member {Setup R : Type} [Field R]
    {proofs : List (Airbender.NativeInitializationBatch.Proof R)} {workers : WorkerBatch Setup R}
    {read write : Token} (edge : Airbender.NativeMixedMemoryOrder.Step proofs workers read write) :
    write ∈ Airbender.NativeLatestReads.available proofs workers :=
  List.mem_append_right _ (List.mem_map.mpr ⟨(read,write),
    (Airbender.NativeMemoryRootsProofs.step_iff proofs workers read write).mpr edge,rfl⟩)

theorem step_bounds {Setup R : Type} [Field R]
    {proofs : List (Airbender.NativeInitializationBatch.Proof R)} {workers : WorkerBatch Setup R} {inputs : PublicBoundary}
    (prior : Airbender.NativeMainDependencies.Effects proofs workers inputs)
    (words : ∀ token ∈ Airbender.NativeLatestReads.available proofs workers, token.word.Bounded) :
    ∀ read write, Airbender.NativeMixedMemoryOrder.Step proofs workers read write →
      read.word.Bounded ∧ write.word.Bounded := by
  intro read write edge
  exact ⟨words _ (prior.workers.prior.latest.reads _ _ edge).source,words _ (active_write_member edge)⟩

/-- Inactive rows use their unchanged processing masks; none are dropped. -/
theorem worker_bounds {Setup R : Type} [Field R]
    {proofs : List (Airbender.NativeInitializationBatch.Proof R)} {workers : WorkerBatch Setup R} {inputs : PublicBoundary}
    (prior : Airbender.NativeMainDependencies.Effects proofs workers inputs)
    (processing : ∀ w ∈ Airbender.NativeTokenLedger.workerRows workers, LocalProcessingAccepted w)
    (words : ∀ token ∈ Airbender.NativeLatestReads.available proofs workers, token.word.Bounded) :
    ∀ w ∈ Airbender.NativeTokenLedger.workerRows workers, ∀ slot : Fin 43, ∀ flag : Bool,
      (Airbender.NativeMemoryTokens.encodeKey (quotientMemoryKey w slot flag)).word.Bounded := by
  intro w member slot flag
  have effects := Airbender.Blake2Worker.ProcessingProofs.effects (processing w member).conventions
  rcases effects.multiplicityBit with zero | active
  · apply (encoded_bound _).mpr
    change Airbender.NativeWorkerWriteSlices.WordBound (keyValue w slot flag)
    rw [Airbender.Blake2Worker.MemoryKeyProofs.padding_value effects zero slot flag]
    intro limb
    fin_cases limb <;> decide +kernel
  · have edge : Airbender.NativeMixedMemoryOrder.Step proofs workers
        (Airbender.NativeWorkerClockProgress.readToken w slot)
        (Airbender.NativeMemoryTokens.encodeKey (quotientMemoryKey w slot true)) :=
      Or.inr ⟨w,member,active,slot,rfl,rfl⟩
    cases flag
    · exact (step_bounds prior words _ _ edge).1
    · exact (step_bounds prior words _ _ edge).2

theorem terminal_bounds {Setup R : Type} [Field R]
    {proofs : List (Airbender.NativeInitializationBatch.Proof R)} {workers : WorkerBatch Setup R} {inputs : PublicBoundary}
    (prior : Airbender.NativeMainDependencies.Effects proofs workers inputs)
    (words : ∀ token ∈ Airbender.NativeLatestReads.available proofs workers, token.word.Bounded) :
    ∀ token ∈ Airbender.NativeInitializationSeedBoundary.terminalTokens proofs inputs, token.word.Bounded := by
  have matching := prior.workers.prior.latest.unique.paths.keys.addresses.roots.matching
  intro token member
  apply words
  exact matching.mem_iff.mpr (List.mem_append_left _ member)

/-- SAME complete counted source, original public image and old logical
    boundaries derive initialized bounds. No read/result/range law is supplied. -/
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
    Airbender.NativeMixedWordBounds.Effects batch workers inputs := by
  have prior := Airbender.NativeMainDependencyProofs.effects embed memory ch pc gamma config accepted.counted.component identity
  have seeds := Airbender.NativeInitializationSeedBoundaryProofs.boundary embed memory ch pc gamma config accepted.counted.component
  have rules := Airbender.NativeDecodedQueryDomainProofs.counted publicSetup embed memory ch pc gamma decoder config accepted image lookups
  have words := available_bounds prior seeds (main_rules rules)
  have processing := Airbender.NativeActiveWorkerClockProofs.worker_processing embed memory ch pc gamma config accepted.counted.component
  exact ⟨prior,Airbender.NativeMainBatchProofs.effects batch.main accepted.counted.counter,words,
    step_bounds prior words,worker_bounds prior processing words,terminal_bounds prior words⟩

end Airbender.NativeMixedWordBoundsProofs
