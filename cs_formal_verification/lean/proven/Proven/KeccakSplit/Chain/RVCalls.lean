module
public import Proven.KeccakSplit.Chain.Calls
public import Proven.KeccakSplit.Memory.RVHistory
public import Proven.KeccakSplit.Reference.RVExecutions
public import Proven.KeccakSplit.ColumnParity.RVExecution
public import Proven.KeccakSplit.ThetaRho.RVExecution
public import Proven.KeccakSplit.Chi5.RVExecution
public import Proven.Trace.SeedAddressClocks
public import Proven.Delegation.CallPaths
public import Proven.KeccakSplit.Chain.Atomic

@[expose] public section

/-! RV twin of `Chain/Atomic.lean` and `Chain/Calls.lean`: a complete initialized split request from an `RV.State`:
    the control path orders the 361 rows, the RV history splits into one atomic group per row, and each row executes
    its call (`Call.RVExecutesAt`) between consecutive group boundaries. RAM cells include the shadow RAM below
    `ROM_END`. -/

namespace Airbender.Keccak.Split.Native.Proofs
open Trace Trace.Proofs Arithmetic
set_option warningAsError true
set_option maxRecDepth 16384

private theorem member_flatMap_sublist (f : α → List β) {items : List α} {item : α}
    (member : item ∈ items) : (f item).Sublist (items.flatMap f) := by
  induction items with
  | nil => cases member
  | cons first rest ih =>
    rcases List.mem_cons.mp member with same | member
    · subst first
      exact List.sublist_append_left _ _
    · exact (ih member).trans (List.sublist_append_right _ _)

private theorem row_events_sublist {data : MemoryData p} {row : Row p} (member : row ∈ data.rows) :
    (row.memorySteps.map transferEvent).Sublist (Transfer.rawEvents (transferData data)) := by
  simp only [Transfer.rawEvents, transferData, MemoryData.steps, List.map_flatMap]
  apply List.Sublist.trans ?_ (List.sublist_append_right _ _)
  exact member_flatMap_sublist (fun r : Row p => r.memorySteps.map transferEvent) member

theorem seed_row_addresses_distinct [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    (control : Split.Proofs.ControlFacts p) {data : MemoryData p} (accepted : MemoryAccepted data)
    (active : ∀ row ∈ data.rows, row.assignment row.columns.execute = 1)
    {cells : List Cell} (inputs : SeedInputs data cells)
    {row : Row p} (member : row ∈ data.rows) :
    (row.memorySteps.map fun edge => edge.1.address).Nodup := by
  have unique := (SeedTransfer.raw_address_clocks_distinct (seed_transfer_facts hp control accepted active inputs)
    inputs.toSeedInputs).sublist ((row_events_sublist member).map (fun event => (event.1, event.2.1)))
  let clock := (decodeTimestamp row.assignment row.columns.invocation).value + 3
  have times : (row.memorySteps.map transferEvent).map (fun event => (event.1, event.2.1)) =
      (row.memorySteps.map fun edge => edge.1.address).map (fun address => (clock, address)) := by
    simp only [Row.memorySteps, List.map_map, Function.comp_def]
    apply List.map_congr_left
    intro port portMember
    have present : port ∈ row.ports := by simpa only [Array.mem_toList_iff] using portMember
    have time := (seed_writes_bounded (by omega) inputs member present).2
    rw [port_offset row present] at time
    simp only [transferEvent, clock, time]
  rw [times] at unique
  exact unique.of_map _

theorem rv_row_atomic_observations [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    (control : Split.Proofs.ControlFacts p) {data : MemoryData p} (accepted : MemoryAccepted data)
    (active : ∀ row ∈ data.rows, row.assignment row.columns.execute = 1)
    {before after : RV.State} {cells : List Cell} (inputs : SeedInputs data cells)
    {row : Row p} (member : row ∈ data.rows) {events : List MemoryAccess}
    (history : RVHistory cells events before after)
    (permutation : events.Perm (row.memorySteps.map transferEvent))
    (aligned : ∀ cell ∈ cells, cell.Aligned) :
    ∀ port ∈ row.ports, ∃ cell ∈ cells, cell.addressCode = port.address.code row.assignment ∧
      cell.readRV before = some (memoryWord (port.readCode row.assignment)) ∧
      cell.readRV after = some (memoryWord (port.writeCode row.assignment)) := by
  have distinct : (events.map fun event => event.2.1).Nodup := by
    apply (permutation.map (fun event => event.2.1)).nodup_iff.mpr
    simpa only [List.map_map, Function.comp_def, transferEvent] using
      seed_row_addresses_distinct hp control accepted active inputs member
  have noZero : ∀ event ∈ events, event.2.1 ≠ (Cell.register 0).addressCode :=
    fun event present => row_no_zero event (permutation.mem_iff.mp present)
  have observations := Delegation.Proofs.rv_atomic_observations history aligned noZero distinct
  intro port portMember
  have present : transferEvent (readToken row.assignment port, row.writeToken port) ∈ events := by
    apply permutation.mem_iff.mpr
    apply List.mem_map.mpr
    refine ⟨(readToken row.assignment port, row.writeToken port), ?_, rfl⟩
    apply List.mem_map.mpr
    exact ⟨port, by simpa only [Array.mem_toList_iff] using portMember, rfl⟩
  exact observations _ present

/-- Each split row executes its documented call on `RV.State`s (the RV `executes` of the row contract). -/
theorem rv_row_executes (row : Row babyBearModulus) (index : Fin 361) {before after : RV.State}
    {cells : List Cell} {events : List MemoryAccess}
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment row.assignment) row.constraints)
    (active : row.assignment row.columns.execute = 1)
    (arguments : Call.RVArgumentsAt index.val before)
    (reads : ∀ port ∈ row.ports, (readToken row.assignment port).word.Bounded)
    (history : RVHistory cells events before after)
    (permutation : events.Perm (row.memorySteps.map transferEvent))
    (observed : ∀ port ∈ row.ports, ∃ cell : Cell, cell.addressCode = port.address.code row.assignment ∧
      cell.readRV before = some (readToken row.assignment port).word.toBitVec) :
    Call.RVExecutesAt index before after := by
  cases row with
  | mk kind w =>
    cases kind
    · exact ColumnParity.Proofs.rv_executes w index holds active arguments reads history permutation observed
    · exact ThetaRho.Proofs.rv_executes w index holds active arguments reads history permutation observed
    · exact Chi5.Proofs.rv_executes w index holds active arguments reads history permutation observed

/-- RV source of a tracked cell: its seed token, read from the starting RV state. -/
theorem rv_cell_source {data : MemoryData p} {before : RV.State} {cells : List Cell}
    (inputs : RVBoundaryInputs data before cells) {cell : Cell} (member : cell ∈ cells) :
    ∃ token ∈ data.initial, token.address = cell.addressCode ∧
      cell.readRV before = some token.word.toBitVec ∧ token.word = Word.ofBitVec token.word.toBitVec := by
  have present := inputs.addresses.mem_iff.mpr (List.mem_map.mpr ⟨cell, member, rfl⟩)
  obtain ⟨token, tokenMember, code⟩ := List.mem_map.mp present
  obtain ⟨other, _, otherCode, read⟩ := inputs.reads token tokenMember
  have same : other = cell := cell_address_injective (otherCode.trans code)
  subst other
  refine ⟨token, tokenMember, code, by simpa only [memoryWord, MemoryToken.word] using read, ?_⟩
  exact (Delegation.Proofs.word_of_toBitVec (inputs.words token tokenMember)).symm

/-- RV twin of `call_chain`: the call chain of a complete request on `RV.State`s, with its pointer, initial lane
    reads and final memory agreement. -/
theorem rv_call_chain (contract : RowFacts) (control : Split.Proofs.ControlFacts babyBearModulus)
    {data : MemoryData babyBearModulus} {initial : RV.State} {cells : List Cell}
    (accepted : MemoryAccepted data) (inputs : RVCallInputs data initial cells)
    (aligned : ∀ cell ∈ cells, cell.Aligned) :
    ∃ (states : Fin 362 → RV.State) (pointer : BitVec 32),
      states 0 = initial ∧
      (∀ index : Fin 361, Call.RVExecutesAt index (states index.castSucc) (states index.succ)) ∧
      (Cell.register 11).readRV (states 0) = some pointer ∧
      (∀ (slot : Fin 30) (high : Bool), ∃ value : BitVec 32,
        (Call.laneCell pointer ⟨slot.val, by omega⟩ high).readRV (states 0) = some value) ∧
      RVTraceMapping data initial (states 361) cells := by
  have hp := babyBear_clock
  have active := inputs.active
  have boundary := inputs.memory.toRVBoundaryInputs
  have seed := boundary.toSeed
  have facts := seed_transfer_facts hp control accepted active seed
  have reads := fun {row} (member : row ∈ data.rows) =>
    seed_row_reads_bounded contract control accepted active seed member
  -- the x10 seed holds 0
  obtain ⟨source, sourceMember, sourceCode, sourceRead, sourceWord⟩ := rv_cell_source boundary inputs.controlCell
  have zero := Option.some.inj (sourceRead.symm.trans inputs.controlStart)
  rw [zero] at sourceWord
  change source.word = ⟨0, 0⟩ at sourceWord
  -- the control path orders the rows
  obtain ⟨path, head, increasing, matching⟩ : ∃ path : List (MemoryToken babyBearModulus),
      path.head? = some source ∧
      (path.map fun token => (timeOfPair token.time).value).Pairwise (· < ·) ∧
      (path.zip path.tail).Perm (data.rows.map controlEdge) := by
    have unique : (data.initial.map MemoryToken.address).Nodup :=
      seed.addresses.nodup_iff.mpr seed.distinct
    obtain ⟨_, _, _, path, head, _, _, permutation⟩ :=
      Trace.Proofs.keyed_paths_finite MemoryToken.address (fun token => (timeOfPair token.time).value)
        facts.matching facts.addresses unique facts.order source sourceMember
    refine ⟨path, head, ?_, ?_⟩
    · apply Trace.Proofs.rank_ordered (fun token => (timeOfPair token.time).value) path
      intro edge edgeMember
      exact facts.order edge (List.mem_of_mem_filter (permutation.mem_iff.mp edgeMember))
    · rw [sourceCode] at permutation
      have edges := @control_edges babyBearModulus data
      change (path.zip path.tail).Perm (data.steps.filter fun edge => edge.1.address = _) at permutation
      rw [edges] at permutation
      exact permutation
  have pathLength : path.length = 362 := by
    have count := matching.length_eq
    have positive : 0 < path.length := by
      cases path with
      | nil => simp at head
      | cons _ _ => simp
    simp only [List.length_zip, List.length_tail, List.length_map, inputs.calls] at count
    omega
  have steps : ∀ edge ∈ path.zip path.tail, edge.2.word = advance edge.1.word := by
    intro edge member
    obtain ⟨row, rowMember, rfl⟩ := List.mem_map.mp (matching.mem_iff.mp member)
    obtain ⟨index, _, readControl, writeControl, _⟩ :=
      contract.effects row (accepted.constraints row rowMember) (active row rowMember) (reads rowMember)
    rw [← (control_words row).1, ← (control_words row).2, readControl, writeControl]
    rfl
  have words := Delegation.Proofs.path_word_sequence head advance steps
  obtain ⟨ordered, perm, edges, clocks⟩ :=
    Delegation.Proofs.ordered_rows_from_path controlEdge matching increasing
  have count : ordered.length = 361 := perm.length_eq.trans inputs.calls
  have orderedMember : ∀ (i : Nat) (bound : i < ordered.length), ordered[i] ∈ data.rows :=
    fun i bound => perm.mem_iff.mp (List.getElem_mem bound)
  have orderedControl : ∀ (i : Nat) (bound : i < 361),
      (ordered[i]'(by omega)).readWord 0 = ⟨controlAt i, 0⟩ := by
    intro i bound
    have edge : controlEdge (ordered[i]'(by omega)) = (path[i]'(by omega), path[i + 1]'(by omega)) := by
      have e := List.getElem_of_eq edges (i := i) (by simp [pathLength]; omega)
      simp only [List.getElem_zip, List.getElem_tail, List.getElem_map] at e
      exact e.symm
    rw [(control_words _).1, edge]
    change (path[i]'(by omega)).word = _
    rw [words i (by omega), sourceWord, advance_iterate i bound]
  -- one atomic RV group per row, in clock order
  obtain ⟨_, events, after, bound, permutation, order, actual, final⟩ :=
    rv_native_history hp control accepted active boundary aligned
  have grouped : Delegation.Proofs.GroupedRVHistory cells
      (fun row : Row babyBearModulus => row.memorySteps.map transferEvent) ordered.reverse initial after := by
    apply Delegation.Proofs.rv_grouped_history (fun row => (timeOfPair (controlEdge row).2.time).value + 1)
      _ _ order _ _ actual
    · apply List.pairwise_reverse.mpr
      exact clocks.imp (by intro a b less; omega)
    · have rows := List.Perm.flatMap_right (fun row : Row babyBearModulus => row.memorySteps.map transferEvent)
        ((List.reverse_perm ordered).trans perm)
      have pooled : data.rows.flatMap (fun row => row.memorySteps.map transferEvent) =
          data.steps.map transferEvent := by
        simp only [MemoryData.steps, List.map_flatMap]
      exact permutation.trans (pooled ▸ rows).symm
    · intro row _ event present
      obtain ⟨edge, included, rfl⟩ := List.mem_map.mp present
      obtain ⟨port, member, rfl⟩ := List.mem_map.mp included
      exact port_time row (by simpa using member)
  obtain ⟨list, listCount, listHead, listLast, groupSteps⟩ := Delegation.Proofs.rv_grouped_boundaries grouped
  have listLength : list.length = 362 := by simpa [count] using listCount
  let states : Fin 362 → RV.State := fun k => list[361 - k.val]'(by omega)
  have stateZero : states 0 = initial := by
    have endpoint := List.getLast_of_getLast?_eq_some listLast
    simpa [states, List.getLast_eq_getElem, listLength] using endpoint
  have stateLast : states 361 = after := by
    have first : list[0]? = some after := by simpa only [List.head?_eq_getElem?] using listHead
    simpa [states, List.getElem?_eq_getElem, listLength] using first
  have rowHistory : ∀ (i : Nat) (iBound : i < 361), ∃ events : List MemoryAccess,
      events.Perm ((ordered[i]'(by omega)).memorySteps.map transferEvent) ∧
      RVHistory cells events (states ⟨i, by omega⟩) (states ⟨i + 1, by omega⟩) := by
    intro i iBound
    obtain ⟨events, eventsPerm, history⟩ := groupSteps (360 - i) (by simp [count]; omega)
    have reversed : ordered.reverse[360 - i]'(by simp [count]; omega) = ordered[i]'(by omega) := by
      rw [List.getElem_reverse]
      congr 1
      omega
    refine ⟨events, reversed ▸ eventsPerm, ?_⟩
    have left : 360 - i + 1 = 361 - i := by omega
    have right : 360 - i = 361 - (i + 1) := by omega
    have first : states ⟨i, by omega⟩ = list[360 - i + 1]'(by omega) := get_index_eq left.symm
    have second : states ⟨i + 1, by omega⟩ = list[360 - i]'(by omega) := get_index_eq right.symm
    rw [first, second]
    exact history
  -- each row executes its call
  have observations : ∀ (i : Nat) (iBound : i < 361), ∀ port ∈ (ordered[i]'(by omega)).ports,
      ∃ cell ∈ cells, cell.addressCode = port.address.code (ordered[i]'(by omega)).assignment ∧
        cell.readRV (states ⟨i, by omega⟩) = some (readToken (ordered[i]'(by omega)).assignment port).word.toBitVec := by
    intro i iBound port present
    obtain ⟨events, eventsPerm, history⟩ := rowHistory i iBound
    obtain ⟨cell, member, code, before, _⟩ :=
      rv_row_atomic_observations hp control accepted active seed (orderedMember i (by omega))
        history eventsPerm aligned port present
    exact ⟨cell, member, code, before⟩
  have rowRegister : ∀ (i : Nat) (iBound : i < 361) (index register : Nat) (small : register < 32),
      (∃ indexBound : index < (ordered[i]'(by omega)).ports.size,
        ((ordered[i]'(by omega)).ports[index]).address = .constantRegister register) →
      (Cell.register register).readRV (states ⟨i, by omega⟩) =
        some ((ordered[i]'(by omega)).readWord index).toBitVec := by
    intro i iBound index register small ⟨indexBound, address⟩
    obtain ⟨cell, _, code, read⟩ := observations i iBound _ (Array.getElem_mem indexBound)
    have same : cell = .register register := by
      apply cell_address_injective
      rw [code, address]
      simp [MemoryAddress.code, Cell.addressCode, Nat.mod_eq_of_lt small]
    rw [same] at read
    rw [readWord_eq _ indexBound]
    exact read
  have executes : ∀ index : Fin 361, Call.RVExecutesAt index (states index.castSucc) (states index.succ) := by
    intro index
    have member := orderedMember index.val (by omega)
    have arguments : Call.RVArgumentsAt index.val (states ⟨index.val, by omega⟩) := by
      refine ⟨_, _, rowRegister index.val index.isLt 0 10 (by decide) (register_ports _).1,
        rowRegister index.val index.isLt 1 11 (by decide) (register_ports _).2, ?_, ?_⟩
      · rw [orderedControl index.val index.isLt]
        simp [Word.toBitVec, Word.value]
      · have align := contract.aligned _ (accepted.constraints _ member)
        simp only [Word.toBitVec, BitVec.toNat_ofNat]
        omega
    obtain ⟨events, eventsPerm, history⟩ := rowHistory index.val index.isLt
    exact rv_row_executes _ index (accepted.constraints _ member) (active _ member) arguments
      (reads member) history eventsPerm (fun port present => by
        obtain ⟨cell, _, code, read⟩ := observations index.val index.isLt port present
        exact ⟨cell, code, read⟩)
  -- one pointer for the whole request
  let pointer := ((ordered[0]'(by omega)).readWord 1).toBitVec
  have pointerReads : ∀ (k : Nat) (kBound : k < 362),
      (Cell.register 11).readRV (states ⟨k, kBound⟩) = some pointer := by
    intro k
    induction k with
    | zero => intro _; exact rowRegister 0 (by omega) 1 11 (by decide) (register_ports _).2
    | succ k ih =>
      intro kBound
      exact (Call.Proofs.rv_executes_pointer (executes ⟨k, by omega⟩) (ih (by omega))).2
  have rowPointer : ∀ (k : Nat) (kBound : k < 361),
      ((ordered[k]'(by omega)).readWord 1).toBitVec = pointer := by
    intro k kBound
    exact Option.some.inj ((rowRegister k kBound 1 11 (by decide) (register_ports _).2).symm.trans
      (pointerReads k (by omega)))
  -- every lane word is a tracked cell, so it reads in the initial state
  have laneReads : ∀ (slot : Fin 30) (high : Bool), ∃ value : BitVec 32,
      (Call.laneCell pointer ⟨slot.val, by omega⟩ high).readRV (states 0) = some value := by
    intro slot high
    obtain ⟨index, lane, live, slotEq⟩ := slot_coverage slot
    have member := orderedMember index.val (by omega)
    have pointerBound : ((ordered[index.val]'(by omega)).readWord 1).Bounded := by
      obtain ⟨_, ⟨indexBound, _⟩⟩ := register_ports (ordered[index.val]'(by omega))
      rw [readWord_eq _ indexBound]
      exact reads member _ (Array.getElem_mem indexBound)
    obtain ⟨port, present, code⟩ := contract.addresses _ index (accepted.constraints _ member)
      (active _ member) (orderedControl index.val index.isLt) pointerBound lane live high
    have edgeMember : (readToken (ordered[index.val]'(by omega)).assignment port,
        (ordered[index.val]'(by omega)).writeToken port) ∈ data.steps :=
      List.mem_flatMap.mpr ⟨_, member, List.mem_map.mpr ⟨port, by simpa using present, rfl⟩⟩
    have origin := Trace.Proofs.keyed_origins MemoryToken.address
      (fun token => (timeOfPair token.time).value) facts.matching facts.addresses facts.order _ edgeMember
    have tracked := seed.addresses.mem_iff.mp origin
    obtain ⟨cell, cellMember, same⟩ := List.mem_map.mp tracked
    have equal : cell = Call.laneCell pointer ⟨slot.val, by omega⟩ high := by
      apply cell_address_injective
      rw [same]
      change port.address.code _ = _
      rw [code, rowPointer index.val index.isLt]
      congr 2
      exact Fin.ext slotEq
    rw [equal] at cellMember
    obtain ⟨token, _, _, read, _⟩ := rv_cell_source boundary cellMember
    exact ⟨_, by rw [stateZero]; exact read⟩
  refine ⟨states, pointer, stateZero, executes, pointerReads 0 (by omega), laneReads, ?_⟩
  rw [stateLast]
  refine ⟨⟨events, permutation, actual⟩, ?_⟩
  intro token member
  obtain ⟨cell, cellMember, code, read⟩ :=
    Transfer.rv_terminal_reads_at_boundary facts boundary.transfer bound final token member
  exact ⟨cell, cellMember, code, by simpa only [memoryWord, MemoryToken.word] using read⟩

end Airbender.Keccak.Split.Native.Proofs
