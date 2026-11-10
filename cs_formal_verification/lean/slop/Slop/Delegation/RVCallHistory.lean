module
public import Slop.Delegation.RVBoundaryInputs
public import Slop.Delegation.CallGroups
public import Slop.Delegation.PortEvents
public import Slop.Delegation.Readonly
public import Slop.Trace.RVHistoryFrame
public import Human.Helpers.Delegation.RVBoundaryMemory
public import Human.Trace.Delegation.RVExecution
public import Slop.Delegation.History

@[expose] public section

/-! RV twins of the delegation call-history chain (`CallHistory.lean`, `CallBoundaries.lean`, `AtomicHistory.lean`,
    `Atomic.lean`, `CopyFrame.lean`, `Readonly.lean`, `BoundaryInputs.lean`): grouping the realized RV history by
    worker call, per-call RV states, per-port observations, and the state-free seed facts they use. RAM cells are RAM
    at any address, the shadow RAM below `ROM_END` included. Proof bodies follow the Sail ones. -/

namespace Airbender.Delegation.Proofs
open Trace Trace.Proofs Arithmetic
set_option warningAsError true

/-! ### State-free seed facts -/

theorem seed_initialized_cell [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    {data : MemoryData p} (accepted : MemoryAccepted data)
    {cells : List Cell} (inputs : SeedProofs.SeedInputs data cells)
    {edge : MemoryToken p × MemoryToken p} (member : edge ∈ data.steps) :
    ∃ cell ∈ cells, cell.addressCode = edge.1.address :=
  SeedTransfer.initialized_cell (SeedProofs.transfer_facts hp accepted inputs) inputs.toSeedInputs member

theorem seed_port_initialized_cell [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    {data : MemoryData p} {cells : List Cell}
    (accepted : MemoryAccepted data) (inputs : SeedProofs.SeedInputs data cells)
    {row : Row p} (member : row ∈ data.rows) {port : MemoryPort} (present : port ∈ row.ports)
    {cell : Cell} (address : (readToken row.assignment port).address = cell.addressCode) :
    cell ∈ cells := by
  have step : (readToken row.assignment port, row.writeToken port) ∈ data.steps :=
    List.mem_flatMap.mpr ⟨row, member, List.mem_map.mpr ⟨port, by simpa using present, rfl⟩⟩
  obtain ⟨actual, tracked, same⟩ := seed_initialized_cell hp accepted inputs step
  rw [address] at same
  have equal : actual = cell := Trace.Proofs.cell_address_injective same
  exact equal ▸ tracked

/-- The seed token of a tracked cell. -/
theorem seed_cell_source {data : MemoryData p} {cells : List Cell}
    (inputs : SeedProofs.SeedInputs data cells) {cell : Cell} (member : cell ∈ cells) :
    ∃ token ∈ data.initial, token.address = cell.addressCode := by
  obtain ⟨token, present, code⟩ := List.mem_map.mp
    (inputs.addresses.mem_iff.mpr (List.mem_map.mpr ⟨cell, member, rfl⟩))
  exact ⟨token, present, code⟩

/-- State-free `readonly_cell`: a cell whose every native port copies its read value keeps its seed word. -/
theorem seed_readonly_cell [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    {data : MemoryData p} {cells : List Cell} {source : MemoryToken p}
    (accepted : MemoryAccepted data) (inputs : SeedProofs.SeedInputs data cells)
    (member : source ∈ data.initial)
    (copies : ∀ edge ∈ data.steps, edge.1.address = source.address → edge.1.word = edge.2.word) :
    (∀ edge ∈ data.steps, edge.1.address = source.address → edge.1.word = source.word) ∧
    ∃ sink ∈ data.terminal, sink.address = source.address ∧ sink.word = source.word := by
  obtain ⟨sink, sinkMember, address, path, head, last, _, matching⟩ :=
    (SeedProofs.memory_effects hp accepted inputs).paths _ member
  have constant := path_word_constant head (fun edge edgeMember => by
    have included := matching.mem_iff.mp edgeMember
    have pair := List.mem_filter.mp included
    exact copies edge pair.1 (by simpa using pair.2))
  constructor
  · intro edge edgeMember atCell
    have included : edge ∈ path.zip path.tail := matching.mem_iff.mpr
      (List.mem_filter.mpr ⟨edgeMember, by simpa using atCell⟩)
    exact constant _ (List.of_mem_zip included).1
  · exact ⟨sink, sinkMember, address, constant _ (List.mem_of_getLast? last)⟩

/-- A port present in every (nonempty) row that reads one cell, whose every native port copies its read value: the
    cell's seed token fixes the word every row reads there and the cell's terminal token. -/
theorem seed_port_history [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    {data : MemoryData p} {cells : List Cell}
    (accepted : MemoryAccepted data) (inputs : SeedProofs.SeedInputs data cells) (nonempty : data.rows ≠ [])
    {port : MemoryPort} {cell : Cell} (present : ∀ row ∈ data.rows, port ∈ row.ports)
    (address : ∀ row ∈ data.rows, (readToken row.assignment port).address = cell.addressCode)
    (copies : ∀ edge ∈ data.steps, edge.1.address = cell.addressCode → edge.1.word = edge.2.word) :
    ∃ source ∈ data.initial, source.address = cell.addressCode ∧
      (∀ row ∈ data.rows, (readToken row.assignment port).word = source.word) ∧
      ∃ sink ∈ data.terminal, sink.address = cell.addressCode ∧ sink.word = source.word := by
  obtain ⟨first, firstMember⟩ := List.exists_mem_of_ne_nil _ nonempty
  have tracked := seed_port_initialized_cell hp accepted inputs firstMember (present first firstMember)
    (address first firstMember)
  obtain ⟨source, sourceMember, sourceCode⟩ := seed_cell_source inputs tracked
  have constant := seed_readonly_cell hp accepted inputs sourceMember
    (fun edge member same => copies edge member (same.trans sourceCode))
  refine ⟨source, sourceMember, sourceCode, fun row member => ?_, ?_⟩
  · have included : (readToken row.assignment port, row.writeToken port) ∈ data.steps :=
      List.mem_flatMap.mpr ⟨row, member, List.mem_map.mpr ⟨port, by simpa using present row member, rfl⟩⟩
    exact constant.1 _ included ((address row member).trans sourceCode.symm)
  · obtain ⟨sink, sinkMember, sinkAddress, sinkWord⟩ := constant.2
    exact ⟨sink, sinkMember, sinkAddress.trans sourceCode, sinkWord⟩

private theorem address_clocks_distinct (events : List MemoryAccess)
    (perAddress : ∀ address, ((events.filter fun event => decide (event.2.1 = address)).map Prod.fst).Nodup) :
    (events.map fun event => (event.1, event.2.1)).Nodup := by
  induction events with
  | nil => simp
  | cons first rest ih =>
    have tailLocal : ∀ address,
        ((rest.filter fun event => decide (event.2.1 = address)).map Prod.fst).Nodup := by
      intro address
      have whole := perAddress address
      by_cases same : first.2.1 = address
      · simp only [List.filter_cons, same, decide_true, ite_true, List.map_cons, List.nodup_cons] at whole
        exact whole.2
      · simpa only [List.filter_cons, same, decide_false, Bool.false_eq_true, ite_false] using whole
    refine List.nodup_cons.mpr ⟨?_, ih tailLocal⟩
    intro present
    obtain ⟨other, otherMember, equal⟩ := List.mem_map.mp present
    have here := perAddress first.2.1
    simp only [List.filter_cons, decide_true, ite_true, List.map_cons, List.nodup_cons] at here
    apply here.1
    apply List.mem_map.mpr
    refine ⟨other, List.mem_filter.mpr ⟨otherMember, ?_⟩, ?_⟩
    · simpa using (Prod.ext_iff.mp equal).2
    · exact (Prod.ext_iff.mp equal).1

theorem seed_raw_address_clocks_distinct [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    {data : MemoryData p} (accepted : MemoryAccepted data)
    {cells : List Cell} (inputs : SeedProofs.SeedInputs data cells) :
    ((rawEvents data).map fun event => (event.1, event.2.1)).Nodup := by
  apply address_clocks_distinct
  intro address
  obtain ⟨history, permutation, _⟩ :=
    SeedTransfer.raw_cell_history (SeedProofs.transfer_facts hp accepted inputs) inputs.toSeedInputs address
  have unique : (history.val.map Prod.fst).Nodup := by
    apply List.pairwise_map.mpr
    exact history.property.imp (by
      intro a b less equal
      change b.1 < a.1 at less
      omega)
  exact (permutation.map Prod.fst).nodup_iff.mp unique

private theorem member_flatMap_sublist (f : α → List β) {items : List α} {item : α}
    (member : item ∈ items) : (f item).Sublist (items.flatMap f) := by
  induction items with
  | nil => cases member
  | cons first rest ih =>
    rcases List.mem_cons.mp member with same | member
    · subst first
      exact List.sublist_append_left _ _
    · exact (ih member).trans (List.sublist_append_right _ _)

private theorem row_events_sublist {data : MemoryData p} {row : Row p}
    (member : row ∈ data.rows) : (row.memorySteps.map transferEvent).Sublist (rawEvents data) := by
  simp only [rawEvents, Trace.Proofs.Transfer.rawEvents, transferData, MemoryData.steps, List.map_flatMap]
  apply List.Sublist.trans ?_ (List.sublist_append_right _ _)
  exact member_flatMap_sublist (fun r : Row p => r.memorySteps.map transferEvent) member

/-- State-free `row_addresses_distinct`: one worker call touches each address once. -/
theorem seed_row_addresses_distinct [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    {data : MemoryData p} (accepted : MemoryAccepted data)
    {cells : List Cell} (inputs : SeedProofs.SeedInputs data cells)
    {row : Row p} (member : row ∈ data.rows) :
    (row.memorySteps.map fun edge => edge.1.address).Nodup := by
  have unique := (seed_raw_address_clocks_distinct hp accepted inputs).sublist
    ((row_events_sublist member).map (fun event => (event.1, event.2.1)))
  let clock := (decodeTimestamp row.assignment row.columns.invocation).value + 3
  have times : (row.memorySteps.map transferEvent).map (fun event => (event.1, event.2.1)) =
      (row.memorySteps.map fun edge => edge.1.address).map (fun address => (clock, address)) := by
    simp only [Row.memorySteps, List.map_map, Function.comp_def]
    apply List.map_congr_left
    intro port portMember
    have present : port ∈ row.ports := by simpa only [Array.mem_toList_iff] using portMember
    have time := (SeedProofs.writes_bounded (by omega) accepted inputs member present).2
    rw [port_offset row present] at time
    simp only [transferEvent, clock, time]
  rw [times] at unique
  exact unique.of_map _

theorem word_of_toBitVec {word : Word} (bound : word.Bounded) : Word.ofBitVec word.toBitVec = word :=
  Word.eq_of_value (Word.ofBitVec_bound _) bound (by rw [Word.ofBitVec_value, Word.toBitVec_toNat bound])

/-! ### RV boundary reads -/

/-- A seed token's word, given the RV read of its cell. -/
theorem rv_seed_word {data : MemoryData p} {before : RV.State} {cells : List Cell}
    (inputs : RVBoundaryInputs data before cells) {token : MemoryToken p} (present : token ∈ data.initial)
    {cell : Cell} (code : token.address = cell.addressCode) {value : BitVec 32}
    (read : cell.readRV before = some value) : token.word = Word.ofBitVec value := by
  obtain ⟨other, _, otherCode, otherRead⟩ := inputs.reads token present
  have same : other = cell := cell_address_injective (otherCode.trans code)
  subst other
  have equal : token.word.toBitVec = value := by
    have := otherRead.symm.trans read
    simpa only [memoryWord, MemoryToken.word] using Option.some.inj this
  have bound := inputs.toSeed.words token present
  rw [← equal]
  apply Word.eq_of_value bound (Word.ofBitVec_bound _)
  rw [Word.ofBitVec_value, Word.toBitVec_toNat bound]

/-- The seed facts' pointer characterization, read from the starting RV state. -/
theorem rv_seed_register {data : MemoryData p} {initial : RV.State} {cells : List Cell}
    (inputs : RVBoundaryInputs data initial cells) {index : BitVec 5} {pointer : BitVec 32}
    (source : ∃ token ∈ data.initial, token.address = (Cell.register index).addressCode ∧
      token.word = Word.ofBitVec pointer) :
    (Cell.register index).readRV initial = some pointer := by
  obtain ⟨token, present, code, word⟩ := source
  obtain ⟨cell, _, cellCode, read⟩ := inputs.reads token present
  have same : cell = .register index := cell_address_injective (cellCode.trans code)
  subst cell
  rw [read]
  show some token.word.toBitVec = some pointer
  rw [word, Word.ofBitVec_roundtrip]

/-- RV `boundary_image`: a boundary `RV.State` image is the proof-level `RVBoundaryInputs`. -/
theorem RVBoundaryMemoryInputs.toRVBoundaryInputs {data : MemoryData p} {before : RV.State} {cells : List Cell}
    (inputs : RVBoundaryMemoryInputs data before cells) : RVBoundaryInputs data before cells := by
  refine ⟨⟨⟨inputs.image.addresses, inputs.distinct⟩, ?_, inputs.clocks, inputs.clockRoom,
    inputs.invocationHigh⟩, ?_⟩
  · intro token member
    obtain ⟨cell, _, value, _, _, word⟩ := inputs.image.values token member
    rw [word]
    exact Word.ofBitVec_bound value
  · intro token member
    obtain ⟨cell, present, value, code, read, word⟩ := inputs.image.values token member
    refine ⟨cell, present, code, ?_⟩
    show cell.readRV before = some token.word.toBitVec
    rw [word, Word.ofBitVec_roundtrip]
    exact read

/-! ### Grouped RV histories -/

/-- An RV history split into consecutive worker calls (newest first). -/
inductive GroupedRVHistory (cells : List Cell) (accesses : α → List MemoryAccess) :
    List α → RV.State → RV.State → Prop where
  | nil (before) : GroupedRVHistory cells accesses [] before before
  | cons {row rest before middle after events}
      (past : GroupedRVHistory cells accesses rest before middle)
      (permutation : events.Perm (accesses row))
      (current : RVHistory cells events middle after) :
      GroupedRVHistory cells accesses (row :: rest) before after

theorem rv_grouped_history {rows : List α} {events : List MemoryAccess}
    {cells : List Cell} {before after : RV.State} (clock : α → Nat) (accesses : α → List MemoryAccess)
    (rowOrder : rows.Pairwise (fun a b => clock b < clock a))
    (eventOrder : events.Pairwise (fun a b => b.1 ≤ a.1))
    (permutation : events.Perm (rows.flatMap accesses))
    (times : ∀ row ∈ rows, ∀ event ∈ accesses row, event.1 = clock row)
    (history : RVHistory cells events before after) :
    GroupedRVHistory cells accesses rows before after := by
  have coverage : ∀ event ∈ events, ∃ row ∈ rows, event.1 = clock row := by
    intro event member
    obtain ⟨row, included, present⟩ := List.mem_flatMap.mp (permutation.mem_iff.mp member)
    exact ⟨row, included, times row included event present⟩
  have grouped := group_call_events clock rowOrder eventOrder coverage
  have unique : (rows.map clock).Nodup := by
    apply List.pairwise_map.mpr
    exact rowOrder.imp (by intro a b less; omega)
  have groups : ∀ row ∈ rows,
      (events.filter fun event => decide (event.1 = clock row)).Perm (accesses row) :=
    fun row member => call_group_perm clock accesses unique permutation times member
  rw [← grouped] at history
  clear permutation times coverage grouped eventOrder unique rowOrder
  induction rows generalizing after with
  | nil => cases history; exact .nil before
  | cons row rest ih =>
    rw [List.flatMap_cons] at history
    obtain ⟨middle, past, current⟩ := rv_history_append.mp history
    exact .cons (ih past (fun later member => groups later (List.mem_cons_of_mem _ member)))
      (groups row List.mem_cons_self) current

theorem rv_ungrouped_history {rows : List α} {cells : List Cell} {accesses : α → List MemoryAccess}
    {before after : RV.State} (history : GroupedRVHistory cells accesses rows before after) :
    ∃ events, events.Perm (rows.flatMap accesses) ∧ RVHistory cells events before after := by
  induction history with
  | nil => exact ⟨[], List.Perm.refl _, .nil _⟩
  | @cons row rest before middle after events past permutation current ih =>
    obtain ⟨earlier, earlierPerm, earlierHistory⟩ := ih
    exact ⟨events ++ earlier, by simpa only [List.flatMap_cons] using permutation.append earlierPerm,
      rv_history_append.mpr ⟨middle, earlierHistory, current⟩⟩

theorem rv_grouped_trace_mapping {p : Nat} {data : MemoryData p}
    {initial after : RV.State} {cells : List Cell} {rows : List (Row p)}
    (permutation : rows.Perm data.rows)
    (history : GroupedRVHistory cells (fun row => row.memorySteps.map transferEvent) rows initial after)
    (terminal : ∀ token ∈ data.terminal, ∃ cell ∈ cells, cell.addressCode = token.address ∧
      cell.readRV after = some (memoryWord token.value)) :
    Delegation.RVTraceMapping data initial after cells := by
  constructor
  · obtain ⟨events, eventPerm, actual⟩ := rv_ungrouped_history history
    refine ⟨events, ?_, actual⟩
    have rows := List.Perm.flatMap_right (fun row => row.memorySteps.map transferEvent) permutation
    have pooled : data.rows.flatMap (fun row => row.memorySteps.map transferEvent) =
        data.steps.map transferEvent := by
      simp only [MemoryData.steps, List.map_flatMap]
    exact eventPerm.trans (pooled ▸ rows)
  · simpa only [Trace.MemoryToken.word, memoryWord] using terminal

theorem rv_grouped_boundaries {rows : List α} {cells : List Cell} {before after : RV.State}
    {accesses : α → List MemoryAccess}
    (history : GroupedRVHistory cells accesses rows before after) :
    ∃ states : List RV.State, ∃ count : states.length = rows.length + 1,
      states.head? = some after ∧ states.getLast? = some before ∧
      ∀ (i : Nat) (bound : i < rows.length), ∃ events : List MemoryAccess,
        events.Perm (accesses (rows[i]'bound)) ∧
          RVHistory cells events (states[i + 1]'(by omega)) (states[i]'(by omega)) := by
  induction history with
  | nil before =>
    refine ⟨[before], rfl, rfl, rfl, ?_⟩
    intro i bound
    simp at bound
  | @cons row rest before middle after events past permutation current ih =>
    obtain ⟨states, count, head, last, steps⟩ := ih
    refine ⟨after :: states, by simp only [List.length_cons]; omega, rfl, ?_, ?_⟩
    · simp only [List.getLast?_cons, last, Option.getD_some]
    · intro i bound
      cases i with
      | zero =>
        have first : states[0]'(by omega) = middle := by
          have first := head
          rw [List.head?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at first
          exact Option.some.inj first
        refine ⟨events, permutation, ?_⟩
        simpa only [List.getElem_cons_zero, List.getElem_cons_succ, first] using current
      | succ i =>
        have earlier : i < rest.length := by simpa only [List.length_cons, Nat.succ_lt_succ_iff] using bound
        obtain ⟨earlierEvents, matching, realized⟩ := steps i earlier
        exact ⟨earlierEvents, matching, realized⟩

/-! ### Per-port observations -/

/-- One `Cell.applyRV` makes the cell read the applied value (not x0). -/
theorem applyRV_readback {before after : RV.State} {cell : Cell} {value : BitVec 32}
    (applied : cell.applyRV value before = some after) (nonzero : cell ≠ .register 0)
    (aligned : cell.Aligned) : cell.readRV after = some value := by
  unfold Cell.applyRV at applied
  by_cases unchanged : cell.readRV before = some value
  · simp only [unchanged, ↓reduceIte] at applied
    cases Option.some.inj applied
    exact unchanged
  · simp only [unchanged, ↓reduceIte] at applied
    obtain ⟨result, written, readback⟩ := writeRV_readback cell value before
      (fun zero => False.elim (nonzero zero)) aligned
    rw [written] at applied
    cases Option.some.inj applied
    exact readback

/-- RV `atomic_observations`: within one call's history (each address once) every access reads its value at the
    call's start state and leaves its written value at the call's end state. -/
theorem rv_atomic_observations {cells : List Cell} {events : List MemoryAccess}
    {before after : RV.State} (history : RVHistory cells events before after)
    (aligned : ∀ cell ∈ cells, cell.Aligned)
    (noZero : ∀ event ∈ events, event.2.1 ≠ (Cell.register 0).addressCode)
    (distinct : (events.map fun event => event.2.1).Nodup) :
    ∀ event ∈ events, ∃ cell ∈ cells, cell.addressCode = event.2.1 ∧
      cell.readRV before = some (memoryWord event.2.2.1) ∧
      cell.readRV after = some (memoryWord event.2.2.2) := by
  induction history with
  | nil => intro event member; cases member
  | @cons event rest before middle after past cell member address old written ih =>
    have unique := List.nodup_cons.mp distinct
    have untouched : ∀ other ∈ rest, other.2.1 ≠ cell.addressCode := by
      intro other present same
      exact unique.1 (List.mem_map.mpr ⟨other, present, same.trans address⟩)
    have tail := ih (fun e m => noZero e (List.mem_cons_of_mem _ m)) unique.2
    intro other included
    rcases List.mem_cons.mp included with same | included
    · subst other
      have nonzero : cell ≠ .register 0 := by
        intro zero
        exact noZero event List.mem_cons_self (by rw [← address, zero])
      have read : cell.readRV before = some (memoryWord event.2.2.1) := by
        cases cell with
        | register index =>
          have earlier := rv_history_cell_frame past aligned (.register index) trivial untouched
            (readRV_register index before)
          rw [earlier] at old
          rw [readRV_register]
          exact old
        | ram address' =>
          have readable := readable_of_aligned (aligned _ member)
          have earlier := rv_history_cell_frame past aligned (.ram address') (aligned _ member) untouched
            (readRV_ram before readable)
          rw [earlier] at old
          rw [readRV_ram before readable]
          exact old
      exact ⟨cell, member, address, read, applyRV_readback written nonzero (aligned cell member)⟩
    · obtain ⟨actual, present, code, read, result⟩ := tail other included
      have different : actual ≠ cell := by
        intro same
        exact untouched other included (by rw [← code, same])
      exact ⟨actual, present, code, read,
        applyRV_frame written different (aligned cell member) (aligned actual present) result⟩

theorem rv_row_atomic_observations [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    {data : MemoryData p} (accepted : MemoryAccepted data)
    {before after : RV.State} {cells : List Cell} (inputs : SeedProofs.SeedInputs data cells)
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
      seed_row_addresses_distinct hp accepted inputs member
  have noZero : ∀ event ∈ events, event.2.1 ≠ (Cell.register 0).addressCode := by
    intro event eventMember
    obtain ⟨edge, edgeMember, rfl⟩ := List.mem_map.mp (permutation.mem_iff.mp eventMember)
    change edge ∈ row.ports.toList.map (fun port => (readToken row.assignment port, row.writeToken port)) at edgeMember
    obtain ⟨port, portMember, rfl⟩ : ∃ port ∈ row.ports.toList,
      (readToken row.assignment port, row.writeToken port) = edge := List.mem_map.mp edgeMember
    exact port_not_zero row (by simpa only [Array.mem_toList_iff] using portMember)
  have observations := rv_atomic_observations history aligned noZero distinct
  intro port portMember
  have present : transferEvent (readToken row.assignment port, row.writeToken port) ∈ events := by
    apply permutation.mem_iff.mpr
    apply List.mem_map.mpr
    refine ⟨(readToken row.assignment port, row.writeToken port), ?_, rfl⟩
    apply List.mem_map.mpr
    exact ⟨port, by simpa only [Array.mem_toList_iff] using portMember, rfl⟩
  exact observations _ present

/-- RV `grouped_atomic_boundaries`: per-call RV states (newest first) with each call's port observations. -/
theorem rv_grouped_atomic_boundaries [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    {data : MemoryData p} (accepted : MemoryAccepted data)
    {initial after : RV.State} {cells : List Cell} (inputs : SeedProofs.SeedInputs data cells)
    {ordered : List (Row p)} (permutation : ordered.Perm data.rows)
    (history : GroupedRVHistory cells (fun row => row.memorySteps.map transferEvent) ordered initial after)
    (aligned : ∀ cell ∈ cells, cell.Aligned) :
    ∃ states : List RV.State, ∃ count : states.length = ordered.length + 1,
      states.head? = some after ∧ states.getLast? = some initial ∧
      ∀ (i : Nat) (bound : i < ordered.length),
        let row := ordered[i]'bound
        ∃ events : List MemoryAccess, events.Perm (row.memorySteps.map transferEvent) ∧
          RVHistory cells events (states[i + 1]'(by omega)) (states[i]'(by omega)) ∧
          ∀ port ∈ row.ports, ∃ cell ∈ cells, cell.addressCode = port.address.code row.assignment ∧
            cell.readRV (states[i + 1]'(by omega)) = some (memoryWord (port.readCode row.assignment)) ∧
            cell.readRV (states[i]'(by omega)) = some (memoryWord (port.writeCode row.assignment)) := by
  obtain ⟨states, count, head, last, steps⟩ := rv_grouped_boundaries history
  refine ⟨states, count, head, last, ?_⟩
  intro i bound
  obtain ⟨events, eventsPerm, current⟩ := steps i bound
  exact ⟨events, eventsPerm, current,
    rv_row_atomic_observations hp accepted inputs (permutation.mem_iff.mp (List.getElem_mem _))
      current eventsPerm aligned⟩

/-- RV `history_cell_copy_frame`: a cell whose every access copies its read value keeps its read. -/
theorem rv_history_cell_copy_frame {cells : List Cell} {events : List MemoryAccess}
    {before after : RV.State} (history : RVHistory cells events before after)
    (aligned : ∀ cell ∈ cells, cell.Aligned) (target : Cell)
    (targetAligned : target.Aligned)
    (copies : ∀ event ∈ events, event.2.1 = target.addressCode →
      memoryWord event.2.2.1 = memoryWord event.2.2.2)
    {value : BitVec 32} (read : target.readRV before = some value) :
    target.readRV after = some value := by
  induction history with
  | nil => exact read
  | @cons event rest before middle after past cell member address old written ih =>
    have earlier := ih (fun e present => copies e (List.mem_cons_of_mem _ present)) read
    by_cases same : target = cell
    · subst target
      have equal : value = memoryWord event.2.2.2 :=
        (Option.some.inj (earlier.symm.trans old)).trans (copies event List.mem_cons_self address.symm)
      unfold Cell.applyRV at written
      simp only [earlier.trans (congrArg some equal), ↓reduceIte] at written
      cases Option.some.inj written
      exact earlier
    · exact applyRV_frame written same (aligned cell member) targetAligned earlier

end Airbender.Delegation.Proofs
