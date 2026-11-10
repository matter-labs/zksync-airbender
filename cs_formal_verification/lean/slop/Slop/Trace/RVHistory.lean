module
public import Slop.Trace.RVCells
public import Human.Helpers.Memory.RVHistory
public import Slop.Trace.RowHistory
public import Slop.Trace.LastWrite
public import Slop.Trace.RowContext
public import Slop.Trace.Addresses
public import Slop.Defs.Helpers.Memory.Ports
public import Slop.Defs.Helpers.Context.Model
public import Slop.Defs.Helpers.Memory.RowEvents
public import Slop.Defs.Helpers.Memory.History

@[expose] public section

/-! RV32 history core. The event-level core (`MemoryHistory`, timestamp
    sorting, permutation, `native_row_order`, `native_events_projection`, `native_history_parts`,
    `native_memory_history`) is state-free. The state-touching parts are the
    history inductive over `RV.State` (`Cell.readRV` / `Cell.writeRV`), seeding from `initialImageRV`, realization,
    relabelling, address membership, and the row position. -/

namespace Airbender.Trace.Proofs
open Arithmetic

/-- RV sibling of `SailStateMatches`: the RV state reads the latest value of each tracked cell. -/
def RVStateMatches (cells : List Cell) (history : TimestampSortedMemoryAccessList) (state : RV.State) : Prop :=
  ∀ cell ∈ cells, cell.readRV state =
    some (memoryWord (MemoryAccessList.lastWriteValue history.val history.property cell.addressCode))

theorem _root_.Airbender.Trace.RVHistory.writes {cells : List Cell} {events : List MemoryAccess}
    {before after : RV.State} (history : RVHistory cells events before after) :
    RVWriteHistory cells (events.map fun event => (event.2.1, event.2.2.2)) before after := by
  induction history with
  | nil => exact .nil _
  | cons past cell member address read written ih =>
    exact .cons ih cell member address written

/-- The write-only RV state mapping is deterministic. -/
theorem RVWriteHistory.unique {cells : List Cell} {values : List (Nat × Nat)}
    {before left right : RV.State} (a : RVWriteHistory cells values before left)
    (b : RVWriteHistory cells values before right) : left = right := by
  induction a generalizing right with
  | nil => cases b; rfl
  | cons past cell member address write ih =>
    cases b with
    | cons other second secondMember secondAddress secondWrite =>
      have sameCell : cell = second := cell_address_injective (address.trans secondAddress.symm)
      have sameState := ih other
      subst second
      subst sameState
      exact Option.some.inj (write.symm.trans secondWrite)

theorem rv_history_append {cells : List Cell} {new old : List MemoryAccess}
    {before after : RV.State} :
    RVHistory cells (new ++ old) before after ↔
      ∃ middle, RVHistory cells old before middle ∧ RVHistory cells new middle after := by
  constructor
  · intro history
    induction new generalizing after with
    | nil => exact ⟨after, history, .nil after⟩
    | cons event rest ih =>
      cases history with
      | cons past cell member address read written =>
        obtain ⟨middle, oldHistory, newHistory⟩ := ih past
        exact ⟨middle, oldHistory, .cons newHistory cell member address read written⟩
  · rintro ⟨middle, oldHistory, newHistory⟩
    induction newHistory with
    | nil => exact oldHistory
    | cons past cell member address read written ih =>
      exact .cons (ih oldHistory) cell member address read written

theorem rv_history_relabel (clock : MemoryAccess → Nat) {cells : List Cell}
    {events : List MemoryAccess} {before after : RV.State}
    (history : RVHistory cells events before after) :
    RVHistory cells (events.map (relabelMemoryEvent clock)) before after := by
  induction history with
  | nil before => exact .nil before
  | cons past cell member address read write ih =>
    exact .cons ih cell member address read write

/-- Every realized access belongs to the public cell domain. -/
theorem rv_history_address_member {cells : List Cell} {events : List MemoryAccess}
    {before after : RV.State} (history : RVHistory cells events before after)
    {event : MemoryAccess} (present : event ∈ events) :
    ∃ cell ∈ cells, cell.addressCode = event.2.1 := by
  induction history with
  | nil => simp at present
  | cons past cell member address read write ih =>
    rcases List.mem_cons.mp present with same | earlier
    · subst event; exact ⟨cell, member, address⟩
    · exact ih earlier

/-- Seed matching from the public RV token list: each cell's read is the latest value of its seed token. -/
theorem rv_seed_history_matches {p : Nat} {before : RV.State} {cells : List Cell}
    {tokens : List (MemoryToken p)} (unique : (tokens.map MemoryToken.address).Nodup)
    (reads : ∀ cell ∈ cells, ∃ token ∈ tokens, token.address = cell.addressCode ∧
      cell.readRV before = some (memoryWord token.value))
    (seed : TimestampSortedMemoryAccessList)
    (permutation : seed.val.Perm
      (tokens.map fun token => (token.address, token.address, 0, token.value))) :
    RVStateMatches cells seed before := by
  have distinct : (seed.val.map (fun event => event.2.1)).Nodup := by
    apply (permutation.map (fun event => event.2.1)).nodup_iff.mpr
    simpa only [List.map_map, Function.comp_def] using unique
  intro cell member
  obtain ⟨token, present, address, read⟩ := reads cell member
  have eventMember : List.Mem (α := MemoryAccess)
      (token.address, token.address, 0, token.value) seed.val :=
    permutation.mem_iff.mpr (List.mem_map.mpr ⟨token, present, rfl⟩)
  have last := last_write_unique seed.val seed.property distinct eventMember
  rw [address] at last
  rw [last]
  exact read

/-- Pointwise access to the RV image: each public cell's initial read is the seed token. -/
theorem rvImage_reads {p : Nat} {before : RV.State} :
    ∀ (cells : List Cell) (tokens : List (MemoryToken p)),
      cells.mapM (fun cell => (cell.readRV before).map (cell.initialToken ·)) = some tokens →
      List.Forall₂ (fun cell token => ∃ value, cell.readRV before = some value ∧
        token = cell.initialToken (p := p) value) cells tokens
  | [], tokens, image => by
    have empty : some ([] : List (MemoryToken p)) = some tokens := image
    cases Option.some.inj empty
    exact .nil
  | cell :: tail, tokens, image => by
    rw [List.mapM_cons] at image
    generalize hread : cell.readRV before = read at image
    cases read with
    | none => simp at image
    | some value =>
      generalize hr : List.mapM (fun cell => (cell.readRV before).map (fun x => cell.initialToken (p := p) x)) tail = r at image
      cases r with
      | none => simp at image
      | some remaining =>
        have eq : cell.initialToken value :: remaining = tokens := by
          simpa using image
        subst eq
        exact .cons ⟨value, hread, rfl⟩ (rvImage_reads tail remaining hr)

theorem rvImage_addresses {p : Nat} {before : RV.State} {cells : List Cell}
    {tokens : List (MemoryToken p)}
    (image : initialImageRV before cells = some tokens) :
    tokens.map MemoryToken.address = cells.map Cell.addressCode := by
  have reads := rvImage_reads cells tokens image
  clear image
  induction reads with
  | nil => rfl
  | @cons cell token cells tokens head tail ih =>
    obtain ⟨value, _, rfl⟩ := head
    simpa only [List.map_cons, Cell.initialToken] using congrArg (List.cons cell.addressCode) ih

theorem rvImage_unique {p : Nat} {before : RV.State} {cells : List Cell}
    {tokens : List (MemoryToken p)} (image : initialImageRV before cells = some tokens)
    (domain : cells.Nodup) : (tokens.map MemoryToken.address).Nodup := by
  rw [rvImage_addresses image]
  exact domain.map cell_address_injective

theorem rvImage_cell_source {p : Nat} {before : RV.State} {cells : List Cell}
    {tokens : List (MemoryToken p)} (image : initialImageRV before cells = some tokens) :
    ∀ cell ∈ cells, ∃ token ∈ tokens, ∃ value,
      cell.readRV before = some value ∧ token = cell.initialToken value := by
  have reads := rvImage_reads cells tokens image
  clear image
  induction reads with
  | nil => simp
  | @cons cell token cells tokens head tail ih =>
    intro actual member
    rcases List.mem_cons.mp member with rfl | member
    · obtain ⟨value, read, same⟩ := head
      exact ⟨token, List.mem_cons_self, value, read, same⟩
    · obtain ⟨source, sourceMember, value, read, same⟩ := ih actual member
      exact ⟨source, List.mem_cons_of_mem _ sourceMember, value, read, same⟩

theorem rv_initial_history_matches {p : Nat} {before : RV.State} {cells : List Cell}
    {tokens : List (MemoryToken p)} (image : initialImageRV before cells = some tokens)
    (domain : cells.Nodup) (seed : TimestampSortedMemoryAccessList)
    (permutation : seed.val.Perm
      (tokens.map fun token => (token.address, token.address, 0, token.value))) :
    RVStateMatches cells seed before := by
  apply rv_seed_history_matches (rvImage_unique image domain) ?_ seed permutation
  intro cell member
  obtain ⟨token, present, value, read, equal⟩ := rvImage_cell_source image cell member
  refine ⟨token, present, ?_, ?_⟩
  · rw [equal]; rfl
  · rw [equal]
    simp only [Cell.initialToken, memoryWord, Nat.unpair_pair]
    rw [Word.ofBitVec_roundtrip]
    exact read

/-- One actual RV update advances the representation of Clean's last-write function and preserves every other aligned
    cell. A port equal to the cell's current value leaves the state unchanged (`Cell.applyRV`); otherwise it is a
    `writeRV` (a RAM write always succeeds), whose x0 value is the `zero` hypothesis. -/
theorem rv_matches_after_write {cells : List Cell} {history : TimestampSortedMemoryAccessList}
    {before : RV.State} (boundState : RVStateMatches cells history before)
    (aligned : ∀ cell ∈ cells, cell.Aligned)
    (event : MemoryAccess) (sorted : MemoryAccessList.isTimestampSorted (event :: history.val))
    (cell : Cell) (member : cell ∈ cells) (address : cell.addressCode = event.2.1)
    (zero : cell = .register 0 → memoryWord event.2.2.2 = 0) :
    ∃ after, cell.applyRV (memoryWord event.2.2.2) before = some after ∧
      RVStateMatches cells ⟨event :: history.val, sorted⟩ after := by
  obtain ⟨time, key, old, value⟩ := event
  by_cases unchanged : cell.readRV before = some (memoryWord value)
  · refine ⟨before, ?_, ?_⟩
    · simp [Cell.applyRV, unchanged]
    intro other otherMember
    by_cases same : other = cell
    · subst other
      simpa [MemoryAccessList.lastWriteValue, address] using unchanged
    · have distinctCode : key ≠ other.addressCode := by
        intro sameCode
        exact same (cell_address_injective (sameCode.symm.trans address.symm))
      simp only [MemoryAccessList.lastWriteValue, ite_eq_right distinctCode]
      exact boundState other otherMember
  · obtain ⟨after, written, readback⟩ :=
      writeRV_readback cell (memoryWord value) before zero (aligned cell member)
    refine ⟨after, ?_, ?_⟩
    · simp [Cell.applyRV, unchanged, written]
    intro other otherMember
    by_cases same : other = cell
    · subst other
      simpa [MemoryAccessList.lastWriteValue, address] using readback
    · have distinctCode : key ≠ other.addressCode := by
        intro sameCode
        exact same (cell_address_injective (sameCode.symm.trans address.symm))
      simp only [MemoryAccessList.lastWriteValue, ite_eq_right distinctCode]
      exact writeRV_frame written same (aligned cell member) (aligned other otherMember)
        (boundState other otherMember)

/-- Extend an already-bound initial RV history using Clean consistency. Read values are derived. -/
theorem rv_realize_history {cells : List Cell} (events : List MemoryAccess)
    (seed : TimestampSortedMemoryAccessList) {before : RV.State}
    (boundState : RVStateMatches cells seed before)
    (aligned : ∀ cell ∈ cells, cell.Aligned)
    (addresses : ∀ event ∈ events, ∃ cell ∈ cells, cell.addressCode = event.2.1)
    (zero : ∀ event ∈ events, event.2.1 = (Cell.register 0).addressCode →
      memoryWord event.2.2.2 = 0)
    (sorted : MemoryAccessList.isTimestampSorted (List.append (α := MemoryAccess) events seed.val))
    (consistent : MemoryAccessList.isConsistentOnline (List.append (α := MemoryAccess) events seed.val) sorted) :
    ∃ after, RVHistory cells events before after ∧
      RVStateMatches cells ⟨List.append (α := MemoryAccess) events seed.val, sorted⟩ after := by
  induction events with
  | nil => exact ⟨before, .nil before, boundState⟩
  | cons event rest ih =>
    have ordered := List.Pairwise.of_cons sorted
    change event.2.2.1 = MemoryAccessList.lastWriteValue (List.append (α := MemoryAccess) rest seed.val) ordered event.2.1 ∧
      MemoryAccessList.isConsistentOnline (List.append (α := MemoryAccess) rest seed.val) ordered at consistent
    obtain ⟨middle, past, bound⟩ := ih (fun e m => addresses e (List.mem_cons_of_mem _ m))
      (fun e m => zero e (List.mem_cons_of_mem _ m))
      ordered consistent.2
    obtain ⟨cell, member, address⟩ := addresses event (List.mem_cons_self)
    have read := bound cell member
    rw [address, ← consistent.1] at read
    obtain ⟨after, written, last⟩ := rv_matches_after_write bound aligned event sorted cell member address
      (fun same => zero event (List.mem_cons_self) (by rw [← address, same]))
    exact ⟨after, .cons past cell member address read written, last⟩

/-- Native RV cell reads: every event of an initialized RV history addresses a public cell. -/
theorem rv_initialized_cells {Kind : Type} [CircuitLayout Kind] {p : Nat} [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    [ClockLaws Kind p] (inverse : (-3840 : ZMod p) * 524288 = 1) {trace : Data p Kind}
    (accepted : Accepted trace) (boundary : ClockBoundary trace)
    {before : RV.State} {cells : List Cell}
    (image : initialImageRV before cells = some trace.initialMemory) :
    ∀ row ∈ trace.rows, ∀ port ∈ row.ports,
      ∃ cell ∈ cells, port.address.code row.assignment = cell.addressCode := by
  intro row member port present
  have origin := initialized_addresses hp inverse accepted boundary row member port present
  rw [rvImage_addresses image] at origin
  obtain ⟨cell, belongs, equal⟩ := List.mem_map.mp origin
  exact ⟨cell, belongs, equal.symm⟩

theorem rv_native_event_cells {Kind : Type} [CircuitLayout Kind] [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    [ClockLaws Kind p] (inverse : (-3840 : ZMod p) * 524288 = 1) {trace : Data p Kind}
    (accepted : Accepted trace) (boundary : ClockBoundary trace)
    {before : RV.State} {cells : List Cell} (image : initialImageRV before cells = some trace.initialMemory) :
    ∀ event ∈ trace.nativeEvents, ∃ cell ∈ cells, cell.addressCode = event.2.1 := by
  intro event member
  change event ∈ trace.memorySteps.map (fun edge =>
    (trace.memoryEpoch + (timeOfPair edge.2.time).value, edge.1.address, edge.1.value, edge.2.value)) at member
  obtain ⟨edge, edgeMember, equal⟩ := List.mem_map.mp member
  subst event
  change edge ∈ trace.rows.flatMap Row.memorySteps at edgeMember
  obtain ⟨row, rowMember, rowEdge⟩ := List.mem_flatMap.mp edgeMember
  obtain ⟨port, portMember, rfl⟩ := List.mem_map.mp rowEdge
  obtain ⟨cell, present, address⟩ := rv_initialized_cells hp inverse accepted boundary image row rowMember
    port (by simpa using portMember)
  exact ⟨cell, present, address.symm⟩

/-- Realize the accepted native transfers as an RV history. The x0 law is an explicit hypothesis (discharged
    elsewhere, by the decoder). No read value is assumed. -/
theorem rv_native_history {Kind : Type} [CircuitLayout Kind] [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    [ClockLaws Kind p] (inverse : (-3840 : ZMod p) * 524288 = 1) {trace : Data p Kind}
    (accepted : Accepted trace) (boundary : ClockBoundary trace)
    {before : RV.State} {cells : List Cell} (image : initialImageRV before cells = some trace.initialMemory)
    (domain : cells.Nodup) (aligned : ∀ cell ∈ cells, cell.Aligned)
    (zero : ∀ event ∈ trace.nativeEvents, event.2.1 = (Cell.register 0).addressCode →
      memoryWord event.2.2.2 = 0) :
    ∃ (history : TimestampSortedMemoryAccessList) (events : List MemoryAccess)
      (seed : TimestampSortedMemoryAccessList) (after : RV.State),
      MemoryHistory trace history ∧ List.append (α := MemoryAccess) events seed.val = history.val ∧
      events.Perm trace.nativeEvents ∧ RVHistory cells events before after ∧
      RVStateMatches cells history after := by
  obtain ⟨history, checked⟩ := native_memory_history hp inverse accepted boundary (rvImage_unique image domain)
  obtain ⟨events, seed, combined, permutation, initial⟩ := native_history_parts checked
  have ordered : MemoryAccessList.isTimestampSorted (List.append (α := MemoryAccess) events seed.val) := by
    simpa only [combined] using history.property
  have consistent : MemoryAccessList.isConsistentOnline
      (List.append (α := MemoryAccess) events seed.val) ordered := by
    simpa only [combined] using checked.2
  obtain ⟨after, actual, final⟩ := rv_realize_history events seed
    (rv_initial_history_matches image domain seed initial) aligned
    (fun event member => rv_native_event_cells hp inverse accepted boundary image event
      (permutation.mem_iff.mp member))
    (fun event member => zero event (permutation.mem_iff.mp member)) ordered consistent
  refine ⟨history, events, seed, after, checked, combined, permutation, actual, ?_⟩
  intro cell member
  simpa only [combined] using final cell member

/-- The RV native history in instruction order: rows in descending clock, with the same per-row events. -/
theorem rv_native_row_history {Kind : Type} [CircuitLayout Kind] [Fact p.Prime]
    (hp : 2 * timestampBase + 4 < p) [ClockLaws Kind p]
    (inverse : (-3840 : ZMod p) * 524288 = 1) {trace : Data p Kind}
    (accepted : Accepted trace) (boundary : ClockBoundary trace)
    {before : RV.State} {cells : List Cell}
    (image : initialImageRV before cells = some trace.initialMemory)
    (domain : cells.Nodup) (aligned : ∀ cell ∈ cells, cell.Aligned)
    (zero : ∀ event ∈ trace.nativeEvents, event.2.1 = (Cell.register 0).addressCode →
      memoryWord event.2.2.2 = 0) :
    ∃ (history : TimestampSortedMemoryAccessList) (rows : List (Row p Kind)) (after : RV.State),
      MemoryHistory trace history ∧ rows.Perm trace.rows ∧
      rows.Pairwise (fun a b => rowClock b < rowClock a) ∧
      RVHistory cells (rows.flatMap fun row => (rowEvents trace.memoryEpoch row).reverse) before after ∧
      RVStateMatches cells history after := by
  obtain ⟨history, events, seed, after, consistent, combined, permutation, execution, final⟩ :=
    rv_native_history hp inverse accepted boundary image domain aligned zero
  obtain ⟨rows, rowPermutation, rowSorted, sorted, eventPermutation⟩ :=
    native_row_order hp inverse accepted boundary
  have eventsSorted : MemoryAccessList.isTimestampSorted events := by
    have full : MemoryAccessList.isTimestampSorted (List.append (α := MemoryAccess) events seed.val) := by
      simpa only [combined] using history.property
    exact (List.pairwise_append.mp full).1
  have same := List.Perm.eq_of_pairwise' sorted eventsSorted (eventPermutation.trans permutation.symm)
  exact ⟨history, rows, after, consistent, rowPermutation, rowSorted, same.symm ▸ execution, final⟩

/-- Locate `row` in the RV history: the older rows' writes give the RV state at the row's start. -/
theorem rv_row_context_of_history {Kind : Type} [CircuitLayout Kind] [Fact p.Prime]
    {trace : Data p Kind} {initial : RV.State} {cells : List Cell}
    {rows : List (Row p Kind)} {final : RV.State}
    (rowsPermutation : rows.Perm trace.rows)
    (rowsOrdered : rows.Pairwise (fun a b => b.clock < a.clock))
    (native : RVHistory cells
      (rows.flatMap fun row => (rowEvents trace.memoryEpoch row).reverse) initial final)
    (eventsProjection :
      (rows.flatMap fun row => (rowEvents trace.memoryEpoch row).reverse).Perm trace.nativeEvents)
    {row : Row p Kind} {before : RV.State}
    (position : RVRowPosition trace initial cells row before) :
    ∃ (middle : RV.State) (events : List MemoryAccess) (rawAfter : RV.State),
      (∀ event ∈ events, event ∈ trace.nativeEvents) ∧
      RVHistory cells events initial middle ∧
      RVHistory cells (rowEvents trace.memoryEpoch row).reverse middle rawAfter ∧
      before = { middle with pc := row.start.word.toBitVec } := by
  obtain ⟨newer, older, middle, permutation, ordered, writes, state⟩ := position
  have same : rows = newer ++ row :: older :=
    List.Perm.eq_of_pairwise' rowsOrdered ordered (rowsPermutation.trans permutation.symm)
  rw [same, List.flatMap_append, List.flatMap_cons] at native
  obtain ⟨currentEnd, tailHistory, _⟩ := rv_history_append.mp native
  obtain ⟨currentStart, past, current⟩ := rv_history_append.mp tailHistory
  have canonicalWrites : RVWriteHistory cells (older.flatMap rowWriteValues) initial currentStart := by
    have projected := RVHistory.writes past
    simpa only [List.map_flatMap, row_write_values] using projected
  have equal := RVWriteHistory.unique canonicalWrites writes
  subst currentStart
  refine ⟨middle, _, currentEnd, ?_, past, current, state⟩
  intro event present
  apply eventsProjection.mem_iff.mp
  rw [same, List.flatMap_append, List.flatMap_cons]
  simp only [List.mem_append]
  exact Or.inr (Or.inr present)

/-- Operand reads of an RV row: the first port is a read-only register read (the first port's write equals its
    read), so its value is the pre-state register; the second port reads the same pre-state (the first write is
    the identity on RV.Same). -/
theorem rv_row_operand_reads {cells : List Cell} {columns : TraceColumns}
    {first second destination : MemoryPort} {w : Nat → ZMod p} {i j : BitVec 5} (epoch : Nat)
    (firstReadonly : first.writeValue = none)
    (leftAddress : first.address.code w = (Cell.register i).addressCode)
    (rightAddress : second.address.code w = (Cell.register j).addressCode)
    {before after : RV.State}
    (history : RVHistory cells
      (nativeRowEvents epoch columns #[first, second, destination] w).reverse before after) :
    before.getReg i = memoryWord (first.readCode w) ∧
      before.getReg j = memoryWord (second.readCode w) := by
  have readonly : first.readCode w = first.writeCode w := by
    simp [MemoryPort.readCode, MemoryPort.writeCode, firstReadonly]
  dsimp [nativeRowEvents] at history
  cases history with
  | cons past destinationCell dm da dr dw =>
    cases past with
    | cons past rightCell rm ra rr rw =>
      cases past with
      | cons empty leftCell lm la lr lw =>
        cases empty with
        | nil =>
          have leftEq : leftCell = .register i := cell_address_injective (la.trans leftAddress)
          have rightEq : rightCell = .register j := cell_address_injective (ra.trans rightAddress)
          subst leftEq
          subst rightEq
          have lr' : (Cell.register i).readRV before = some (memoryWord (first.readCode w)) := lr
          have unchanged : (Cell.register i).applyRV (memoryWord (first.writeCode w)) before = some before := by
            rw [← readonly]
            simp [Cell.applyRV, lr']
          have hi : before.getReg i = memoryWord (first.readCode w) :=
            Option.some.inj ((readRV_register i before).symm.trans lr')
          have hm := Option.some.inj (lw.symm.trans unchanged)
          subst hm
          rw [readRV_register] at rr
          exact ⟨hi, Option.some.inj rr⟩

end Airbender.Trace.Proofs
