module
public import Proven.Keccak.ControlHistory
public import Proven.Keccak.PointerHistory
public import Proven.Keccak.StateCells
public import Proven.Delegation.RVCallHistory
public import Proven.Delegation.SeedOperations
public import Proven.Delegation.CallPaths
public import Proven.Defs.Circuits.Keccak.Artifact
public import Proven.Defs.Helpers.Memory.Ports
public import Proven.Defs.Trace.Workers.Keccak.Call

@[expose] public section

/-! State-free twins of the special5 span's control, pointer, effect and lane-domain lemmas (`ControlHistory.lean`,
    `PointerHistory.lean`, `CallExecution.lean`, `StateCells.lean`). Those take a Sail `BoundaryInputs` and read the
    initial x10/x11 from the Sail state; here the public facts are the seed tokens (`SeedInputs`) and the x10 seed
    word, with no machine state, so the RV route can use them. Proof bodies follow the Sail ones. -/

namespace Airbender.Keccak.Proofs
open Trace Trace.Proofs Delegation.Proofs Arithmetic
set_option warningAsError true
set_option maxRecDepth 16384

/-- Seed-level special5 call span: the seed facts, modeled tables, the family/active rows, the tracked x10 cell, its
    seed word (zero) and the call count. -/
structure SeedCallInputs [Fact p.Prime] (data : Delegation.MemoryData p) (cells : List Cell) : Prop where
  memory : Delegation.SeedProofs.SeedInputs data cells
  tables : data.setup = Delegation.modeledSetup Controller.rows
  controlCell : Cell.register 10 ∈ cells
  controlStart : ∀ token ∈ data.initial, token.address = (Cell.register 10).addressCode → token.word = ⟨0, 0⟩
  family : ∀ row ∈ data.rows, row.family = .keccak
  active : ∀ row ∈ data.rows, row.assignment Variables.execute = 1
  calls : data.rows.length = 649

theorem seed_call_path [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    {data : Delegation.MemoryData p} {cells : List Cell}
    (accepted : Delegation.MemoryAccepted data) (inputs : SeedCallInputs data cells) :
    ∃ sink ∈ data.terminal, sink.address = (Cell.register 10).addressCode ∧
      ∃ path : List (MemoryToken p), ∃ size : path.length = 650, path.getLast? = some sink ∧
        (path.map fun token => (timeOfPair token.time).value).Pairwise (· < ·) ∧
        (path.zip path.tail).Perm (data.rows.map fun row =>
          (readToken row.assignment importedConstraintsMemoryPorts[0],
            row.writeToken importedConstraintsMemoryPorts[0])) ∧
        ∀ i : Fin 650, (path[i.val]'(by have := i.isLt; omega)).word =
          ⟨(scheduleControl i).packed, 0⟩ := by
  obtain ⟨source, sourceMember, sourceCode⟩ := seed_cell_source inputs.memory inputs.controlCell
  have sourceWord := inputs.controlStart source sourceMember sourceCode
  obtain ⟨sink, sinkMember, address, path, head, last, ordered, matching⟩ :=
    (Delegation.SeedProofs.memory_effects hp accepted inputs.memory).paths _ sourceMember
  have edges : (path.zip path.tail).Perm
      (data.rows.map fun row => (readToken row.assignment importedConstraintsMemoryPorts[0],
        row.writeToken importedConstraintsMemoryPorts[0])) := by
    rw [sourceCode] at matching
    rw [control_edges inputs.family] at matching
    exact matching
  have length : path.length = 650 := by
    have count := edges.length_eq
    have positive : 0 < path.length := by
      cases path with
      | nil => simp at head
      | cons _ _ => simp
    simp only [List.length_zip, List.length_tail, List.length_map, inputs.calls] at count
    omega
  have checks : ∀ edge ∈ path.zip path.tail, ∃ w : Nat → ZMod p,
      FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints data.setup.keccak) ∧ w 0 = 1 ∧
      edge.1.word = Word.mk (w 3).val (w 4).val ∧ edge.2.word = Word.mk (w 5).val (w 6).val := by
    intro edge member
    obtain ⟨row, rowMember, rfl⟩ := List.mem_map.mp (edges.mem_iff.mp member)
    cases row with
    | mk kind w =>
      have family := inputs.family ⟨kind, w⟩ rowMember
      change kind = .keccak at family
      subst kind
      have core := Verification.holds_of_sublist (accepted.constraints _ rowMember)
        (List.sublist_append_left (importedConstraints data.setup.keccak) importedConstraintsTimestampLookups)
      refine ⟨w, core, inputs.active _ rowMember, ?_, ?_⟩
      all_goals simp [readToken, Delegation.Row.writeToken, MemoryToken.word,
        importedConstraintsMemoryPorts, MemoryPort.readCode, MemoryPort.writeCode, pairCode]
  exact ⟨sink, sinkMember, address.trans sourceCode, path, length, last, ordered, edges,
    forced_path (by dsimp [timestampBase] at hp; omega) length head sourceWord checks⟩

/-- Seed twin of `call_schedule`: the 649 rows ordered by native write clock read/write the pinned controls. -/
theorem seed_call_schedule [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    {data : Delegation.MemoryData p} {cells : List Cell}
    (accepted : Delegation.MemoryAccepted data) (inputs : SeedCallInputs data cells) :
    CallSchedule data := by
  obtain ⟨sink, sinkMember, address, path, length, last, increasing, matching, schedule⟩ :=
    seed_call_path hp accepted inputs
  obtain ⟨ordered, perm, edges, clocks⟩ :=
    Delegation.Proofs.ordered_rows_from_path _ matching increasing
  have count : ordered.length = 649 := perm.length_eq.trans inputs.calls
  refine ⟨ordered, count, perm, clocks, ?_⟩
  intro i
  have edge : (readToken (ordered[i.val]'(by omega)).assignment importedConstraintsMemoryPorts[0],
      (ordered[i.val]'(by omega)).writeToken importedConstraintsMemoryPorts[0]) =
      (path[i.val]'(by omega), path[i.val + 1]'(by omega)) := by
    have atIndex := congrArg (fun pairs => pairs[i.val]?) edges
    simpa [List.getElem?_eq_getElem, count, length] using atIndex.symm
  have read := congrArg (fun pair => pair.1.word) edge
  have write := congrArg (fun pair => pair.2.word) edge
  constructor
  · simpa [readToken, MemoryToken.word, MemoryPort.readCode, WordColumns.code,
      importedConstraintsMemoryPorts, pairCode] using
      read.trans (schedule ⟨i.val, by have := i.isLt; omega⟩)
  · simpa [Delegation.Row.writeToken, MemoryToken.word, MemoryPort.writeCode, WordColumns.code,
      importedConstraintsMemoryPorts, pairCode] using
      write.trans (schedule ⟨i.val + 1, by have := i.isLt; omega⟩)

/-- Seed twin of `call_pointer`: x11 is a tracked cell, and every row's state pointer and x11's terminal token are
    its seed word. -/
theorem seed_call_pointer [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    {data : Delegation.MemoryData p} {cells : List Cell}
    (accepted : Delegation.MemoryAccepted data) (inputs : SeedCallInputs data cells) :
    Cell.register 11 ∈ cells ∧ ∀ source ∈ data.initial, source.address = (Cell.register 11).addressCode →
      (∀ row ∈ data.rows, statePointer row.assignment = source.word) ∧
      ∃ sink ∈ data.terminal, sink.address = (Cell.register 11).addressCode ∧ sink.word = source.word := by
  obtain ⟨row, member⟩ : ∃ row, row ∈ data.rows := by
    have nonempty : data.rows ≠ [] := by
      intro empty
      have count := inputs.calls
      simp [empty] at count
    exact List.exists_mem_of_ne_nil _ nonempty
  have family := inputs.family row member
  have portMember : importedConstraintsMemoryPorts[1] ∈ row.ports := by
    simp [Delegation.Row.ports, family, importedConstraintsMemoryPorts]
  refine ⟨seed_port_initialized_cell hp accepted inputs.memory member portMember (cell := .register 11) (by rfl), ?_⟩
  intro source present code
  have stable := seed_readonly_cell hp accepted inputs.memory present (by rw [code]; exact pointer_copies inputs.family)
  refine ⟨?_, by simpa only [code] using stable.2⟩
  intro row member
  have family := inputs.family row member
  have portMember : importedConstraintsMemoryPorts[1] ∈ row.ports := by
    simp [Delegation.Row.ports, family, importedConstraintsMemoryPorts]
  have edgeMember : (readToken row.assignment importedConstraintsMemoryPorts[1],
      row.writeToken importedConstraintsMemoryPorts[1]) ∈ data.steps :=
    List.mem_flatMap.mpr ⟨row, member, List.mem_map.mpr ⟨_, by simpa using portMember, rfl⟩⟩
  have result := stable.1 _ edgeMember (by rw [code]; rfl)
  simpa [statePointer, readToken, MemoryToken.word, MemoryPort.readCode,
    WordColumns.code, importedConstraintsMemoryPorts, pairCode] using result

/-- Seed twin of `call_execution`'s effects: every row has the native effects. -/
theorem seed_call_effects [Fact p.Prime] (hp : 16777216 ≤ p)
    (inverse : 256 * (-7864320 : ZMod p) = 1)
    {data : Delegation.MemoryData p} {cells : List Cell}
    (accepted : Delegation.MemoryAccepted data) (inputs : SeedCallInputs data cells) :
    Delegation.WordBounds data ∧ ∀ row ∈ data.rows, Native.RowEffects row.assignment := by
  have bounds := Delegation.SeedProofs.operation_word_bounds (by omega) (by linear_combination inverse)
    accepted inputs.memory inputs.tables
    (by intro row member other; have := inputs.family row member; simp_all)
    (fun row member _ => inputs.active row member)
  refine ⟨bounds, ?_⟩
  intro row member
  have holds := accepted.constraints row member
  have reads := bounds.reads row member
  have family := inputs.family row member
  rcases row with ⟨kind, w⟩
  change kind = .keccak at family
  subst kind
  simp only [Delegation.Row.constraints, inputs.tables, Delegation.modeledSetup] at holds
  have core := Verification.holds_of_sublist holds (List.sublist_append_left
    (importedConstraints (setupTable Controller.rows)) importedConstraintsTimestampLookups)
  exact Native.Proofs.native_effects hp inverse core (inputs.active _ member) reads

/-- Seed twin of `call_state_cells`: every half of every one of the 31 physical lanes at the seed pointer is a tracked
    cell. -/
theorem seed_call_state_cells [Fact p.Prime] (hp : 16777216 ≤ p)
    (inverse : 256 * (-7864320 : ZMod p) = 1)
    {data : Delegation.MemoryData p} {cells : List Cell}
    (accepted : Delegation.MemoryAccepted data) (inputs : SeedCallInputs data cells)
    {source : MemoryToken p} (present : source ∈ data.initial)
    (code : source.address = (Cell.register 11).addressCode) :
    ∀ physical : Fin 31, ∀ half : Fin 2,
      Cell.ram (source.word.toBitVec + BitVec.ofNat 32 (8 * physical.val + 4 * half.val)) ∈ cells := by
  have clockBound : 2 * timestampBase + 4 < p := by norm_num [timestampBase]; omega
  obtain ⟨ordered, count, permutation, _, controls⟩ := seed_call_schedule clockBound accepted inputs
  have pointers := ((seed_call_pointer clockBound accepted inputs).2 source present code).1
  have effects := (seed_call_effects hp inverse accepted inputs).2
  intro physical half
  obtain ⟨call, lane, coverage⟩ := scheduled_lane_coverage physical
  let row := ordered[call.val]'(by have := call.isLt; omega)
  have member : row ∈ data.rows := permutation.mem_iff.mp (List.getElem_mem _)
  have family := inputs.family row member
  have control : (row.assignment Variables.controlReadLo).val =
      (scheduleControl ⟨call.val, by omega⟩).packed := congrArg Word.lo (controls call).1
  have indices := scheduled_lane_indices call (effects row member) (inputs.active row member) control
  have index : (row.assignment (7 + lane.val)).val = physical.val := (indices lane).trans coverage
  let position : Fin 12 := ⟨2 * lane.val + half.val, by omega⟩
  let port := importedConstraintsMemoryPorts[2 + position.val]'(by change 2 + position.val < 14; omega)
  have portPresent : port ∈ row.ports := by
    rw [Delegation.Row.ports, family]
    exact Array.getElem_mem _
  have shape : port.address = .indirect importedConstraintsIndirectPorts[position] := by
    have all : ∀ i : Fin 12, (importedConstraintsMemoryPorts[2 + i.val]'(by change 2 + i.val < 14; omega)).address =
        .indirect importedConstraintsIndirectPorts[i] := by
      intro i
      fin_cases i <;> rfl
    exact all position
  have edgeMember : (readToken row.assignment port, row.writeToken port) ∈ data.steps := by
    apply List.mem_flatMap.mpr
    refine ⟨row, member, ?_⟩
    apply List.mem_map.mpr
    exact ⟨port, by simpa only [Array.mem_toList_iff] using portPresent, rfl⟩
  obtain ⟨cell, cellTracked, cellCode⟩ := seed_initialized_cell clockBound accepted inputs.memory edgeMember
  change cell.addressCode = port.address.code row.assignment at cellCode
  rw [shape] at cellCode
  have tracked := (indirect_cell cellCode) ▸ cellTracked
  rw [(effects row member).addresses.addresses position, pointers row member] at tracked
  have div : position.val / 2 = lane.val := by dsimp [position]; have := half.isLt; omega
  have mod : position.val % 2 = half.val := by dsimp [position]; have := half.isLt; omega
  simpa only [div, mod, index] using tracked

end Airbender.Keccak.Proofs
