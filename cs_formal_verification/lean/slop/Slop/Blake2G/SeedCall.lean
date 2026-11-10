module
public import Slop.Blake2G.ControlPool
public import Slop.Blake2G.StateCells
public import Slop.Blake2G.BlockFrame
public import Slop.Delegation.RVCallHistory
public import Slop.Delegation.SeedOperations
public import Human.Circuits.Keccak.Tables.Controller
public import Slop.Blake2G.CallControl
public import Slop.Blake2G.PhysicalPorts
public import Slop.Delegation.CallPaths
public import Slop.Delegation.IndexedPaths
public import Slop.Delegation.NativeViews

@[expose] public section

/-! State-free twins of the G span's control, pointer and block-domain lemmas (`ControlPool.lean`, `CallHistory.lean`,
    `PointerHistory.lean`, `StateCells.lean`, `BlockFrame.lean`). Those take a Sail `BoundaryInputs` and read the
    initial x10/x11/x12 from the Sail state; here the public facts are the seed tokens (`SeedInputs`) and the x12 seed
    word, with no machine state, so the RV route can use them. Proof bodies follow the Sail ones. -/

namespace Airbender.Blake2G.Proofs
open Trace Trace.Proofs Delegation.Proofs Arithmetic
set_option warningAsError true

/-- Seed-level G call span: the seed facts, modeled tables, the family/active rows, x12's seed word and the call
    count. -/
structure SeedCallInputs [Fact p.Prime] (data : Delegation.MemoryData p) (cells : List Cell) (reduced : Bool) :
    Prop where
  memory : Delegation.SeedProofs.SeedInputs data cells
  tables : data.setup = Delegation.modeledSetup Keccak.Controller.rows
  family : ∀ row ∈ data.rows, row.family = .blakeG
  active : ∀ row ∈ data.rows, row.assignment Variables.execute = 1
  controlStart : ∀ token ∈ data.initial, token.address = (Cell.register 12).addressCode →
    token.word = controlAt reduced 0
  calls : data.rows.length = callCount reduced

/-- Seed-level `ControlPoolInputs`. -/
structure SeedControlPoolInputs [Fact p.Prime] (data : Delegation.MemoryData p) (cells : List Cell)
    (reduced : Bool) : Prop where
  memory : Delegation.SeedProofs.SeedInputs data cells
  tables : data.setup = Delegation.modeledSetup Keccak.Controller.rows
  family : ∀ row ∈ data.rows, row.family = .blakeG
  active : ∀ row ∈ data.rows, row.assignment Variables.execute = 1
  controlCell : Cell.register 12 ∈ cells
  controlStart : ∀ token ∈ data.initial, token.address = (Cell.register 12).addressCode →
    token.word = controlAt reduced 0

private theorem seed_pool_path [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    {data : Delegation.MemoryData p} {cells : List Cell} {reduced : Bool}
    (accepted : Delegation.MemoryAccepted data) (inputs : SeedControlPoolInputs data cells reduced) :
    ∃ source : MemoryToken p, ∃ path : List (MemoryToken p),
      path.length = data.rows.length + 1 ∧ path.head? = some source ∧
      source.word = controlAt reduced 0 ∧
      (path.map fun token => (timeOfPair token.time).value).Pairwise (· < ·) ∧
      (path.zip path.tail).Perm (data.rows.map fun row =>
        (readToken row.assignment importedConstraintsMemoryPorts[8],
          row.writeToken importedConstraintsMemoryPorts[8])) ∧
      ∃ sink ∈ data.terminal, sink.address = (Cell.register 12).addressCode ∧
        path.getLast? = some sink := by
  obtain ⟨source, sourceMember, sourceCode⟩ := seed_cell_source inputs.memory inputs.controlCell
  have initialWord := inputs.controlStart source sourceMember sourceCode
  obtain ⟨sink, sinkMember, sinkAddress, path, head, last, ordered, matching⟩ :=
    (Delegation.SeedProofs.memory_effects hp accepted inputs.memory).paths _ sourceMember
  rw [sourceCode] at matching
  change (path.zip path.tail).Perm
    (data.steps.filter fun edge => edge.1.address = (Cell.register 12).addressCode) at matching
  rw [control_edges inputs.family] at matching
  have length : path.length = data.rows.length + 1 := by
    have equal := matching.length_eq
    have positive : 0 < path.length := by cases path <;> simp_all
    simp only [List.length_zip, List.length_tail, List.length_map] at equal
    omega
  exact ⟨source, path, length, head, initialWord, ordered, matching, sink, sinkMember,
    sinkAddress.trans sourceCode, last⟩

private theorem seed_pool_scheduled_path [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    {data : Delegation.MemoryData p} {cells : List Cell} {reduced : Bool}
    (accepted : Delegation.MemoryAccepted data) (inputs : SeedControlPoolInputs data cells reduced) :
    ∃ path : List (MemoryToken p), path.length = data.rows.length + 1 ∧
      (path.map fun token => (timeOfPair token.time).value).Pairwise (· < ·) ∧
      (path.zip path.tail).Perm (data.rows.map fun row =>
        (readToken row.assignment importedConstraintsMemoryPorts[8],
          row.writeToken importedConstraintsMemoryPorts[8])) ∧
      (∀ (i : Nat) (bound : i < path.length), (path[i]'bound).word = controlAt reduced i) ∧
      ∃ sink ∈ data.terminal, sink.address = (Cell.register 12).addressCode ∧
        path.getLast? = some sink := by
  obtain ⟨source, path, length, head, initialWord, ordered, matching, terminal⟩ :=
    seed_pool_path hp accepted inputs
  have advances : ∀ i, i + 1 < path.length → ∀ edge ∈ path.zip path.tail,
      edge.1.word = controlAt reduced i → edge.2.word = controlAt reduced (i + 1) := by
    intro i bound edge member current
    obtain ⟨row, rowMember, rfl⟩ := List.mem_map.mp (matching.mem_iff.mp member)
    have core : FlatOperation.ConstraintsHoldFlat (Verification.environment row.assignment)
        (importedConstraints (setupTable Control.controllerRows)) := by
      have holds := accepted.constraints row rowMember
      simp only [Delegation.Row.constraints, inputs.family row rowMember,
        inputs.tables, Delegation.modeledSetup] at holds
      exact Verification.holds_of_sublist holds (List.sublist_append_left
        (importedConstraints (setupTable Control.controllerRows)) importedConstraintsTimestampLookups)
    have currentLo : (row.assignment Variables.controlReadLo).val = (controlAt reduced i).lo := by
      simpa [readToken, MemoryToken.word, importedConstraintsMemoryPorts,
        MemoryPort.readCode, WordColumns.code, pairCode, Variables.controlReadLo] using congrArg Word.lo current
    have size : i % callCount reduced < callCount reduced :=
      Nat.mod_lt _ (by cases reduced <;> decide)
    have repeated : controlAt reduced (i % callCount reduced) = controlAt reduced i := by
      simp [controlAt]
    have currentLo' := currentLo
    rw [← repeated] at currentLo'
    have next := forced_control_step (by dsimp [timestampBase] at hp; omega)
      reduced (i % callCount reduced) size core (inputs.active row rowMember) currentLo'
    have following : controlAt reduced (i % callCount reduced + 1) = controlAt reduced (i + 1) := by
      simp [controlAt, Nat.add_mod]
    rw [following] at next
    simpa [Delegation.Row.writeToken, MemoryToken.word, importedConstraintsMemoryPorts,
      MemoryPort.writeCode, WordColumns.code, pairCode,
      Variables.controlWriteLo, Variables.controlWriteHi] using next
  exact ⟨path, length, ordered, matching,
    Delegation.Proofs.indexed_path_words head (controlAt reduced) initialWord advances, terminal⟩

/-- Seed-level `pool_ordered_controls`. -/
theorem seed_pool_ordered_controls [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    {data : Delegation.MemoryData p} {cells : List Cell} {reduced : Bool}
    (accepted : Delegation.MemoryAccepted data) (inputs : SeedControlPoolInputs data cells reduced) :
    ∃ ordered : List (Delegation.Row p), ordered.Perm data.rows ∧
      ordered.Pairwise (fun a b =>
        (timeOfPair (a.writeToken importedConstraintsMemoryPorts[8]).time).value <
        (timeOfPair (b.writeToken importedConstraintsMemoryPorts[8]).time).value) ∧
      (∀ (i : Nat) (bound : i < ordered.length),
        (readToken (ordered[i]'bound).assignment importedConstraintsMemoryPorts[8]).word = controlAt reduced i ∧
        ((ordered[i]'bound).writeToken importedConstraintsMemoryPorts[8]).word = controlAt reduced (i + 1)) ∧
      ∃ sink ∈ data.terminal, sink.address = (Cell.register 12).addressCode ∧
        sink.word = controlAt reduced data.rows.length := by
  obtain ⟨path, length, increasing, matching, sequence, sink, sinkMember, address, last⟩ :=
    seed_pool_scheduled_path hp accepted inputs
  obtain ⟨ordered, permutation, edges, clocks⟩ := Delegation.Proofs.ordered_rows_from_path _ matching increasing
  refine ⟨ordered, permutation, clocks, ?_, sink, sinkMember, address, ?_⟩
  · intro i bound
    have edge := congrArg (fun pairs => pairs[i]?) edges
    have pathBound : i + 1 < path.length := by have := permutation.length_eq; omega
    have edge : (path[i]'(by omega), path[i + 1]'pathBound) =
        (readToken (ordered[i]'bound).assignment importedConstraintsMemoryPorts[8],
          (ordered[i]'bound).writeToken importedConstraintsMemoryPorts[8]) := by
      simpa [List.getElem?_eq_getElem, bound, List.length_zip, List.length_tail,
        show i < path.length - 1 by omega] using edge
    exact ⟨(congrArg (fun edge => edge.1.word) edge).symm.trans (sequence i (by omega)),
      (congrArg (fun edge => edge.2.word) edge).symm.trans (sequence (i + 1) pathBound)⟩
  · have positive : 0 < path.length := by omega
    have endToken : path[path.length - 1]'(by omega) = sink := by
      have endToken := last
      rw [List.getLast?_eq_getElem?] at endToken
      simpa [List.getElem?_eq_getElem, show path.length - 1 < path.length by omega] using endToken
    have value := sequence (path.length - 1) (by omega)
    simpa only [length, Nat.add_sub_cancel] using
      (congrArg MemoryToken.word endToken).symm.trans value

/-- Seed-level `ordered_controls`. -/
theorem seed_ordered_controls [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    {data : Delegation.MemoryData p} {cells : List Cell} {reduced : Bool}
    (accepted : Delegation.MemoryAccepted data) (inputs : SeedCallInputs data cells reduced) :
    ∃ ordered : List (Delegation.Row p), ordered.Perm data.rows ∧
      ordered.Pairwise (fun a b =>
        (timeOfPair (a.writeToken importedConstraintsMemoryPorts[8]).time).value <
        (timeOfPair (b.writeToken importedConstraintsMemoryPorts[8]).time).value) ∧
      (∀ (i : Nat) (bound : i < ordered.length),
        (readToken (ordered[i]'bound).assignment importedConstraintsMemoryPorts[8]).word = controlAt reduced i ∧
        ((ordered[i]'bound).writeToken importedConstraintsMemoryPorts[8]).word = controlAt reduced (i + 1)) ∧
      ∃ sink ∈ data.terminal, sink.address = (Cell.register 12).addressCode ∧
        sink.word = controlAt reduced data.rows.length := by
  have count : 0 < data.rows.length := by
    rw [inputs.calls]
    cases reduced <;> decide
  obtain ⟨first, firstMember⟩ := List.exists_mem_of_ne_nil data.rows
    (by intro empty; simp [empty] at count)
  have portMember : importedConstraintsMemoryPorts[8] ∈ first.ports := by
    simp [Delegation.Row.ports, inputs.family first firstMember, importedConstraintsMemoryPorts]
  have tracked := seed_port_initialized_cell hp accepted inputs.memory firstMember portMember
    (cell := .register 12) (by rfl)
  exact seed_pool_ordered_controls hp accepted
    ⟨inputs.memory, inputs.tables, inputs.family, inputs.active, tracked, inputs.controlStart⟩

private def pointerPort (index : Fin 2) : MemoryPort :=
  if index.val = 0 then importedConstraintsMemoryPorts[0] else importedConstraintsMemoryPorts[5]

private theorem pointer_copies {data : Delegation.MemoryData p}
    (family : ∀ row ∈ data.rows, row.family = .blakeG) (index : Fin 2) :
    ∀ edge ∈ data.steps,
      edge.1.address = (Cell.register (BitVec.ofNat 5 (10 + index.val))).addressCode →
        edge.1.word = edge.2.word := by
  intro edge edgeMember address
  obtain ⟨row, rowMember, edgeMember⟩ := List.mem_flatMap.mp edgeMember
  obtain ⟨port, portMember, rfl⟩ := List.mem_map.mp edgeMember
  cases row with
  | mk kind w =>
    have same := family ⟨kind, w⟩ rowMember
    change kind = .blakeG at same
    subst kind
    simp [Delegation.Row.ports, importedConstraintsMemoryPorts] at portMember
    rcases portMember with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | rfl
      | (fin_cases index <;> simp [readToken, MemoryAddress.code, Cell.addressCode] at address)

private theorem seed_pointer_history [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    {data : Delegation.MemoryData p} {cells : List Cell} {reduced : Bool}
    (accepted : Delegation.MemoryAccepted data) (inputs : SeedCallInputs data cells reduced)
    (index : Fin 2) :
    ∃ source ∈ data.initial, source.address = (Cell.register (BitVec.ofNat 5 (10 + index.val))).addressCode ∧
      (∀ row ∈ data.rows, (readToken row.assignment (pointerPort index)).word = source.word) ∧
      ∃ sink ∈ data.terminal, sink.address = (Cell.register (BitVec.ofNat 5 (10 + index.val))).addressCode ∧
        sink.word = source.word := by
  have nonempty : data.rows ≠ [] := by
    intro empty
    have count := inputs.calls
    cases reduced <;> simp [empty, callCount] at count
  exact seed_port_history hp accepted inputs.memory nonempty
    (fun row member => by
      rw [Delegation.Row.ports, inputs.family row member]
      fin_cases index <;> simp [pointerPort, importedConstraintsMemoryPorts])
    (fun _ _ => by fin_cases index <;> rfl) (pointer_copies inputs.family index)

/-- Seed-level `call_pointers`: the x10/x11 seed tokens fix every row's pointers and the terminal x10/x11. -/
theorem seed_call_pointers [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    {data : Delegation.MemoryData p} {cells : List Cell} {reduced : Bool}
    (accepted : Delegation.MemoryAccepted data) (inputs : SeedCallInputs data cells reduced) :
    ∃ state message : BitVec 32,
      (∃ source ∈ data.initial, source.address = (Cell.register 10).addressCode ∧ source.word = Word.ofBitVec state) ∧
      (∃ source ∈ data.initial, source.address = (Cell.register 11).addressCode ∧
        source.word = Word.ofBitVec message) ∧
      (∀ row ∈ data.rows, Native.statePointer row.assignment = Word.ofBitVec state ∧
        Native.messagePointer row.assignment = Word.ofBitVec message) ∧
      (∃ sink ∈ data.terminal, sink.address = (Cell.register 10).addressCode ∧ sink.word = Word.ofBitVec state) ∧
      (∃ sink ∈ data.terminal, sink.address = (Cell.register 11).addressCode ∧
        sink.word = Word.ofBitVec message) := by
  obtain ⟨stateSource, stateMember, stateCode, stateRows, stateSink, stateSinkMember, stateSinkCode,
    stateSinkWord⟩ := seed_pointer_history hp accepted inputs 0
  obtain ⟨messageSource, messageMember, messageCode, messageRows, messageSink, messageSinkMember,
    messageSinkCode, messageSinkWord⟩ := seed_pointer_history hp accepted inputs 1
  have stateBound := inputs.memory.words stateSource stateMember
  have messageBound := inputs.memory.words messageSource messageMember
  refine ⟨stateSource.word.toBitVec, messageSource.word.toBitVec,
    ⟨stateSource, stateMember, stateCode, (word_of_toBitVec stateBound).symm⟩,
    ⟨messageSource, messageMember, messageCode, (word_of_toBitVec messageBound).symm⟩, ?_,
    ⟨stateSink, stateSinkMember, stateSinkCode, stateSinkWord.trans (word_of_toBitVec stateBound).symm⟩,
    ⟨messageSink, messageSinkMember, messageSinkCode,
      messageSinkWord.trans (word_of_toBitVec messageBound).symm⟩⟩
  intro row member
  rw [word_of_toBitVec stateBound, word_of_toBitVec messageBound]
  constructor
  · simpa [Native.statePointer, Native.messagePointer, Delegation.Row.readWord, Delegation.Row.ports, pointerPort]
      using stateRows row member
  · simpa [Native.statePointer, Native.messagePointer, Delegation.Row.readWord, Delegation.Row.ports, pointerPort]
      using messageRows row member

theorem seed_initialized_indirect_cell [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    {data : Delegation.MemoryData p} (accepted : Delegation.MemoryAccepted data)
    {cells : List Cell} (inputs : Delegation.SeedProofs.SeedInputs data cells)
    {row : Delegation.Row p} (member : row ∈ data.rows) {port : MemoryPort} (present : port ∈ row.ports)
    {indirect : Verification.IndirectPort} (shape : port.address = .indirect indirect) :
    Cell.ram (indirect.address row.assignment) ∈ cells := by
  have edgeMember : (readToken row.assignment port, row.writeToken port) ∈ data.steps := by
    apply List.mem_flatMap.mpr
    refine ⟨row, member, ?_⟩
    apply List.mem_map.mpr
    exact ⟨port, by simpa only [Array.mem_toList_iff] using present, rfl⟩
  obtain ⟨cell, tracked, code⟩ := seed_initialized_cell hp accepted inputs edgeMember
  change cell.addressCode = port.address.code row.assignment at code
  rw [shape] at code
  have same := indirect_cell code
  exact same ▸ tracked

private theorem first_round_coverage (reduced block : Bool) (word : Fin 16) :
    ∃ call : Fin 8, ∃ port : Fin 6,
      if block then port.val < 4 ∧
        (Control.step (scheduledController reduced call.val (by have := call.isLt; cases reduced <;> simp only [callCount, Bool.false_eq_true, ↓reduceIte] <;> omega))).stateOffsets[Fin.ofNat 4 port.val] = word.val
      else 4 ≤ port.val ∧
        (Control.step (scheduledController reduced call.val (by have := call.isLt; cases reduced <;> simp only [callCount, Bool.false_eq_true, ↓reduceIte] <;> omega))).messageOffsets[Fin.ofNat 2 (port.val - 4)] = word.val := by
  have finite : ∀ reduced block : Bool, ∀ word : Fin 16, ∃ call : Fin 8, ∃ port : Fin 6,
      if block then port.val < 4 ∧
        (Control.step (scheduledController reduced call.val (by have := call.isLt; cases reduced <;> simp only [callCount, Bool.false_eq_true, ↓reduceIte] <;> omega))).stateOffsets[Fin.ofNat 4 port.val] = word.val
      else 4 ≤ port.val ∧
        (Control.step (scheduledController reduced call.val (by have := call.isLt; cases reduced <;> simp only [callCount, Bool.false_eq_true, ↓reduceIte] <;> omega))).messageOffsets[Fin.ofNat 2 (port.val - 4)] = word.val := by decide +kernel
  exact finite reduced block word

private theorem operation_inputs {data : Delegation.MemoryData p} {cells : List Cell} {reduced : Bool}
    [Fact p.Prime] (inputs : SeedCallInputs data cells reduced) :
    (∀ row ∈ data.rows, row.family = .blakeRound → ∃ round, Blake2Round.Memory.RoundMask row.assignment round) ∧
    (∀ row ∈ data.rows, row.family = .keccak → row.assignment Keccak.Variables.execute = 1) := by
  constructor
  all_goals intro row member other; have := inputs.family row member; simp_all

/-- Seed-level `call_block_cells`: every word of both blocks is a tracked RAM cell. -/
theorem seed_call_block_cells [Fact p.Prime] (hp : 8388608 ≤ p)
    (inverse : 64 * (-31457280 : ZMod p) = 1)
    {data : Delegation.MemoryData p} {cells : List Cell} {reduced : Bool}
    (accepted : Delegation.MemoryAccepted data) (inputs : SeedCallInputs data cells reduced)
    {statePointer messagePointer : BitVec 32}
    (pointers : ∀ row ∈ data.rows, Native.statePointer row.assignment = Word.ofBitVec statePointer ∧
      Native.messagePointer row.assignment = Word.ofBitVec messagePointer) :
    ∀ block : Bool, ∀ word : Fin 16,
      Cell.ram ((if block then statePointer else messagePointer) + BitVec.ofNat 32 (4 * word.val)) ∈ cells := by
  have clockBound : 2 * timestampBase + 4 < p := by norm_num [timestampBase]; omega
  obtain ⟨ordered, permutation, _, controls, _⟩ := seed_ordered_controls clockBound accepted inputs
  have bounds := Delegation.SeedProofs.operation_word_bounds hp inverse accepted inputs.memory inputs.tables
    (operation_inputs inputs).1 (operation_inputs inputs).2
  intro block word
  obtain ⟨call, index, coverage⟩ := first_round_coverage reduced block word
  have callBound : call.val < callCount reduced := by have := call.isLt; cases reduced <;> simp only [callCount, Bool.false_eq_true, ↓reduceIte] <;> omega
  have rowBound : call.val < ordered.length := by rw [permutation.length_eq, inputs.calls]; exact callBound
  let row := ordered[call.val]'rowBound
  have member : row ∈ data.rows := permutation.mem_iff.mp (List.getElem_mem _)
  have native : row = ⟨.blakeG, row.assignment⟩ := by
    have same : row = ⟨row.family, row.assignment⟩ := by rfl
    simpa only [inputs.family row member] using same
  have core : FlatOperation.ConstraintsHoldFlat (Verification.environment row.assignment)
      (importedConstraints (setupTable Control.controllerRows)) := by
    have h := accepted.constraints row member
    simp only [Delegation.Row.constraints, inputs.family row member, inputs.tables, Delegation.modeledSetup] at h
    exact Verification.holds_of_sublist h (List.sublist_append_left _ importedConstraintsTimestampLookups)
  have control : (row.assignment Variables.controlReadLo).val = (controlAt reduced call.val).lo := by
    have value := congrArg Word.lo (controls call.val rowBound).1
    simpa [row, readToken, MemoryToken.word, importedConstraintsMemoryPorts,
      MemoryPort.readCode, WordColumns.code, pairCode, Variables.controlReadLo] using value
  have controlBound : (row.assignment Variables.controlReadLo).val < 256 := by
    rw [control]
    exact (scheduledController reduced call.val callBound).register.isLt
  -- the serialized inverse fixes p = BabyBear, above Blake2G's 2^25 bound
  have field : 33554432 ≤ p := by
    rw [serialized_field inverse]; unfold babyBearModulus; norm_num
  have addresses := native_addresses (by omega) inverse core (inputs.active row member) controlBound
    (by simpa only [← native] using bounds.reads row member)
  have mapped : addressInput row.assignment controlBound =
      ⟨scheduledController reduced call.val callBound, Word.ofBitVec statePointer, Word.ofBitVec messagePointer⟩ := by
    dsimp only [addressInput]
    rw [(pointers row member).1, (pointers row member).2]
    congr 2
    exact Fin.ext control
  rw [mapped] at addresses
  have address := congrArg (fun values : Vector (BitVec 32) 6 => values[index]) addresses
  simp only [Fin.getElem_fin, Vector.getElem_map] at address
  change importedConstraintsIndirectPorts[index].address row.assignment = _ at address
  have present : wordPort index ∈ row.ports := by
    rw [Delegation.Row.ports, inputs.family row member]
    exact Array.getElem_mem (wordIndex index).isLt
  have tracked := seed_initialized_indirect_cell clockBound accepted inputs.memory member present
    (word_port_address index)
  rw [address] at tracked
  cases block
  · simp only [Bool.false_eq_true, ↓reduceIte] at coverage ⊢
    obtain ⟨selected, offset⟩ := coverage
    fin_cases index
    all_goals norm_num only [Fin.val_ofNat, Nat.reduceSub, Nat.reduceLT,
      Fin.getElem_fin] at selected
    all_goals norm_num only [Fin.val_ofNat, Nat.reduceSub, Fin.getElem_fin] at offset
    all_goals simpa only [Addresses.expected, Word.ofBitVec_roundtrip, Fin.getElem_fin,
      Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
      List.getElem_cons_succ, offset] using tracked
  · simp only [↓reduceIte] at coverage ⊢
    obtain ⟨selected, offset⟩ := coverage
    fin_cases index
    all_goals norm_num only [Fin.val_ofNat, Nat.reduceSub, Nat.reduceLT,
      Fin.getElem_fin] at selected
    all_goals norm_num only [Fin.val_ofNat, Nat.reduceSub, Fin.getElem_fin] at offset
    all_goals simpa only [Addresses.expected, Word.ofBitVec_roundtrip, Fin.getElem_fin,
      Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
      List.getElem_cons_succ, offset] using tracked

private theorem seed_port_code [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    {data : Delegation.MemoryData p} {cells : List Cell}
    (accepted : Delegation.MemoryAccepted data) (inputs : Delegation.SeedProofs.SeedInputs data cells)
    {row : Delegation.Row p} (member : row ∈ data.rows) (family : row.family = .blakeG)
    (index : Fin 6) :
    (wordPort index).address.code row.assignment =
      (Cell.ram (importedConstraintsIndirectPorts[index].address row.assignment)).addressCode := by
  have present : wordPort index ∈ row.ports := by
    rw [Delegation.Row.ports, family]
    exact Array.getElem_mem (wordIndex index).isLt
  have step : (readToken row.assignment (wordPort index), row.writeToken (wordPort index)) ∈ data.steps := by
    apply List.mem_flatMap.mpr
    refine ⟨row, member, List.mem_map.mpr ⟨_, ?_, rfl⟩⟩
    simpa only [Array.mem_toList_iff] using present
  obtain ⟨cell, _, code⟩ := seed_initialized_cell hp accepted inputs step
  change cell.addressCode = (wordPort index).address.code row.assignment at code
  rw [word_port_address] at code
  rw [indirect_cell code] at code
  simpa only [word_port_address] using code.symm

/-- Seed-level `call_block_domain`: the x10/x11 seed pointers are 64-aligned, different, and both blocks are tracked. -/
theorem seed_call_block_domain [Fact p.Prime] (hp : 8388608 ≤ p)
    (inverse : 64 * (-31457280 : ZMod p) = 1)
    {data : Delegation.MemoryData p} {cells : List Cell} {reduced : Bool}
    (accepted : Delegation.MemoryAccepted data) (inputs : SeedCallInputs data cells reduced) :
    ∃ statePointer messagePointer : BitVec 32,
      (∃ source ∈ data.initial, source.address = (Cell.register 10).addressCode ∧
        source.word = Word.ofBitVec statePointer) ∧
      (∃ source ∈ data.initial, source.address = (Cell.register 11).addressCode ∧
        source.word = Word.ofBitVec messagePointer) ∧
      (∀ row ∈ data.rows, Native.statePointer row.assignment = Word.ofBitVec statePointer ∧
        Native.messagePointer row.assignment = Word.ofBitVec messagePointer) ∧
      statePointer.toNat % 64 = 0 ∧ messagePointer.toNat % 64 = 0 ∧
      statePointer ≠ messagePointer ∧
      ∀ block : Bool, ∀ word : Fin 16,
        Cell.ram ((if block then statePointer else messagePointer) + BitVec.ofNat 32 (4 * word.val)) ∈ cells := by
  -- the serialized inverse fixes p = BabyBear, above Blake2G's 2^25 bound
  have field : 33554432 ≤ p := by
    rw [serialized_field inverse]; unfold babyBearModulus; norm_num
  have clockBound : 2 * timestampBase + 4 < p := by norm_num [timestampBase]; omega
  obtain ⟨statePointer, messagePointer, stateSource, messageSource, pointers, _, _⟩ :=
    seed_call_pointers clockBound accepted inputs
  have tracked := seed_call_block_cells hp inverse accepted inputs pointers
  obtain ⟨ordered, permutation, _, controls, _⟩ := seed_ordered_controls clockBound accepted inputs
  have firstBound : 0 < ordered.length := by
    rw [permutation.length_eq, inputs.calls]
    cases reduced <;> decide
  let row := ordered[0]'firstBound
  have member : row ∈ data.rows := permutation.mem_iff.mp (List.getElem_mem _)
  have family := inputs.family row member
  have core : FlatOperation.ConstraintsHoldFlat (Verification.environment row.assignment)
      (importedConstraints (setupTable Control.controllerRows)) := by
    have h := accepted.constraints row member
    simp only [Delegation.Row.constraints, family, inputs.tables, Delegation.modeledSetup] at h
    exact Verification.holds_of_sublist h (List.sublist_append_left _ importedConstraintsTimestampLookups)
  have alignment := pointer_alignment (by omega) inverse core
  have pointer := pointers row member
  have stateLow := congrArg Word.lo pointer.1
  have messageLow := congrArg Word.lo pointer.2
  simp [Native.statePointer, Delegation.Row.readWord, Delegation.Row.ports, readToken,
    MemoryToken.word, MemoryPort.readCode, WordColumns.code, WordColumns.evaluate,
    importedConstraintsMemoryPorts, Word.ofBitVec, limbBase] at stateLow
  simp [Native.messagePointer, Delegation.Row.readWord, Delegation.Row.ports, readToken,
    MemoryToken.word, MemoryPort.readCode, WordColumns.code, WordColumns.evaluate,
    importedConstraintsMemoryPorts, Word.ofBitVec, limbBase] at messageLow
  have stateAligned : statePointer.toNat % 64 = 0 := by
    rw [stateLow, Nat.mod_mod_of_dvd _ (by decide : 64 ∣ 65536)] at alignment
    exact alignment.1
  have messageAligned : messagePointer.toNat % 64 = 0 := by
    rw [messageLow, Nat.mod_mod_of_dvd _ (by decide : 64 ∣ 65536)] at alignment
    exact alignment.2
  have bounds := Delegation.SeedProofs.operation_word_bounds hp inverse accepted inputs.memory inputs.tables
    (operation_inputs inputs).1 (operation_inputs inputs).2
  have native : row = ⟨.blakeG, row.assignment⟩ := by
    have same : row = ⟨row.family, row.assignment⟩ := by rfl
    simpa only [family] using same
  have control : (row.assignment Variables.controlReadLo).val = (controlAt reduced 0).lo := by
    have value := congrArg Word.lo (controls 0 firstBound).1
    simpa [row, readToken, MemoryToken.word, importedConstraintsMemoryPorts,
      MemoryPort.readCode, WordColumns.code, pairCode, Variables.controlReadLo] using value
  have controlBound : (row.assignment Variables.controlReadLo).val < 256 := by
    rw [control]
    cases reduced <;> decide
  have addresses := native_addresses (by omega) inverse core (inputs.active row member) controlBound
    (by simpa only [← native] using bounds.reads row member)
  have mapped : addressInput row.assignment controlBound =
      ⟨scheduledController reduced 0 (by cases reduced <;> decide),
        Word.ofBitVec statePointer, Word.ofBitVec messagePointer⟩ := by
    dsimp only [addressInput]
    rw [pointer.1, pointer.2]
    congr 2
    exact Fin.ext control
  rw [mapped] at addresses
  have stateAddress := congrArg (fun values : Vector (BitVec 32) 6 => values[0]) addresses
  have messageAddress := congrArg (fun values : Vector (BitVec 32) 6 => values[4]) addresses
  have stateNative : importedConstraintsIndirectPorts[0].address row.assignment = statePointer := by
    cases reduced <;> simpa [Addresses.expected, scheduledController, controllerAt, controlAt,
      Control.step, Control.stateLanes, Control.messageSchedule, Control.controllerRows, Word.ofBitVec_roundtrip] using stateAddress
  have messageNative : importedConstraintsIndirectPorts[4].address row.assignment = messagePointer := by
    cases reduced <;> simpa [Addresses.expected, scheduledController, controllerAt, controlAt,
      Control.step, Control.stateLanes, Control.messageSchedule, Control.controllerRows, Word.ofBitVec_roundtrip] using messageAddress
  have separate : statePointer ≠ messagePointer := by
    intro same
    have one := seed_port_code clockBound accepted inputs.memory member family 0
    have six := seed_port_code clockBound accepted inputs.memory member family 4
    change (wordPort 0).address.code row.assignment =
      (Cell.ram (importedConstraintsIndirectPorts[0].address row.assignment)).addressCode at one
    change (wordPort 4).address.code row.assignment =
      (Cell.ram (importedConstraintsIndirectPorts[4].address row.assignment)).addressCode at six
    rw [stateNative] at one
    rw [messageNative, ← same] at six
    have equal := one.trans six.symm
    have unique := seed_row_addresses_distinct clockBound accepted inputs.memory member
    have samePorts : (row.memorySteps.map fun edge => edge.1.address)[1]'(by
        simp [Delegation.Row.memorySteps, Delegation.Row.ports, family, importedConstraintsMemoryPorts]) =
      (row.memorySteps.map fun edge => edge.1.address)[6]'(by
        simp [Delegation.Row.memorySteps, Delegation.Row.ports, family, importedConstraintsMemoryPorts]) := by
      simpa [Delegation.Row.memorySteps, Delegation.Row.ports, family, importedConstraintsMemoryPorts,
        wordPort, wordIndex, readToken] using equal
    have impossible := unique.getElem_inj_iff.mp samePorts
    omega
  exact ⟨statePointer, messagePointer, stateSource, messageSource, pointers, stateAligned, messageAligned,
    separate, tracked⟩

end Airbender.Blake2G.Proofs
