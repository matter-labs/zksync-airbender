module
public import Slop.Blake2Round.ControlPool
public import Slop.Blake2Round.NativeExecution
public import Slop.Delegation.RVCallHistory
public import Slop.Delegation.SeedOperations

@[expose] public section

/-! State-free twins of the extended-BLAKE span's control and pointer lemmas (`ControlPool.lean`, `CallHistory.lean`,
    `PointerHistory.lean`): those take a Sail `BoundaryInputs` and read x10/x11/x12 from the Sail state; here the
    public facts are the seed tokens (`SeedInputs`) and x12's seed word, so the RV route can use them. The control
    path lemmas (`ControlMatchingInputs`) are already state-free; the private ones are copied. -/

namespace Airbender.Blake2Round.Proofs
open Trace Trace.Proofs Delegation.Proofs Arithmetic
set_option warningAsError true
set_option maxRecDepth 16384

/-- Seed-level extended-BLAKE call span. -/
structure SeedCallInputs [Fact p.Prime] (data : Delegation.MemoryData p) (cells : List Cell) (flags : Fin 8) :
    Prop where
  memory : Delegation.SeedProofs.SeedInputs data cells
  tables : data.setup = Delegation.modeledSetup Keccak.Controller.rows
  family : ∀ row ∈ data.rows, row.family = .blakeRound
  controlStart : ∀ token ∈ data.initial, token.address = (Cell.register 12).addressCode →
    token.word = controlAt flags 0
  roundsBound : data.rows.length ≤ 10
  nonempty : data.rows ≠ []

theorem SeedCallInputs.toMatching [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    {data : Delegation.MemoryData p} {cells : List Cell} {flags : Fin 8}
    (accepted : Delegation.MemoryAccepted data) (inputs : SeedCallInputs data cells flags) :
    ControlMatchingInputs data flags := by
  obtain ⟨first, firstMember⟩ := List.exists_mem_of_ne_nil _ inputs.nonempty
  have portMember : importedConstraintsMemoryPorts[42] ∈ first.ports := by
    simp [Delegation.Row.ports, inputs.family first firstMember, importedConstraintsMemoryPorts]
  have tracked := seed_port_initialized_cell hp accepted inputs.memory firstMember portMember
    (cell := .register 12) (by rfl)
  obtain ⟨source, sourceMember, sourceCode⟩ := seed_cell_source inputs.memory tracked
  exact ⟨⟨accepted.matching, Delegation.Proofs.preserved_addresses,
    Delegation.SeedProofs.memory_order hp accepted inputs.memory⟩,
    inputs.memory.addresses.nodup_iff.mpr inputs.memory.distinct, inputs.tables,
    inputs.family, ⟨source, sourceMember, sourceCode, inputs.controlStart source sourceMember sourceCode⟩,
    inputs.roundsBound⟩

private theorem control_next (flags : Fin 8) {i : Nat} (bound : i < 10) :
    Control.next (controlAt flags i) = controlAt flags (i + 1) := by
  have flagBound := flags.isLt
  interval_cases i
  all_goals simp [Control.next, controlAt]
  all_goals omega

private theorem control_iterate (flags : Fin 8) {i : Nat} (bound : i ≤ 10) :
    Control.next^[i] (controlAt flags 0) = controlAt flags i := by
  induction i with
  | zero => simp
  | succ i ih => rw [Function.iterate_succ_apply', ih (by omega), control_next flags (by omega)]

private theorem control_edges {data : Delegation.MemoryData p}
    (family : ∀ row ∈ data.rows, row.family = .blakeRound) :
    (data.steps.filter fun edge => edge.1.address = (Cell.register 12).addressCode) =
      data.rows.map (fun row => (readToken row.assignment importedConstraintsMemoryPorts[42],
        row.writeToken importedConstraintsMemoryPorts[42])) := by
  simp only [Delegation.MemoryData.steps, List.filter_flatMap, List.map_eq_flatMap]
  change (data.rows.map _).flatten = (data.rows.map _).flatten
  apply congrArg List.flatten
  apply List.map_congr_left
  intro row member
  cases row with
  | mk kind w =>
    have same := family ⟨kind, w⟩ member
    change kind = .blakeRound at same
    subst kind
    simp [Delegation.Row.memorySteps, Delegation.Row.ports, importedConstraintsMemoryPorts,
      readToken, MemoryAddress.code, Cell.addressCode, pairCode, Nat.pair_eq_pair]

private theorem call_path [Fact p.Prime] {data : Delegation.MemoryData p} {flags : Fin 8}
    (inputs : ControlMatchingInputs data flags) :
    ∃ source : MemoryToken p, ∃ path : List (MemoryToken p),
      path.length = data.rows.length + 1 ∧ path.head? = some source ∧
      source.word = controlAt flags 0 ∧
      (path.map fun token => (timeOfPair token.time).value).Pairwise (· < ·) ∧
      (path.zip path.tail).Perm (data.rows.map fun row =>
        (readToken row.assignment importedConstraintsMemoryPorts[42],
          row.writeToken importedConstraintsMemoryPorts[42])) ∧
      ∃ sink ∈ data.terminal, sink.address = (Cell.register 12).addressCode ∧
        path.getLast? = some sink := by
  obtain ⟨source, sourceMember, sourceCode, initialWord⟩ := inputs.source
  obtain ⟨sink, sinkMember, sinkAddress, path, head, last, _, matching⟩ :=
    Trace.Proofs.keyed_paths_finite MemoryToken.address (fun token => (timeOfPair token.time).value)
      inputs.facts.matching inputs.facts.addresses inputs.distinct inputs.facts.order source sourceMember
  have ordered := Trace.Proofs.rank_ordered (fun token : MemoryToken p => (timeOfPair token.time).value) path
    (fun edge member => inputs.facts.order edge (List.mem_of_mem_filter (matching.mem_iff.mp member)))
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

private theorem scheduled_path [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    {data : Delegation.MemoryData p} {flags : Fin 8}
    (accepted : Delegation.MemoryAccepted data) (inputs : ControlMatchingInputs data flags) :
    ∃ path : List (MemoryToken p), path.length = data.rows.length + 1 ∧
      (path.map fun token => (timeOfPair token.time).value).Pairwise (· < ·) ∧
      (path.zip path.tail).Perm (data.rows.map fun row =>
        (readToken row.assignment importedConstraintsMemoryPorts[42],
          row.writeToken importedConstraintsMemoryPorts[42])) ∧
      (∀ (i : Nat) (bound : i < path.length), (path[i]'bound).word = controlAt flags i) ∧
      ∃ sink ∈ data.terminal, sink.address = (Cell.register 12).addressCode ∧
        path.getLast? = some sink := by
  obtain ⟨source, path, length, head, initialWord, ordered, matching, terminal⟩ := call_path inputs
  have core (row : Delegation.Row p) (member : row ∈ data.rows) :
      FlatOperation.ConstraintsHoldFlat (Verification.environment row.assignment)
        (importedConstraints setupTable) := by
    have holds := accepted.constraints row member
    have family := inputs.family row member
    simp only [Delegation.Row.constraints, family, inputs.tables, Delegation.modeledSetup] at holds
    exact Verification.holds_of_sublist holds (List.sublist_append_left
      (importedConstraints setupTable) importedConstraintsTimestampLookups)
  have advances : ∀ edge ∈ path.zip path.tail, edge.2.word = Control.next edge.1.word := by
    intro edge member
    obtain ⟨row, rowMember, rfl⟩ := List.mem_map.mp (matching.mem_iff.mp member)
    have result := Control.Proofs.soundness (by dsimp [timestampBase] at hp; omega)
      setupTable _ _ row.assignment ⟨core row rowMember, ⟨rfl, rfl⟩⟩
    simpa [Control.spec, readToken, MemoryToken.word, Delegation.Row.writeToken,
      importedConstraintsMemoryPorts, MemoryPort.readCode, MemoryPort.writeCode,
      WordColumns.code, pairCode, Control.Mapping, Variables.controlReadLo, Variables.controlReadHi,
      Variables.controlWriteLo, Variables.controlWriteHi] using result.2
  have sequence := Delegation.Proofs.path_word_sequence head Control.next advances
  refine ⟨path, length, ordered, matching, ?_, terminal⟩
  intro i bound
  have count := inputs.roundsBound
  rw [sequence i bound, initialWord, control_iterate flags (by omega)]

/-- State-free `pool_ordered_controls`. -/
theorem matching_ordered_controls [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    {data : Delegation.MemoryData p} {flags : Fin 8}
    (accepted : Delegation.MemoryAccepted data) (inputs : ControlMatchingInputs data flags) :
    ∃ ordered : List (Delegation.Row p), ordered.Perm data.rows ∧
      ordered.Pairwise (fun a b =>
        (timeOfPair (a.writeToken importedConstraintsMemoryPorts[42]).time).value <
        (timeOfPair (b.writeToken importedConstraintsMemoryPorts[42]).time).value) ∧
      (∀ (i : Nat) (bound : i < ordered.length),
        (readToken (ordered[i]'bound).assignment importedConstraintsMemoryPorts[42]).word = controlAt flags i ∧
        ((ordered[i]'bound).writeToken importedConstraintsMemoryPorts[42]).word = controlAt flags (i + 1)) ∧
      ∃ sink ∈ data.terminal, sink.address = (Cell.register 12).addressCode ∧
        sink.word = controlAt flags data.rows.length := by
  obtain ⟨path, length, increasing, matching, sequence, sink, sinkMember, address, last⟩ :=
    scheduled_path hp accepted inputs
  obtain ⟨ordered, permutation, edges, clocks⟩ := Delegation.Proofs.ordered_rows_from_path _ matching increasing
  refine ⟨ordered, permutation, clocks, ?_, sink, sinkMember, address, ?_⟩
  · intro i bound
    have edge := congrArg (fun pairs => pairs[i]?) edges
    have pathBound : i + 1 < path.length := by have := permutation.length_eq; omega
    have edge : (path[i]'(by omega), path[i + 1]'pathBound) =
        (readToken (ordered[i]'bound).assignment importedConstraintsMemoryPorts[42],
          (ordered[i]'bound).writeToken importedConstraintsMemoryPorts[42]) := by
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

/-- State-free `pool_modes`. -/
theorem matching_modes [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    {data : Delegation.MemoryData p} {flags : Fin 8}
    (accepted : Delegation.MemoryAccepted data) (inputs : ControlMatchingInputs data flags) :
    CallModes data flags := by
  intro row member round
  obtain ⟨actualRound, _, read⟩ := matching_rounds hp accepted inputs row member
  have core : FlatOperation.ConstraintsHoldFlat (Verification.environment row.assignment)
      (importedConstraints setupTable) := by
    have holds := accepted.constraints row member
    simp only [Delegation.Row.constraints, inputs.family row member,
      inputs.tables, Delegation.modeledSetup] at holds
    exact Verification.holds_of_sublist holds (List.sublist_append_left
      (importedConstraints setupTable) importedConstraintsTimestampLookups)
  have flags := control_flags (by dsimp [timestampBase] at hp; omega) core flags actualRound read
  have : Fact (1 < p) := ⟨(Fact.out : p.Prime).one_lt⟩
  have one (column : Nat) : decide (row.assignment column = 1) = decide ((row.assignment column).val = 1) := by
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    constructor
    · intro equal
      rw [equal, ZMod.val_one]
    · intro equal
      apply ZMod.val_injective
      rw [equal, ZMod.val_one]
  change decide (row.assignment 139 = 1) = _ ∧
    decide (row.assignment 140 = 1) = _ ∧ decide (row.assignment 141 = 1) = _
  rw [one 139, one 140, one 141, flags.1, flags.2.1, flags.2.2]
  exact ⟨rfl, rfl, rfl⟩

private def pointerPort (index : Fin 2) : MemoryPort :=
  if index.val = 0 then importedConstraintsMemoryPorts[0] else importedConstraintsMemoryPorts[25]

private theorem pointer_copies {data : Delegation.MemoryData p}
    (family : ∀ row ∈ data.rows, row.family = .blakeRound) (index : Fin 2) :
    ∀ edge ∈ data.steps,
      edge.1.address = (Cell.register (BitVec.ofNat 5 (10 + index.val))).addressCode →
        edge.1.word = edge.2.word := by
  intro edge edgeMember address
  obtain ⟨row, rowMember, edgeMember⟩ := List.mem_flatMap.mp edgeMember
  obtain ⟨port, portMember, rfl⟩ := List.mem_map.mp edgeMember
  cases row with
  | mk kind w =>
    have same := family ⟨kind, w⟩ rowMember
    change kind = .blakeRound at same
    subst kind
    simp [Delegation.Row.ports, importedConstraintsMemoryPorts] at portMember
    rcases portMember with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl
    all_goals first
      | rfl
      | (fin_cases index <;> simp [readToken, MemoryAddress.code, Cell.addressCode] at address)

private theorem seed_pointer_history [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    {data : Delegation.MemoryData p} {cells : List Cell} {flags : Fin 8}
    (accepted : Delegation.MemoryAccepted data) (inputs : SeedCallInputs data cells flags)
    (index : Fin 2) :
    ∃ source ∈ data.initial, source.address = (Cell.register (BitVec.ofNat 5 (10 + index.val))).addressCode ∧
      (∀ row ∈ data.rows, (readToken row.assignment (pointerPort index)).word = source.word) ∧
      ∃ sink ∈ data.terminal, sink.address = (Cell.register (BitVec.ofNat 5 (10 + index.val))).addressCode ∧
        sink.word = source.word :=
  seed_port_history hp accepted inputs.memory inputs.nonempty
    (fun row member => by
      rw [Delegation.Row.ports, inputs.family row member]
      fin_cases index <;> simp [pointerPort, importedConstraintsMemoryPorts])
    (fun _ _ => by fin_cases index <;> rfl) (pointer_copies inputs.family index)

/-- Seed-level `call_pointers`. -/
theorem seed_call_pointers [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    {data : Delegation.MemoryData p} {cells : List Cell} {flags : Fin 8}
    (accepted : Delegation.MemoryAccepted data) (inputs : SeedCallInputs data cells flags) :
    ∃ state message : BitVec 32,
      (∃ source ∈ data.initial, source.address = (Cell.register 10).addressCode ∧ source.word = Word.ofBitVec state) ∧
      (∃ source ∈ data.initial, source.address = (Cell.register 11).addressCode ∧
        source.word = Word.ofBitVec message) ∧
      ∀ row ∈ data.rows, ∀ round,
        (Native.input round row.assignment).statePointer = Word.ofBitVec state ∧
        (Native.input round row.assignment).messagePointer = Word.ofBitVec message := by
  obtain ⟨stateSource, stateMember, stateCode, stateRows, -⟩ := seed_pointer_history hp accepted inputs 0
  obtain ⟨messageSource, messageMember, messageCode, messageRows, -⟩ := seed_pointer_history hp accepted inputs 1
  have stateBound := inputs.memory.words stateSource stateMember
  have messageBound := inputs.memory.words messageSource messageMember
  refine ⟨stateSource.word.toBitVec, messageSource.word.toBitVec,
    ⟨stateSource, stateMember, stateCode, (word_of_toBitVec stateBound).symm⟩,
    ⟨messageSource, messageMember, messageCode, (word_of_toBitVec messageBound).symm⟩, ?_⟩
  intro row member round
  rw [word_of_toBitVec stateBound, word_of_toBitVec messageBound]
  constructor
  · simpa [Native.input, Delegation.Row.readWord, Delegation.Row.ports, pointerPort] using stateRows row member
  · simpa [Native.input, Delegation.Row.readWord, Delegation.Row.ports, pointerPort] using messageRows row member

end Airbender.Blake2Round.Proofs
