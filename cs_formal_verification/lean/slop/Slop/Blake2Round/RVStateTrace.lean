module
public import Slop.Blake2Round.SeedCall
public import Slop.Blake2Round.CallGroups
public import Slop.Delegation.RVExecution
public import Human.Trace.Workers.Blake2Round.RVCall
public import Slop.Defs.Circuits.Blake2Round.Artifact
public import Slop.Defs.Helpers.Memory.Ports
public import Slop.Defs.Trace.Workers.Blake2Round.Call

@[expose] public section

/-! RV twins of `CallGroups.call_scheduled_history` and `StateTrace.call_state_trace` for the extended-BLAKE span: the
    RV history grouped by call in control order, the per-call RV states, each call's round (its exclusive mask, from
    the x12 schedule), its row reference and port observations. RAM cells include the shadow RAM below `ROM_END`. -/

namespace Airbender.Blake2Round.Proofs
open Trace Trace.Proofs Delegation.Proofs Arithmetic
set_option warningAsError true
set_option maxRecDepth 16384

/-- RV sibling of `BoundaryCallInputs`. -/
structure RVBoundaryCallInputs [Fact p.Prime] (data : Delegation.MemoryData p)
    (initial : RV.State) (cells : List Cell) (flags : Fin 8) : Prop where
  memory : Delegation.Proofs.RVBoundaryInputs data initial cells
  tables : data.setup = Delegation.modeledSetup Keccak.Controller.rows
  family : ∀ row ∈ data.rows, row.family = .blakeRound
  controlStart : (Cell.register 12).readRV initial = some (BitVec.ofNat 32 ((8 + flags.val) * 65536))
  calls : data.rows.length = if flags.val % 2 = 1 then 7 else 10

theorem RVBoundaryCallInputs.toSeed [Fact p.Prime] {data : Delegation.MemoryData p} {initial : RV.State}
    {cells : List Cell} {flags : Fin 8} (inputs : RVBoundaryCallInputs data initial cells flags) :
    SeedCallInputs data cells flags := by
  have count : 0 < data.rows.length ∧ data.rows.length ≤ 10 := by
    rw [inputs.calls]; split_ifs <;> decide
  refine ⟨inputs.memory.toSeed, inputs.tables, inputs.family, ?_, count.2,
    fun empty => by simp [empty] at count⟩
  intro token present code
  rw [rv_seed_word inputs.memory present code inputs.controlStart]
  have flagBound := flags.isLt
  simp [Word.ofBitVec, controlAt, limbBase, BitVec.toNat_ofNat]
  omega

theorem rv_call_scheduled_history [Fact p.Prime] (hp : 8388608 ≤ p)
    (inverse : 64 * (-31457280 : ZMod p) = 1)
    {data : Delegation.MemoryData p} {initial : RV.State} {cells : List Cell} {flags : Fin 8}
    (accepted : Delegation.MemoryAccepted data) (inputs : RVBoundaryCallInputs data initial cells flags)
    (aligned : ∀ cell ∈ cells, cell.Aligned) :
    ∃ (ascending : List (Delegation.Row p)) (after : RV.State), ascending.Perm data.rows ∧
      ascending.Pairwise (fun a b =>
        (timeOfPair (a.writeToken importedConstraintsMemoryPorts[42]).time).value <
        (timeOfPair (b.writeToken importedConstraintsMemoryPorts[42]).time).value) ∧
      (∀ (i : Nat) (bound : i < ascending.length),
        (readToken (ascending[i]'bound).assignment importedConstraintsMemoryPorts[42]).word = controlAt flags i ∧
        ((ascending[i]'bound).writeToken importedConstraintsMemoryPorts[42]).word = controlAt flags (i + 1)) ∧
      GroupedRVHistory cells (fun row => row.memorySteps.map transferEvent) ascending.reverse initial after ∧
      (∀ row ∈ data.rows, ∃ round, Memory.RoundMask row.assignment round ∧
        Row.spec (Native.input round row.assignment) (Native.output row.assignment)) ∧
      ∀ token ∈ data.terminal, ∃ cell ∈ cells, cell.addressCode = token.address ∧
        cell.readRV after = some (memoryWord token.value) := by
  have clockBound : 2 * timestampBase + 4 < p := by norm_num [timestampBase]; omega
  have seed := inputs.toSeed
  have matching := seed.toMatching clockBound accepted
  have masks := matching_masks clockBound accepted matching
  have bounds := Delegation.SeedProofs.operation_word_bounds hp inverse accepted seed.memory seed.tables
    (fun row member _ => masks row member)
    (by intro row member keccak; rw [inputs.family row member] at keccak; cases keccak)
  have effects : ∀ row ∈ data.rows, ∃ round, Memory.RoundMask row.assignment round ∧
      Row.spec (Native.input round row.assignment) (Native.output row.assignment) := by
    intro row member
    obtain ⟨round, mask⟩ := masks row member
    have holds := accepted.constraints row member
    have reads := bounds.reads row member
    have family := inputs.family row member
    rcases row with ⟨kind, w⟩
    change kind = .blakeRound at family
    subst kind
    simp only [Delegation.Row.constraints, inputs.tables, Delegation.modeledSetup] at holds
    have core := Verification.holds_of_sublist holds (List.sublist_append_left
      (importedConstraints setupTable) importedConstraintsTimestampLookups)
    exact ⟨round, mask, Native.Proofs.native_effects hp inverse round core mask reads⟩
  obtain ⟨ascending, perm, increasing, controls, _⟩ := matching_ordered_controls clockBound accepted matching
  obtain ⟨events, after, permutation, eventOrder, history, _, _, terminal⟩ :=
    Delegation.Proofs.rv_native_memory_execution_at_boundary clockBound accepted inputs.memory aligned
  let ordered := ascending.reverse
  have orderedPerm : ordered.Perm data.rows := (List.reverse_perm ascending).trans perm
  let clock := fun row : Delegation.Row p =>
    (timeOfPair (row.writeToken importedConstraintsMemoryPorts[42]).time).value + 1
  have rowOrder : ordered.Pairwise (fun a b => clock b < clock a) := by
    apply List.pairwise_reverse.mpr
    exact increasing.imp (by intro a b less; change _ + 1 < _ + 1; omega)
  have projection : events.Perm (ordered.flatMap fun row => row.memorySteps.map transferEvent) := by
    have rows := List.Perm.flatMap_right (fun row => row.memorySteps.map transferEvent) orderedPerm
    have pooled : data.rows.flatMap (fun row => row.memorySteps.map transferEvent) = data.steps.map transferEvent := by
      simp only [Delegation.MemoryData.steps, List.map_flatMap]
    exact permutation.trans (pooled ▸ rows).symm
  have times : ∀ row ∈ ordered, ∀ event ∈ row.memorySteps.map transferEvent, event.1 = clock row := by
    intro row _ event present
    obtain ⟨edge, included, rfl⟩ := List.mem_map.mp present
    obtain ⟨port, member, rfl⟩ := List.mem_map.mp included
    exact call_event_time row (by simpa using member)
  refine ⟨ascending, after, perm, increasing, controls,
    rv_grouped_history clock _ rowOrder eventOrder projection times history, effects, ?_⟩
  intro token member
  obtain ⟨cell, present, code, read⟩ := terminal token member
  exact ⟨cell, present, code, by simpa only [memoryWord, MemoryToken.word] using read⟩

theorem rv_call_state_trace [Fact p.Prime] (hp : 8388608 ≤ p)
    (inverse : 64 * (-31457280 : ZMod p) = 1)
    {data : Delegation.MemoryData p} {initial : RV.State} {cells : List Cell} {flags : Fin 8}
    (accepted : Delegation.MemoryAccepted data) (inputs : RVBoundaryCallInputs data initial cells flags)
    (aligned : ∀ cell ∈ cells, cell.Aligned) :
    ∃ (ascending : List (Delegation.Row p)), ∃ count : ascending.length = data.rows.length,
    ∃ (after : RV.State) (states : List RV.State), ∃ stateCount : states.length = data.rows.length + 1,
      ascending.Perm data.rows ∧ states.head? = some after ∧ states.getLast? = some initial ∧
      Delegation.RVTraceMapping data initial after cells ∧
      ∀ i : Fin data.rows.length,
        let row := ascending.reverse[i.val]'(by simpa only [List.length_reverse, count] using i.isLt)
        ∃ round : Fin 10, round.val = data.rows.length - 1 - i.val ∧
        Memory.RoundMask row.assignment round ∧
        Row.spec (Native.input round row.assignment) (Native.output row.assignment) ∧
        (readToken row.assignment importedConstraintsMemoryPorts[42]).word =
          controlAt flags (data.rows.length - 1 - i.val) ∧
        (row.writeToken importedConstraintsMemoryPorts[42]).word =
          controlAt flags (data.rows.length - 1 - i.val + 1) ∧
        ∃ events : List MemoryAccess, events.Perm (row.memorySteps.map transferEvent) ∧
          RVHistory cells events (states[i.val + 1]'(by omega)) (states[i.val]'(by omega)) ∧
          ∀ port ∈ row.ports, ∃ cell ∈ cells, cell.addressCode = port.address.code row.assignment ∧
            cell.readRV (states[i.val + 1]'(by omega)) = some (memoryWord (port.readCode row.assignment)) ∧
            cell.readRV (states[i.val]'(by omega)) = some (memoryWord (port.writeCode row.assignment)) := by
  obtain ⟨ascending, after, permutation, _, controls, history, effects, terminal⟩ :=
    rv_call_scheduled_history hp inverse accepted inputs aligned
  have count := permutation.length_eq
  have reversedPerm := (List.reverse_perm ascending).trans permutation
  have clockBound : 2 * timestampBase + 4 < p := by norm_num [timestampBase]; omega
  obtain ⟨states, stateCount, head, last, ports⟩ :=
    rv_grouped_atomic_boundaries clockBound accepted inputs.memory.toSeed reversedPerm history aligned
  have stateLength : states.length = data.rows.length + 1 := by
    simpa only [List.length_reverse, count] using stateCount
  have trace := rv_grouped_trace_mapping reversedPerm history terminal
  refine ⟨ascending, count, after, states, stateLength, permutation, head, last, trace, ?_⟩
  intro i
  let row := ascending.reverse[i.val]'(by simpa only [List.length_reverse, count] using i.isLt)
  have member : row ∈ data.rows := reversedPerm.mem_iff.mp (List.getElem_mem _)
  have index : row = ascending[data.rows.length - 1 - i.val]'(by omega) := by
    simp only [row, List.getElem_reverse, count]
  have control := controls (data.rows.length - 1 - i.val) (by omega)
  rw [← index] at control
  have high := congrArg Word.hi control.1
  have limit : data.rows.length ≤ 10 := by rw [inputs.calls]; split_ifs <;> decide
  let round : Fin 10 := ⟨data.rows.length - 1 - i.val, by omega⟩
  have power : 2 ^ round.val < 1024 := by have := round.isLt; interval_cases round.val <;> decide
  have read : (row.assignment Variables.controlReadHi).val = flags.val + 8 * 2 ^ round.val := by
    simpa [readToken, MemoryToken.word, importedConstraintsMemoryPorts,
      MemoryPort.readCode, WordColumns.code, pairCode, controlAt, round,
      Nat.mod_eq_of_lt power, Variables.controlReadHi] using high
  have core : FlatOperation.ConstraintsHoldFlat (Verification.environment row.assignment)
      (importedConstraints setupTable) := by
    have holds := accepted.constraints row member
    simp only [Delegation.Row.constraints, inputs.family row member, inputs.tables,
      Delegation.modeledSetup] at holds
    exact Verification.holds_of_sublist holds (List.sublist_append_left
      (importedConstraints setupTable) importedConstraintsTimestampLookups)
  obtain ⟨chosen, mask, effect⟩ := effects row member
  have actualMask := exclusive_mask (by norm_num [timestampBase] at clockBound; omega) core flags round read
  have same : chosen = round := by
    have one := actualMask chosen
    rw [mask chosen, ite_eq_left rfl] at one
    by_contra different
    rw [ite_eq_right different] at one
    exact one_ne_zero one
  subst chosen
  obtain ⟨events, eventPerm, current, observed⟩ :=
    ports i.val (by simpa only [List.length_reverse, count] using i.isLt)
  exact ⟨round, rfl, mask, effect, control.1, control.2, events, eventPerm, current, observed⟩

end Airbender.Blake2Round.Proofs
