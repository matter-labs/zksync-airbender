import Slop.Keccak.SeedCall
import Slop.Keccak.CallHistory
import Slop.Delegation.RVExecution
import Human.Trace.Workers.Keccak.RVCall

/-! RV twin of `CallHistory.call_scheduled_history` and `StateTrace.call_state_trace`: the special5 span's RV history
    grouped by call in control order, and the per-call RV states with each call's port observations. RAM cells include
    the shadow RAM below `ROM_END`. -/

namespace Airbender.Keccak.Proofs
open Trace Trace.Proofs Delegation.Proofs Arithmetic
set_option warningAsError true
set_option maxRecDepth 16384

/-- RV sibling of `BoundaryCallInputs`: the proof-level RV boundary (`RVBoundaryInputs`) and the special5 span ABI. -/
structure RVBoundaryCallInputs [Fact p.Prime] (data : Delegation.MemoryData p)
    (initial : RV.State) (cells : List Cell) : Prop where
  memory : Delegation.Proofs.RVBoundaryInputs data initial cells
  controlCell : Cell.register 10 ∈ cells
  controlStart : (Cell.register 10).readRV initial = some 0
  family : ∀ row ∈ data.rows, row.family = .keccak
  active : ∀ row ∈ data.rows, row.assignment Variables.execute = 1
  calls : data.rows.length = 649

theorem RVBoundaryCallInputs.toSeed [Fact p.Prime] {data : Delegation.MemoryData p} {initial : RV.State}
    {cells : List Cell} (inputs : RVBoundaryCallInputs data initial cells)
    (tables : data.setup = Delegation.modeledSetup Controller.rows) : SeedCallInputs data cells := by
  refine ⟨inputs.memory.toSeed, tables, inputs.controlCell, ?_, inputs.family, inputs.active, inputs.calls⟩
  intro token present code
  rw [rv_seed_word inputs.memory present code inputs.controlStart]
  rfl

/-- Every tracked cell has a seed token, read from the starting RV state. -/
private theorem rv_cell_source {data : Delegation.MemoryData p} {before : RV.State} {cells : List Cell}
    (inputs : RVBoundaryInputs data before cells) {cell : Cell} (member : cell ∈ cells) :
    ∃ token ∈ data.initial, cell.readRV before = some token.word.toBitVec ∧
      token.address = cell.addressCode := by
  obtain ⟨token, present, code⟩ := seed_cell_source inputs.toSeed member
  obtain ⟨other, _, otherCode, read⟩ := inputs.reads token present
  have same : other = cell := cell_address_injective (otherCode.trans code)
  subst other
  exact ⟨token, present, by simpa only [memoryWord, MemoryToken.word] using read, code⟩

theorem rv_call_state_trace [Fact p.Prime] (hp : 16777216 ≤ p)
    (inverse : 256 * (-7864320 : ZMod p) = 1)
    {data : Delegation.MemoryData p} {initial : RV.State} {cells : List Cell}
    (accepted : Delegation.MemoryAccepted data) (inputs : RVBoundaryCallInputs data initial cells)
    (tables : data.setup = Delegation.modeledSetup Controller.rows)
    (aligned : ∀ cell ∈ cells, cell.Aligned) :
    ∃ (pointer : BitVec 32) (ascending : List (Delegation.Row p)), ∃ count : ascending.length = 649,
    ∃ (after : RV.State) (states : List RV.State), ∃ stateCount : states.length = 650,
      (Cell.register 11).readRV initial = some pointer ∧ ascending.Perm data.rows ∧
      states.head? = some after ∧ states.getLast? = some initial ∧
      Delegation.RVTraceMapping data initial after cells ∧
      (∀ physical : Fin 31, ∀ half : Fin 2,
        Cell.ram (pointer + BitVec.ofNat 32 (8 * physical.val + 4 * half.val)) ∈ cells) ∧
      ∀ i : Fin 649,
        let row := ascending.reverse[i.val]'(by simpa only [List.length_reverse, count] using i.isLt)
        row.family = .keccak ∧ Native.RowEffects row.assignment ∧ row.assignment Variables.execute = 1 ∧
        Word.mk (row.assignment Variables.controlReadLo).val (row.assignment Variables.controlReadHi).val =
          ⟨(scheduleControl ⟨648 - i.val, by omega⟩).packed, 0⟩ ∧
        Word.mk (row.assignment Variables.controlWriteLo).val (row.assignment Variables.controlWriteHi).val =
          ⟨(scheduleControl ⟨648 - i.val + 1, by omega⟩).packed, 0⟩ ∧
        statePointer row.assignment = Word.ofBitVec pointer ∧
        (∀ port ∈ row.ports, (readToken row.assignment port).word.Bounded) ∧
        (∀ port ∈ row.ports, (row.writeToken port).word.Bounded) ∧
        ∃ events : List MemoryAccess, events.Perm (row.memorySteps.map transferEvent) ∧
          RVHistory cells events (states[i.val + 1]'(by omega)) (states[i.val]'(by omega)) ∧
          ∀ port ∈ row.ports, ∃ cell ∈ cells, cell.addressCode = port.address.code row.assignment ∧
            cell.readRV (states[i.val + 1]'(by omega)) = some (memoryWord (port.readCode row.assignment)) ∧
            cell.readRV (states[i.val]'(by omega)) = some (memoryWord (port.writeCode row.assignment)) := by
  have clockBound : 2 * timestampBase + 4 < p := by norm_num [timestampBase]; omega
  have seed := inputs.toSeed tables
  obtain ⟨ascending, count, perm, increasing, controls⟩ := seed_call_schedule clockBound accepted seed
  obtain ⟨bounds, effects⟩ := seed_call_effects hp inverse accepted seed
  obtain ⟨tracked, pointers⟩ := seed_call_pointer clockBound accepted seed
  obtain ⟨source, present, pointerRead, code⟩ := rv_cell_source inputs.memory tracked
  have pointerWord : Word.ofBitVec source.word.toBitVec = source.word :=
    word_of_toBitVec (seed.memory.words source present)
  have lanes := seed_call_state_cells hp inverse accepted seed present code
  obtain ⟨events, after, permutation, eventOrder, history, _, _, terminal⟩ :=
    Delegation.Proofs.rv_native_memory_execution_at_boundary clockBound accepted inputs.memory aligned
  let ordered := ascending.reverse
  have orderedPerm : ordered.Perm data.rows := (List.reverse_perm ascending).trans perm
  have rowOrder : ordered.Pairwise (fun a b => callWriteTime b + 1 < callWriteTime a + 1) := by
    apply List.pairwise_reverse.mpr
    exact increasing.imp (by intro a b less; omega)
  have projection : events.Perm (ordered.flatMap fun row => row.memorySteps.map transferEvent) := by
    have rows := List.Perm.flatMap_right (fun row => row.memorySteps.map transferEvent) orderedPerm
    have pooled : data.rows.flatMap (fun row => row.memorySteps.map transferEvent) =
        data.steps.map transferEvent := by
      simp only [Delegation.MemoryData.steps, List.map_flatMap]
    exact permutation.trans (pooled ▸ rows).symm
  have times : ∀ row ∈ ordered, ∀ event ∈ row.memorySteps.map transferEvent,
      event.1 = callWriteTime row + 1 := by
    intro row _ event included
    obtain ⟨edge, member, rfl⟩ := List.mem_map.mp included
    obtain ⟨port, portMember, rfl⟩ := List.mem_map.mp member
    exact call_event_time row (by simpa using portMember)
  have grouped := rv_grouped_history (fun row => callWriteTime row + 1) _ rowOrder eventOrder projection times history
  have terminal' : ∀ token ∈ data.terminal, ∃ cell ∈ cells, cell.addressCode = token.address ∧
      cell.readRV after = some (memoryWord token.value) := by
    intro token member
    obtain ⟨cell, cellMember, cellCode, read⟩ := terminal token member
    exact ⟨cell, cellMember, cellCode, by simpa only [memoryWord, MemoryToken.word] using read⟩
  have trace := rv_grouped_trace_mapping orderedPerm grouped terminal'
  obtain ⟨states, stateCount, head, last, ports⟩ :=
    rv_grouped_atomic_boundaries clockBound accepted seed.memory orderedPerm grouped aligned
  have stateLength : states.length = 650 := by
    simpa only [List.length_reverse, count, ordered] using stateCount
  refine ⟨source.word.toBitVec, ascending, count, after, states, stateLength, pointerRead, perm, head, last, trace,
    lanes, ?_⟩
  intro i
  let row := ascending.reverse[i.val]'(by simpa only [List.length_reverse, count] using i.isLt)
  have member : row ∈ data.rows := orderedPerm.mem_iff.mp (List.getElem_mem _)
  have index : row = ascending[648 - i.val]'(by omega) := by
    simp only [row, List.getElem_reverse, count]
  have control := controls ⟨648 - i.val, by omega⟩
  rw [← index] at control
  obtain ⟨events, eventsPerm, current, observed⟩ :=
    ports i.val (by simpa only [List.length_reverse, count, ordered] using i.isLt)
  exact ⟨seed.family row member, effects row member, seed.active row member, control.1, control.2,
    ((pointers source present code).1 row member).trans pointerWord.symm,
    bounds.reads row member, bounds.writes row member, events, eventsPerm, current, observed⟩

end Airbender.Keccak.Proofs
