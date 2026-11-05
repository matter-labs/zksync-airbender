import Human.Helpers.Context.RVInterfaces
import Slop.Trace.RVProgram
import Slop.Trace.RVHistory
import Slop.Trace.RVRom
import Slop.Trace.RVZero
import Slop.Trace.RVWritable

/-! Shared RV facts for one row of an accepted pooled trace, for every family:

    - `rv_pooled_row_entry`: the row's public program entry (family and query match, an aligned ROM word of the
      starting memory that `RV.decode`s to `i` with `rvPooledDecoderFields i = some entry.data`), and the row's start
      PC is the entry's PC. `rv_pooled_fields_family` turns the pooled projection into the row family's own.
    - `rv_pooled_row_history`: the row's native events are an RV history from the row's pre-state (up to its PC),
      together with the x0 and writable-store laws of the whole trace. Each family derives its operand reads from it
      (`rv_row_operand_reads`).
    - `rv_step_of_position` / `rv_step_of_row`: `RV.step` of the row's pre-state executes the entry's instruction. -/

namespace Airbender.Trace.Proofs
open Arithmetic

/-! ### (a) The row's program entry -/

/-- The pooled projection restricted to one family: the entry's family tag selects the family's own projection. -/
theorem rv_pooled_fields_family {i : RV.Instr} {data : DecoderData PooledFamily}
    (fields : rvPooledDecoderFields i = some data) :
    ((data.family = .addSub ∨ data.family = .wordMemory) →
      ∃ d, rvDecoderFields i = some d ∧ data = d.mapFamily pooledArithmeticFamily) ∧
    (data.family = .jumpBranchSlt →
      ∃ d, JumpBranchSlt.rvDecoderFields i = some d ∧ data = d.mapFamily (fun _ => .jumpBranchSlt)) ∧
    (data.family = .mulDiv →
      ∃ d, MulDiv.rvDecoderFields i = some d ∧ data = d.mapFamily (fun _ => .mulDiv)) ∧
    (data.family = .shiftBinop →
      ∃ d, ShiftBinop.rvDecoderFields i = some d ∧ data = d.mapFamily (fun _ => .shiftBinop)) ∧
    (data.family = .subwordMemory →
      ∃ d, SubwordMemory.rvDecoderFields i = some d ∧ data = d.mapFamily (fun _ => .subwordMemory)) := by
  have arithmetic (f : Family) : pooledArithmeticFamily f = .addSub ∨ pooledArithmeticFamily f = .wordMemory := by
    cases f <;> simp [pooledArithmeticFamily]
  rcases rv_pooled_fields_cases fields with h | h | h | h | h
  all_goals obtain ⟨d, fd, rfl⟩ := h
  all_goals refine ⟨?_, ?_, ?_, ?_, ?_⟩
  all_goals intro tag
  all_goals first
    | exact ⟨d, fd, rfl⟩
    | (simp [DecoderData.mapFamily] at tag; done)
    | (rcases arithmetic d.family with a | a <;> simp [DecoderData.mapFamily, a] at tag)

/-- (a) Row-entry fetch: every row of an accepted RV-decoded pooled trace has a public program entry with the row's
    family and query, an aligned ROM address whose starting bytes decode to `i` with native data
    `rvPooledDecoderFields i`; the row's start PC is the entry's PC. -/
theorem rv_pooled_row_entry {p : Nat} [Fact p.Prime] (hp : limbBase < p)
    {trace : PooledTrace p} {initial : RV.State} {addresses : List (BitVec 32)}
    {program : List RVPooledProgramEntry}
    (image : rvProgramImageWith rvPooledDecoderFields initial addresses = some program)
    (decoded : RVPooledDecoded trace program) {row : Row p PooledFamily} (member : row ∈ trace.rows) :
    ∃ entry ∈ program, ∃ i : RV.Instr,
      entry.data.family = row.family ∧ row.decoderQuery = entry.query ∧
      RV.decode entry.bits = some i ∧ rvPooledDecoderFields i = some entry.data ∧
      (entry.pc.toNat < RV.ROM_END ∧ entry.pc.toNat % 4 = 0) ∧
      entry.bits = RV.read initial.mem entry.pc 4 ∧
      row.start.word.toBitVec = entry.pc := by
  obtain ⟨entry, present, family, query⟩ := rv_decoder_member (decoded row member)
  obtain ⟨guard, bits, i, decodes, fields⟩ := rvProgram_entry_fetch image entry present
  exact ⟨entry, present, i, family, query, decodes, fields, guard, bits, rv_query_pc hp query⟩

/-! ### (b) The row's RV history -/

/-- Native port updates do not read or write the PC. -/
theorem applyRV_with_pc {cell : Cell} {value : BitVec 32} {s t : RV.State} (pc : BitVec 32)
    (write : cell.applyRV value s = some t) :
    cell.applyRV value { s with pc := pc } = some { t with pc := pc } := by
  have read : cell.readRV { s with pc := pc } = cell.readRV s := by cases cell <;> rfl
  unfold Cell.applyRV at write ⊢
  rw [read]
  by_cases h : cell.readRV s = some value
  · rw [if_pos h] at write
    rw [if_pos h]
    obtain rfl := Option.some.inj write
    rfl
  · rw [if_neg h] at write
    rw [if_neg h]
    cases cell with
    | register index =>
      obtain rfl := Option.some.inj write
      rfl
    | ram address =>
      simp only [Cell.writeRV] at write ⊢
      by_cases w : RV.writable address 4
      · rw [if_pos w] at write
        rw [if_pos w]
        obtain rfl := Option.some.inj write
        rfl
      · rw [if_neg w] at write
        cases write

/-- RV histories do not read or write the PC. -/
theorem rv_history_with_pc {cells : List Cell} {events : List MemoryAccess} {before after : RV.State}
    (history : RVHistory cells events before after) (pc : BitVec 32) :
    RVHistory cells events { before with pc := pc } { after with pc := pc } := by
  induction history with
  | nil before => exact .nil _
  | cons past cell member address read write ih =>
    refine .cons ih cell member address ?_ (applyRV_with_pc pc write)
    cases cell <;> exact read

/-- (b) Family-agnostic row history: for any pooled row at RV pre-state `before`, the earlier rows' events are an RV
    history from the starting state to `middle`, the row's own events (`rowEvents`, reversed: first port first) are an
    RV history from `middle` (equivalently from `before`, which is `middle` at the row's start PC), and every native
    write to x0 carries zero and every changing RAM write is RV-writable. -/
theorem rv_pooled_row_history {p : Nat} [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    (inverse : (-3840 : ZMod p) * 524288 = 1) {trace : PooledTrace p} (accepted : Accepted trace)
    {initial : RV.State} {cells : List Cell} {program : List RVPooledProgramEntry}
    (inputs : RVPooledHistoryInputs trace initial cells program)
    (decoded : RVPooledDecoded trace program)
    {row : Row p PooledFamily} {before : RV.State}
    (position : RVRowPosition trace initial cells row before) :
    ∃ (middle : RV.State) (events : List MemoryAccess) (rawAfter : RV.State),
      (∀ event ∈ events, event ∈ trace.nativeEvents) ∧
      RVHistory cells events initial middle ∧
      RVHistory cells (rowEvents trace.memoryEpoch row).reverse middle rawAfter ∧
      before = { middle with pc := row.start.word.toBitVec } ∧
      RVHistory cells (rowEvents trace.memoryEpoch row).reverse before { rawAfter with pc := before.pc } ∧
      (∀ event ∈ trace.nativeEvents, event.2.1 = (Cell.register 0).addressCode →
        memoryWord event.2.2.2 = 0) ∧
      (∀ event ∈ trace.nativeEvents, event.2.2.1 ≠ event.2.2.2 → ∀ cell ∈ cells,
        cell.addressCode = event.2.1 → ∀ index, cell = .ram index → RV.writable index 4) := by
  have clocks := inputs.initialization.clocks
  obtain ⟨addresses, programImage⟩ := inputs.initialization.programImage
  have zero := Airbender.Trace.RVZero.rv_pooled_zero_writes hp inverse accepted clocks inputs.initialization.image
    programImage decoded
  have writable := Airbender.Trace.RVWritable.rv_pooled_writable hp accepted inputs.initialization.aligned
  obtain ⟨history, rows, after, _, rowsPermutation, rowsOrdered, native, _⟩ :=
    rv_native_row_history hp inverse accepted clocks inputs.initialization.image
      inputs.initialization.distinct inputs.initialization.aligned zero writable
  have projection :
      (rows.flatMap fun row => (rowEvents trace.memoryEpoch row).reverse).Perm trace.nativeEvents := by
    rw [native_events_projection (by dsimp [timestampBase] at hp; omega) inverse accepted clocks]
    exact rowsPermutation.flatMap (fun row _ => List.reverse_perm _)
  obtain ⟨middle, events, rawAfter, present, past, current, atState⟩ :=
    rv_row_context_of_history rowsPermutation rowsOrdered native projection position
  refine ⟨middle, events, rawAfter, present, past, current, atState, ?_, zero, writable⟩
  subst atState
  exact rv_history_with_pc current _

/-! ### (c) The step of the row's pre-state -/

/-- (c) For a row at RV pre-state `before` whose start PC is an aligned ROM address `pc` whose starting bytes decode
    to `i`, `RV.step before` executes `i` (the earlier rows' writes never change ROM). -/
theorem rv_step_of_position {Kind : Type} [CircuitLayout Kind] {p : Nat} [Fact p.Prime]
    {trace : Data p Kind} {initial : RV.State} {cells : List Cell} {row : Row p Kind} {before : RV.State}
    (position : RVRowPosition trace initial cells row before)
    {pc : BitVec 32} (start : row.start.word.toBitVec = pc)
    (guard : pc.toNat < RV.ROM_END ∧ pc.toNat % 4 = 0)
    {i : RV.Instr} (decodes : RV.decode (RV.read initial.mem pc 4) = some i) :
    before.pc = pc ∧ RV.step before = RV.exec before i := by
  obtain ⟨_, _, middle, _, _, writes, atState⟩ := position
  have beforePC : before.pc = pc := by
    rw [atState]
    exact start
  have agree : ∀ a : RV.Word, a.toNat < RV.ROM_END → before.mem a = initial.mem a := by
    intro a rom
    rw [atState]
    exact rvWriteHistory_rom writes a rom
  obtain ⟨_, step⟩ := rv_step_fetch before initial agree pc beforePC guard
  rw [decodes] at step
  exact ⟨beforePC, step⟩

/-- (c) for a pooled row: (a) and `rv_step_of_position` together. -/
theorem rv_step_of_row {p : Nat} [Fact p.Prime] (hp : limbBase < p)
    {trace : PooledTrace p} {initial : RV.State} {cells : List Cell} {addresses : List (BitVec 32)}
    {program : List RVPooledProgramEntry}
    (image : rvProgramImageWith rvPooledDecoderFields initial addresses = some program)
    (decoded : RVPooledDecoded trace program) {row : Row p PooledFamily} (member : row ∈ trace.rows)
    {before : RV.State} (position : RVRowPosition trace initial cells row before) :
    ∃ entry ∈ program, ∃ i : RV.Instr,
      entry.data.family = row.family ∧ row.decoderQuery = entry.query ∧
      RV.decode entry.bits = some i ∧ rvPooledDecoderFields i = some entry.data ∧
      before.pc = entry.pc ∧ RV.step before = RV.exec before i := by
  obtain ⟨entry, present, i, family, query, decodes, fields, guard, bits, start⟩ :=
    rv_pooled_row_entry hp image decoded member
  have fetched : RV.decode (RV.read initial.mem entry.pc 4) = some i := bits ▸ decodes
  obtain ⟨beforePC, step⟩ := rv_step_of_position position start guard fetched
  exact ⟨entry, present, i, family, query, decodes, fields, beforePC, step⟩

end Airbender.Trace.Proofs
