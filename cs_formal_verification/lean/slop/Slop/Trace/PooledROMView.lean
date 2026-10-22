import Slop.Trace.ROMView
import Slop.Trace.PooledComposition

namespace Airbender.Trace.PooledROMView
open Arithmetic Reference.RiscV.Sail
open ROMView

/-- ROM load-data columns and their dependent helpers are recomputed. Native
    addresses, clocks, queries and outputs retain their original witness values. -/
def subwordReadData (w : Nat → ZMod p) (lo hi : ZMod p) : Nat → ZMod p :=
  fun i => if i = 25 then lo else if i = 26 then hi
    else if i = 50 then w 36 * hi + (1 - w 36) * lo + 65536 * w 12 + 131072 * w 35
    else if i = 51 then w 11 * (lo + 65536 * w 35)
    else if i = 54 then w 36 * w 34 + (1 - w 36) * w 33 - w 11 * w 43 - (1 - w 11) * lo
    else w i

set_option maxRecDepth 16384 in
set_option maxHeartbeats 1000000 in
theorem subword_read_data_unused {p : Nat} [Fact p.Prime]
    {setup : Table (ZMod p) (fields 9)} {w : Nat → ZMod p}
    (load : w 10 = 0) (rom : w 41 = 1) (lo hi : ZMod p)
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (SubwordMemory.clockConstraints setup)) :
    FlatOperation.ConstraintsHoldFlat (Verification.environment (subwordReadData w lo hi))
      (SubwordMemory.clockConstraints setup) := by
  have core := Verification.holds_of_sublist h
    (List.sublist_append_left (SubwordMemory.importedConstraints setup) SubwordMemory.importedConstraintsTimestampLookups)
  have ram := Verification.assertion_of_holds core ⟨15, by rw [SubwordMemory.constraint_count]; decide⟩
  have store := Verification.assertion_of_holds core ⟨16, by rw [SubwordMemory.constraint_count]; decide⟩
  have ramZero : w 47 = 0 := by
    simpa [SubwordMemory.importedConstraints, FlatOperation.constraints, Expression.eval,
      Verification.environment, load, rom] using ram
  have storeZero : w 48 = 0 := by
    simpa [SubwordMemory.importedConstraints, FlatOperation.constraints, Expression.eval,
      Verification.environment, load, rom] using store
  simp [SubwordMemory.clockConstraints, SubwordMemory.importedConstraints,
    SubwordMemory.importedConstraintsTimestampLookups, FlatOperation.ConstraintsHoldFlat,
    Verification.environment, Expression.eval, subwordReadData, Lookup.Contains,
    Verification.range16, timestampLookup, Table.toRaw, load, rom, ramZero, storeZero] at h ⊢
  repeat' apply And.intro
  all_goals first | (solve | simp_all) | ring

def row {p : Nat} [Fact p.Prime] (before : State) (native : Row p PooledFamily) : Row p PooledFamily :=
  match native.family with
  | .wordMemory => ⟨.wordMemory, (ROMView.row before (⟨.wordMemory, native.assignment⟩ : Row p)).assignment⟩
  | .subwordMemory =>
    if native.assignment 10 = 0 ∧ native.assignment 41 = 1 then
      let word := publicWord before (Nat.pair 1
        (Nat.pair (native.assignment 21).val (native.assignment 22).val))
      { native with assignment := subwordReadData native.assignment word.lo word.hi }
    else native
  | _ => native

@[simp] theorem row_family {p : Nat} [Fact p.Prime] (before : State) (native : Row p PooledFamily) :
    (row before native).family = native.family := by
  rcases native with ⟨family, w⟩
  cases family <;> first | rfl | (dsimp only [row]; split <;> rfl)

@[simp] theorem row_start {p : Nat} [Fact p.Prime] (before : State) (native : Row p PooledFamily) :
    (row before native).start = native.start := by
  rcases native with ⟨family, w⟩
  cases family with
  | wordMemory =>
    change (⟨.wordMemory, (ROMView.row before (⟨.wordMemory, w⟩ : Row p)).assignment⟩ : Row p).start =
      (⟨.wordMemory, w⟩ : Row p).start
    simpa only [Row.start, Row.columns, ROMView.row_family] using
      ROMView.row_start before (⟨.wordMemory, w⟩ : Row p)
  | subwordMemory =>
    dsimp only [row]
    split <;> simp [Row.start, Row.columns, CircuitLayout.columns,
      SubwordMemory.importedConstraintsTraceColumns, rawPair, subwordReadData]
  | addSub | jumpBranchSlt | mulDiv | shiftBinop => rfl

@[simp] theorem row_finish {p : Nat} [Fact p.Prime] (before : State) (native : Row p PooledFamily) :
    (row before native).finish = native.finish := by
  rcases native with ⟨family, w⟩
  cases family with
  | wordMemory =>
    change (⟨.wordMemory, (ROMView.row before (⟨.wordMemory, w⟩ : Row p)).assignment⟩ : Row p).finish =
      (⟨.wordMemory, w⟩ : Row p).finish
    simpa only [Row.finish, Row.columns, ROMView.row_family] using
      ROMView.row_finish before (⟨.wordMemory, w⟩ : Row p)
  | subwordMemory =>
    dsimp only [row]
    split <;> simp [Row.finish, Row.columns, CircuitLayout.columns,
      SubwordMemory.importedConstraintsTraceColumns, rawPair, subwordReadData]
  | addSub | jumpBranchSlt | mulDiv | shiftBinop => rfl

@[simp] theorem row_query {p : Nat} [Fact p.Prime] (before : State) (native : Row p PooledFamily) :
    (row before native).decoderQuery = native.decoderQuery := by
  rcases native with ⟨family, w⟩
  cases family with
  | wordMemory =>
    change (⟨.wordMemory, (ROMView.row before (⟨.wordMemory, w⟩ : Row p)).assignment⟩ : Row p).decoderQuery =
      (⟨.wordMemory, w⟩ : Row p).decoderQuery
    simpa only [Row.decoderQuery, Row.columns, Row.decoderColumns, ROMView.row_family] using
      ROMView.row_query before (⟨.wordMemory, w⟩ : Row p)
  | subwordMemory =>
    dsimp only [row]
    split
    · simp [Row.decoderQuery, Row.columns, CircuitLayout.columns, Row.decoderColumns,
      CircuitLayout.decoderColumns, SubwordMemory.importedConstraintsTraceColumns,
        SubwordMemory.importedConstraintsDecoderColumns, nativeDecoderQuery, subwordReadData]
      congr 1
      funext index
      fin_cases index <;> simp
    · rfl
  | addSub | jumpBranchSlt | mulDiv | shiftBinop => rfl

theorem row_holds {p : Nat} [Fact p.Prime] (before : State)
    (native : Row p PooledFamily) (setup : PooledSetup p)
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment native.assignment) (native.constraints setup)) :
    FlatOperation.ConstraintsHoldFlat (Verification.environment (row before native).assignment)
      ((row before native).constraints setup) := by
  rcases native with ⟨family, w⟩
  cases family
  all_goals first
    | exact h
    | (simpa only [row, Row.constraints, CircuitLayout.constraints, ROMView.row_family] using
        ROMView.row_holds before (⟨.wordMemory, w⟩ : Row p) setup.wordMemory h)
    | (dsimp only [row]; split
       · rename_i selected
         exact subword_read_data_unused selected.1 selected.2 _ _ h
       · exact h)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 1000000 in
theorem row_transfers {p : Nat} [Fact p.Prime] (hp : 131072 < p)
    (before : State) (native : Row p PooledFamily) (setup : PooledSetup p)
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment native.assignment) (native.constraints setup))
    (bounds : ∀ port ∈ native.ports, (port.address.word native.assignment).Bounded) :
    (row before native).reads = native.reads.map (token before) ∧
      (row before native).writes = native.writes.map (token before) := by
  rcases native with ⟨family, w⟩
  cases family with
  | wordMemory =>
    simpa only [row, Row.reads, Row.writes, Row.ports, CircuitLayout.ports, Row.columns, CircuitLayout.columns, ROMView.row_family] using
      ROMView.row_transfers hp before (⟨.wordMemory, w⟩ : Row p) setup.wordMemory h bounds
  | addSub | jumpBranchSlt | mulDiv | shiftBinop =>
    simp [row, Row.reads, Row.writes, Row.ports, CircuitLayout.ports, Row.columns, CircuitLayout.columns,
      AddSub.importedConstraintsMemoryPorts, AddSub.importedConstraintsTraceColumns,
      JumpBranchSlt.importedConstraintsMemoryPorts, JumpBranchSlt.importedConstraintsTraceColumns,
      MulDiv.importedConstraintsMemoryPorts, MulDiv.importedConstraintsTraceColumns,
      ShiftBinop.importedConstraintsMemoryPorts, ShiftBinop.importedConstraintsTraceColumns,
      readToken, writeToken, MemoryAddress.code, MemoryPort.readCode, MemoryPort.writeCode,
      WordColumns.code, WordColumns.evaluate, token, shadow]
  | subwordMemory =>
    have core := Verification.holds_of_sublist h
      (List.sublist_append_left (SubwordMemory.importedConstraints setup.subwordMemory)
        SubwordMemory.importedConstraintsTimestampLookups)
    have loadBound : (Word.mk (w 21).val (w 22).val).Bounded := by
      exact bounds SubwordMemory.importedConstraintsMemoryPorts[1]
        (by change _ ∈ SubwordMemory.importedConstraintsMemoryPorts; simp [SubwordMemory.importedConstraintsMemoryPorts])
    have storeBound : (Word.mk (w 27).val (w 28).val).Bounded := by
      exact bounds SubwordMemory.importedConstraintsMemoryPorts[2]
        (by change _ ∈ SubwordMemory.importedConstraintsMemoryPorts; simp [SubwordMemory.importedConstraintsMemoryPorts])
    have flag : w 10 = 0 ∨ w 10 = 1 := SubwordMemory.Proofs.local_flags core 1
    rcases flag with load | store
    · have classification := (SubwordMemory.Proofs.rom_selection hp false core load
        (address := ⟨(w 21).val, (w 22).val⟩) (ZMod.natCast_zmod_val _).symm loadBound).1
      change w 41 = (if (w 22).val < 64 then 1 else 0) at classification
      by_cases inside : (w 22).val < 64
      · have selected : w 41 = 1 := by simpa [inside] using classification
        have one : (1 : ZMod p).val = 1 := by
          rw [ZMod.val_one_eq_one_mod]; exact Nat.mod_eq_of_lt (by omega)
        have loBound := lt_trans (public_word_bound before (Nat.pair 1 (Nat.pair (w 21).val (w 22).val))).1
          (by change 65536 < p; omega)
        have hiBound := lt_trans (public_word_bound before (Nat.pair 1 (Nat.pair (w 21).val (w 22).val))).2
          (by change 65536 < p; omega)
        simp [row, load, selected, Row.reads, Row.writes, Row.ports, CircuitLayout.ports, Row.columns, CircuitLayout.columns,
          SubwordMemory.importedConstraintsMemoryPorts, SubwordMemory.importedConstraintsTraceColumns,
          readToken, writeToken, MemoryAddress.code, MemoryPort.readCode, MemoryPort.writeCode,
          pairCode, rawPair, token, shadow, subwordReadData, inside, one,
          ZMod.val_natCast_of_lt loBound, ZMod.val_natCast_of_lt hiBound]
      · have selected : w 41 = 0 := by simpa [inside] using classification
        simp [row, load, selected, Row.reads, Row.writes, Row.ports, CircuitLayout.ports, Row.columns, CircuitLayout.columns,
          SubwordMemory.importedConstraintsMemoryPorts, SubwordMemory.importedConstraintsTraceColumns,
          readToken, writeToken, MemoryAddress.code, MemoryPort.readCode, MemoryPort.writeCode,
          pairCode, token, shadow, inside]
    · have outside := (SubwordMemory.Proofs.rom_selection hp true core store
        (address := ⟨(w 27).val, (w 28).val⟩) (ZMod.natCast_zmod_val _).symm storeBound).2 rfl
      change 64 ≤ (w 28).val at outside
      have notROM : ¬ (w 28).val < 64 := by omega
      simp [row, store, Row.reads, Row.writes, Row.ports, CircuitLayout.ports, Row.columns, CircuitLayout.columns,
        SubwordMemory.importedConstraintsMemoryPorts, SubwordMemory.importedConstraintsTraceColumns,
        readToken, writeToken, MemoryAddress.code, MemoryPort.readCode, MemoryPort.writeCode,
        pairCode, token, shadow, notROM]

def data {p : Nat} [Fact p.Prime] (before : State) (native : PooledTrace p) : PooledTrace p :=
  { native with rows := native.rows.map (row before)
                initialMemory := native.initialMemory.map (token before)
                terminalMemory := native.terminalMemory.map (token before) }

theorem accepted {p : Nat} [Fact p.Prime]
    (hp : 2 * timestampBase + 4 < p) (inverse : (-3840 : ZMod p) * 524288 = 1)
    (before : State) {trace : PooledTrace p} {cells : List Cell}
    (native : Accepted trace) (clocks : ClockBoundary trace)
    (seed : trace.initialMemory = nativeBootImage cells) : Accepted (data before trace) := by
  have addresses := ROMView.native_addresses hp inverse native clocks seed
  have transfers : ∀ r ∈ trace.rows,
      (row before r).reads = r.reads.map (token before) ∧
      (row before r).writes = r.writes.map (token before) := by
    intro r member
    exact row_transfers (by unfold timestampBase at hp; omega) before r trace.rom
      (native.constraints r member) (addresses r member)
  constructor
  · intro r member
    change r ∈ trace.rows.map (row before) at member
    obtain ⟨original, inRows, rfl⟩ := List.mem_map.mp member
    exact row_holds before original trace.rom (native.constraints original inRows)
  · intro r member
    change r ∈ trace.rows.map (row before) at member
    obtain ⟨original, inRows, rfl⟩ := List.mem_map.mp member
    have active := native.active original inRows
    rcases original with ⟨family, w⟩
    cases family with
    | wordMemory =>
      dsimp only [row, ROMView.row]
      split <;> simpa [Row.columns, CircuitLayout.columns,
        WordMemory.importedConstraintsTraceColumns, readData] using active
    | subwordMemory =>
      dsimp only [row]
      split <;> simpa [Row.columns, CircuitLayout.columns,
        SubwordMemory.importedConstraintsTraceColumns, subwordReadData] using active
    | addSub | jumpBranchSlt | mulDiv | shiftBinop => exact active
  · simpa [data, List.map_map, Function.comp_def] using native.states
  · have matching := native.memory.map (token before)
    have reads : (trace.rows.map (row before)).flatMap Row.reads =
        (trace.rows.flatMap Row.reads).map (token before) := by
      simp only [List.flatMap_map, List.map_flatMap]
      apply congrArg List.flatten
      apply List.map_congr_left
      intro r member
      exact (transfers r member).1
    have writes : (trace.rows.map (row before)).flatMap Row.writes =
        (trace.rows.flatMap Row.writes).map (token before) := by
      simp only [List.flatMap_map, List.map_flatMap]
      apply congrArg List.flatten
      apply List.map_congr_left
      intro r member
      exact (transfers r member).2
    simpa only [data, reads, writes, List.map_append] using matching

theorem decoded {p : Nat} [Fact p.Prime] (before : State)
    {trace : PooledTrace p} {program : List PooledProgramEntry}
    (native : PooledDecoded trace program) : PooledDecoded (data before trace) program := by
  intro r member
  change r ∈ trace.rows.map (row before) at member
  obtain ⟨original, inRows, rfl⟩ := List.mem_map.mp member
  simpa [PooledDecoded] using native original inRows

theorem data_clocks {p : Nat} [Fact p.Prime] (before : State)
    {trace : PooledTrace p} (clocks : ClockBoundary trace) : ClockBoundary (data before trace) := by
  refine ⟨clocks.initial, clocks.aligned, ?_⟩
  intro lifted member
  change lifted ∈ trace.initialMemory.map (token before) at member
  obtain ⟨native, present, rfl⟩ := List.mem_map.mp member
  simpa only [token_time] using clocks.memory native present

/-- The public byte view discharges physical initialization; only proven unused
    ROM columns/intermediates change. All native trace outputs stay fixed. -/
theorem execution_boundary {p : Nat} [Fact p.Prime] (hp : 4 < p)
    {projection : SailRV32.instruction → Option (DecoderData PooledFamily)}
    {trace : PooledTrace p} {before : State} {cells : List Cell} {program : List PooledProgramEntry}
    (inputs : PooledBootInputs trace before cells program projection) :
    PooledInputs (data before trace) before cells program projection := by
  obtain ⟨image, reads, setup⟩ := inputs.physicalImage
  have physical : (data before trace).initialMemory = image := by
    change trace.initialMemory.map (token before) = image
    rw [inputs.seed]
    exact ROMView.seed_image inputs.profile reads
  refine { toPooledPublicInputs := inputs.toPooledPublicInputs
           toNativeInputs := {
             distinct := inputs.distinct
             aligned := inputs.aligned
             image := physical.symm ▸ reads
             initialPC := ⟨(4, 0), ?_⟩
             programImage := inputs.programImage
             clocks := data_clocks before (ROMView.native_clocks hp inputs.seed inputs.initialBoundary) }
           wordSetup := physical.symm ▸ setup
           subwordSetup := inputs.subwordSetup
           terminalPC := inputs.terminalPC }
  change initialState before (4, 0) = some trace.initial
  rw [initialState, inputs.profile.pc, inputs.initialBoundary]

/-- Lift pooled physical execution back to the unchanged native trace. -/
theorem trace_execution
    {p : Nat} [Fact p.Prime]
    (hp : 536870912 ≤ p) (inverse : (-3840 : ZMod p) * 524288 = 1)
    {trace : PooledTrace p} {before : State} {cells : List Cell} {program : List PooledProgramEntry}
    (inputs : PooledBootInputs trace before cells program)
    (native : Accepted trace) (membership : PooledDecoded trace program) :
    Realizes (PooledStep program) trace before cells (token before) := by
  have clockSize : 2 * timestampBase + 4 < p := by dsimp [timestampBase]; omega
  have size : 4 < p := by omega
  have clocks := ROMView.native_clocks size inputs.seed inputs.initialBoundary
  obtain ⟨after, execution, pc, terminal⟩ := Proofs.pooled_trace_execution hp inverse
    (execution_boundary size inputs)
    (accepted clockSize inverse before native clocks inputs.seed)
    (decoded before membership)
  refine ⟨after, execution, pc, ?_⟩
  intro sink member
  have lifted := terminal (token before sink) (List.mem_map_of_mem member)
  simpa only [token_address, id_eq] using lifted

end Airbender.Trace.PooledROMView
