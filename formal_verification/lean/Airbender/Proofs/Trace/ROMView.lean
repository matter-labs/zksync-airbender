import Airbender.Review.Helpers.Core.FieldCapacity
import Airbender.Review.Helpers.Core.SerializedInverse
import Airbender.Proofs.WordMemory
import Airbender.Proofs.Trace.Initialization
import Airbender.Proofs.Trace.Addresses
import Airbender.Review.Helpers.Memory.Native

namespace Airbender.Trace.ROMView
open Arithmetic

def readData (w : Nat → ZMod p) (lo hi : ZMod p) : Nat → ZMod p :=
  fun i => if i = WordMemory.Variables.readDataLo then lo
    else if i = WordMemory.Variables.readDataHi then hi else w i

set_option maxRecDepth 16384 in
set_option maxHeartbeats 1000000 in
/-- ROM loads do not use the native read-value columns in any retained
    equation, lookup or clock constraint. Replacing them preserves exactly
    the same imported Clean relation; no compiler correspondence is involved. -/
theorem read_data_unused {p : Nat} [Fact p.Prime]
    {rom : Table (ZMod p) (fields 9)} {w : Nat → ZMod p}
    (load : w WordMemory.Variables.storeSelector = 0)
    (inROM : w WordMemory.Variables.romSelector = 1) (lo hi : ZMod p) :
    FlatOperation.ConstraintsHoldFlat (Verification.environment (readData w lo hi))
      (WordMemory.clockConstraints rom) ↔
    FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (WordMemory.clockConstraints rom) := by
  simp [WordMemory.clockConstraints, WordMemory.importedConstraints,
    WordMemory.importedConstraintsTimestampLookups, FlatOperation.ConstraintsHoldFlat,
    Verification.environment, Expression.eval, readData, Lookup.Contains,
    Verification.range16, timestampLookup, Table.toRaw, load, inROM]

theorem public_word_bound (before : Reference.RiscV.Sail.State) (address : Nat) :
    (publicWord before address).Bounded := by
  dsimp only [publicWord]
  split
  · exact Word.ofBitVec_bound _
  · exact ⟨by decide, by decide⟩

@[simp] theorem token_address (before : Reference.RiscV.Sail.State) (native : MemoryToken p) :
    (token before native).address = native.address := by
  unfold token
  split <;> rfl

@[simp] theorem token_time (before : Reference.RiscV.Sail.State) (native : MemoryToken p) :
    (token before native).time = native.time := by
  unfold token
  split <;> rfl

/-- Change only unused ROM read values. Selectors, addresses, clocks, decoded
    operands and every instruction output remain the original witness data. -/
def row (before : Reference.RiscV.Sail.State) (native : Row p) : Row p :=
  match native.family with
  | .addSub => native
  | .wordMemory =>
    if native.assignment 10 = 0 ∧ native.assignment 35 = 1 then
      let word := publicWord before (Nat.pair 1
        (Nat.pair (native.assignment 19).val (native.assignment 20).val))
      { native with assignment := readData native.assignment word.lo word.hi }
    else native

@[simp] theorem row_family (before : Reference.RiscV.Sail.State) (native : Row p) :
    (row before native).family = native.family := by
  unfold row
  split
  · rfl
  · split <;> rfl

@[simp] theorem row_start (before : Reference.RiscV.Sail.State) (native : Row p) :
    (row before native).start = native.start := by
  rcases native with ⟨family, w⟩
  cases family with
  | addSub => rfl
  | wordMemory =>
    dsimp only [row]
    split <;> simp [Row.start, Row.columns, rawPair,
      WordMemory.importedConstraintsTraceColumns, readData]

@[simp] theorem row_finish (before : Reference.RiscV.Sail.State) (native : Row p) :
    (row before native).finish = native.finish := by
  rcases native with ⟨family, w⟩
  cases family with
  | addSub => rfl
  | wordMemory =>
    dsimp only [row]
    split <;> simp [Row.finish, Row.columns, rawPair,
      WordMemory.importedConstraintsTraceColumns, readData]

@[simp] theorem row_query (before : Reference.RiscV.Sail.State) (native : Row p) :
    (row before native).decoderQuery = native.decoderQuery := by
  rcases native with ⟨family, w⟩
  cases family with
  | addSub => rfl
  | wordMemory =>
    dsimp only [row]
    split <;> simp [Row.decoderQuery, nativeDecoderQuery, Row.decoderColumns,
      Row.columns, WordMemory.importedConstraintsTraceColumns,
      WordMemory.importedConstraintsDecoderColumns, readData]

theorem row_holds {p : Nat} [Fact p.Prime]
    (before : Reference.RiscV.Sail.State) (native : Row p) (rom : Table (ZMod p) (fields 9))
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment native.assignment)
      (native.constraints rom)) :
    FlatOperation.ConstraintsHoldFlat (Verification.environment (row before native).assignment)
      ((row before native).constraints rom) := by
  rcases native with ⟨family, w⟩
  cases family with
  | addSub => exact holds
  | wordMemory =>
    dsimp only [row]
    split
    · rename_i selected
      exact (read_data_unused selected.1 selected.2 _ _).mpr holds
    · exact holds

set_option maxRecDepth 16384 in
set_option maxHeartbeats 1000000 in
theorem row_transfers {p : Nat} [Fact p.Prime] (hp : FieldCapacity.NoWrap p 131072)
    (before : Reference.RiscV.Sail.State) (native : Row p) (rom : Table (ZMod p) (fields 9))
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment native.assignment)
      (native.constraints rom))
    (bounds : ∀ port ∈ native.ports, (port.address.word native.assignment).Bounded) :
    (row before native).reads = native.reads.map (token before) ∧
      (row before native).writes = native.writes.map (token before) := by
  rcases native with ⟨family, w⟩
  cases family with
  | addSub =>
    simp [row, Row.reads, Row.writes, Row.ports, Row.columns,
      AddSub.importedConstraintsMemoryPorts, AddSub.importedConstraintsTraceColumns,
      readToken, writeToken, MemoryAddress.code, MemoryPort.readCode, MemoryPort.writeCode,
      token, shadow]
  | wordMemory =>
    have base : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
        (WordMemory.importedConstraints rom) := Verification.holds_of_sublist holds
      (List.sublist_append_left (WordMemory.importedConstraints rom)
        WordMemory.importedConstraintsTimestampLookups)
    have loadBound : (Word.mk (w 19).val (w 20).val).Bounded := by
      exact bounds ⟨⟨1, #v[21, 22], 47, none⟩, .mixed 10 true #v[19, 20], #v[23, 24], none⟩
        (by simp [Row.ports, WordMemory.importedConstraintsMemoryPorts])
    have storeBound : (Word.mk (w 25).val (w 26).val).Bounded := by
      exact bounds ⟨⟨2, #v[27, 28], 48, none⟩, .mixed 10 false #v[25, 26], #v[29, 30], some #v[31, 32]⟩
        (by simp [Row.ports, WordMemory.importedConstraintsMemoryPorts])
    have flag : w 10 = 0 ∨ w 10 = 1 := WordMemory.Proofs.local_flags base 1
    rcases flag with load | store
    · have classification := (WordMemory.Proofs.rom_selection hp false base load
        (address := ⟨(w 19).val, (w 20).val⟩)
        (ZMod.natCast_zmod_val _).symm loadBound).1
      change w 35 = (if (w 20).val < 64 then 1 else 0) at classification
      by_cases inside : (w 20).val < 64
      · have selected : w 35 = 1 := by simpa [inside] using classification
        have one : (1 : ZMod p).val = 1 := by
          rw [ZMod.val_one_eq_one_mod]
          exact Nat.mod_eq_of_lt (by omega)
        have loBound := lt_trans (public_word_bound before
          (Nat.pair 1 (Nat.pair (w 19).val (w 20).val))).1
          (by change 65536 < p; omega)
        have hiBound := lt_trans (public_word_bound before
          (Nat.pair 1 (Nat.pair (w 19).val (w 20).val))).2
          (by change 65536 < p; omega)
        simp [row, load, selected, Row.reads, Row.writes, Row.ports, Row.columns,
          WordMemory.importedConstraintsMemoryPorts, WordMemory.importedConstraintsTraceColumns,
          readToken, writeToken, MemoryAddress.code, MemoryPort.readCode, MemoryPort.writeCode,
          pairCode, rawPair, token, shadow, readData, inside,
          one,
          ZMod.val_natCast_of_lt loBound, ZMod.val_natCast_of_lt hiBound]
      · have selected : w 35 = 0 := by simpa [inside] using classification
        simp [row, load, selected, Row.reads, Row.writes, Row.ports, Row.columns,
          WordMemory.importedConstraintsMemoryPorts, WordMemory.importedConstraintsTraceColumns,
          readToken, writeToken, MemoryAddress.code, MemoryPort.readCode, MemoryPort.writeCode,
          pairCode, token, shadow, inside]
    · have outside := (WordMemory.Proofs.rom_selection hp true base store
        (address := ⟨(w 25).val, (w 26).val⟩)
        (ZMod.natCast_zmod_val _).symm storeBound).2 rfl
      change 64 ≤ (w 26).val at outside
      have notROM : ¬(w 26).val < 64 := by omega
      simp [row, store, Row.reads, Row.writes, Row.ports, Row.columns,
        WordMemory.importedConstraintsMemoryPorts, WordMemory.importedConstraintsTraceColumns,
        readToken, writeToken, MemoryAddress.code, MemoryPort.readCode, MemoryPort.writeCode,
        pairCode, token, shadow, notROM]

def data {p : Nat} [Fact p.Prime] (before : Reference.RiscV.Sail.State)
    (native : Data p) : Data p :=
  { native with
    rows := native.rows.map (row before)
    initialMemory := native.initialMemory.map (token before)
    terminalMemory := native.terminalMemory.map (token before) }

theorem native_clocks {Kind : Type} [CircuitLayout Kind] {p : Nat} [Fact p.Prime] (hp : FieldCapacity.NoWrap p 4)
    {trace : Data p Kind} {cells : List Cell}
    (seed : trace.initialMemory = nativeBootImage cells)
    (initial : trace.initial = PCState.boundary 0 (4, 0)) : ClockBoundary trace := by
  constructor
  · rw [initial]
    change (4 : ZMod p).val < timestampBase ∧ (0 : ZMod p).val < timestampBase
    rw [ZMod.val_ofNat_of_lt hp]
    norm_num [timestampBase]
  · rw [initial]
    change ((4 : ZMod p).val + timestampBase * (0 : ZMod p).val) % 4 = 0
    rw [ZMod.val_ofNat_of_lt hp]
    norm_num
  · intro native member
    rw [seed] at member
    obtain ⟨cell, _, rfl⟩ := List.mem_map.mp member
    simp [Cell.initialToken, timeOfPair, Timestamp.Bounded, timestampBase]

theorem native_addresses {Kind : Type} [CircuitLayout Kind] {p : Nat} [Fact p.Prime]
    [Proofs.ClockLaws Kind p] (hp : FieldCapacity.ClockNoWrap p timestampBase)
    (inverse : SerializedInverse.Clock p) {trace : Data p Kind}
    (accepted : Accepted trace) (clocks : ClockBoundary trace) {cells : List Cell}
    (seed : trace.initialMemory = nativeBootImage cells) :
    ∀ native ∈ trace.rows, ∀ port ∈ native.ports,
      (port.address.word native.assignment).Bounded := by
  intro native member port present
  have initialized := Proofs.initialized_addresses hp inverse accepted clocks native member port present
  rw [seed] at initialized
  have addresses : (nativeBootImage (p := p) cells).map MemoryToken.address =
      cells.map Cell.addressCode := by
    simp [nativeBootImage, List.map_map, Cell.initialToken]
  rw [addresses] at initialized
  obtain ⟨cell, _, equal⟩ := List.mem_map.mp initialized
  rw [Proofs.address_word equal.symm]
  exact Proofs.cell_address_bound cell

theorem accepted {p : Nat} [Fact p.Prime] (hp : FieldCapacity.ClockNoWrap p timestampBase)
    (inverse : SerializedInverse.Clock p)
    (before : Reference.RiscV.Sail.State) {trace : Data p} {cells : List Cell}
    (native : Accepted trace) (clocks : ClockBoundary trace)
    (seed : trace.initialMemory = nativeBootImage cells) : Accepted (data before trace) := by
  have addresses := native_addresses hp inverse native clocks seed
  have transfers : ∀ r ∈ trace.rows,
      (row before r).reads = r.reads.map (token before) ∧
      (row before r).writes = r.writes.map (token before) := by
    intro r member
    exact row_transfers (by unfold timestampBase at hp; omega)
      before r trace.rom (native.constraints r member) (addresses r member)
  constructor
  · intro r member
    change r ∈ trace.rows.map (row before) at member
    obtain ⟨original, inRows, equal⟩ := List.mem_map.mp member
    subst r
    exact row_holds before original trace.rom (native.constraints original inRows)
  · intro r member
    change r ∈ trace.rows.map (row before) at member
    obtain ⟨original, inRows, equal⟩ := List.mem_map.mp member
    subst r
    have active := native.active original inRows
    rcases original with ⟨family, w⟩
    cases family with
    | addSub => exact active
    | wordMemory =>
      dsimp only [row]
      split <;> simpa [Row.columns, WordMemory.importedConstraintsTraceColumns, readData] using active
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

theorem decoded {p : Nat} [Fact p.Prime] (before : Reference.RiscV.Sail.State)
    {trace : Data p} {program : List ProgramEntry} (native : Decoded trace program) :
    Decoded (data before trace) program := by
  intro r member
  change r ∈ trace.rows.map (row before) at member
  obtain ⟨original, inRows, equal⟩ := List.mem_map.mp member
  subst r
  simpa using native original inRows

theorem public_word_read {before : Reference.RiscV.Sail.State} {address value : BitVec 32}
    (read : (Cell.ram address).read before = .ok value before) :
    publicWord before (Cell.ram address).addressCode = Word.ofBitVec value := by
  simp only [publicWord, Cell.addressCode, Nat.unpair_pair]
  change (match (Cell.ram (Word.ofBitVec address).toBitVec).read before with
    | .ok value _ => Word.ofBitVec value
    | .error _ _ => ⟨0, 0⟩) = Word.ofBitVec value
  rw [Word.ofBitVec_roundtrip, read]

theorem shadow_ram (address : BitVec 32) :
    shadow (Cell.ram address).addressCode ↔ address.toNat < ROM.limit := by
  simp only [shadow, Cell.addressCode, Nat.unpair_pair, true_and, Word.ofBitVec]
  change address.toNat / 65536 < 64 ↔ address.toNat < 4194304
  omega

theorem seed_cell {before : Reference.RiscV.Sail.State} {cells : List Cell}
    (profile : InitialProfile before cells) {cell : Cell} (member : cell ∈ cells)
    {value : BitVec 32} (read : cell.read before = .ok value before) :
    token before (cell.initialToken (p := p) 0) = cell.initialToken value := by
  cases cell with
  | register index =>
    have zero : value = 0 := (EStateM.Result.ok.inj (read.symm.trans (profile.registers index))).1
    subst value
    simp [token, shadow, Cell.initialToken, Cell.addressCode]
  | ram address =>
    by_cases inside : address.toNat < ROM.limit
    · have masked := (shadow_ram address).mpr inside
      simp only [token, Cell.initialToken, if_pos masked, public_word_read read]
    · have zero : value = 0 := (EStateM.Result.ok.inj
        (read.symm.trans (profile.ram address member (Nat.le_of_not_gt inside)))).1
      subst value
      have unmasked := mt (shadow_ram address).mp inside
      simp only [token, Cell.initialToken, if_neg unmasked]

theorem seed_image {before : Reference.RiscV.Sail.State} {cells : List Cell}
    {image : List (MemoryToken p)} (profile : InitialProfile before cells)
    (reads : initialImage before cells = some image) :
    (nativeBootImage cells).map (token before) = image := by
  have checked := Proofs.image_reads reads
  clear reads
  induction checked with
  | nil => rfl
  | @cons cell native cells tokens head tail ih =>
    have remaining : InitialProfile before cells :=
      ⟨profile.pc, profile.registers,
        fun address member => profile.ram address (List.mem_cons_of_mem cell member)⟩
    obtain ⟨value, read, rfl⟩ := head
    simp only [nativeBootImage, List.map_cons, List.map_map] at ih ⊢
    rw [ih remaining, seed_cell profile List.mem_cons_self read]

theorem data_clocks {p : Nat} [Fact p.Prime] (before : Reference.RiscV.Sail.State)
    {trace : Data p} (clocks : ClockBoundary trace) : ClockBoundary (data before trace) := by
  refine ⟨clocks.initial, clocks.aligned, ?_⟩
  intro lifted member
  change lifted ∈ trace.initialMemory.map (token before) at member
  obtain ⟨native, present, rfl⟩ := List.mem_map.mp member
  simpa only [token_time] using clocks.memory native present

theorem execution_boundary [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception] {p : Nat} [Fact p.Prime] (hp : FieldCapacity.NoWrap p 4)
    {trace : Data p} {before : Reference.RiscV.Sail.State}
    {cells : List Cell} {program : List ProgramEntry}
    {projection : SailRV32.instruction → Option DecoderData}
    (inputs : NativeBootBoundary trace before cells program projection) :
    ExecutionBoundary (data before trace) before cells program projection := by
  obtain ⟨image, reads, setup⟩ := inputs.rom
  have physical : (data before trace).initialMemory = image := by
    change trace.initialMemory.map (token before) = image
    rw [inputs.seed]
    exact seed_image inputs.profile reads
  refine { toPublicBoundary := inputs.toPublicBoundary
           image := physical.symm ▸ reads
           initialPC := ⟨(4, 0), ?_⟩
           rom := physical.symm ▸ setup
           clocks := data_clocks before (native_clocks hp inputs.seed inputs.initial) }
  change initialState before (4, 0) = some trace.initial
  rw [initialState, inputs.profile.pc, inputs.initial]

end Airbender.Trace.ROMView
