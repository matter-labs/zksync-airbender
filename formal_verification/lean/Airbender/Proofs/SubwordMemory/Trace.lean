import Airbender.Review.Helpers.Registries.SubwordMemory
import Airbender.Proofs.SubwordMemory.Timestamp
import Airbender.Proofs.SubwordMemory.Decoder
import Airbender.Proofs.Trace.RowHistory

namespace Airbender.SubwordMemory

@[simp] theorem trace_columns (kind : TraceKind) :
    Trace.CircuitLayout.columns kind = importedConstraintsTraceColumns := rfl

@[simp] theorem trace_ports (kind : TraceKind) :
    Trace.CircuitLayout.ports kind = importedConstraintsMemoryPorts := rfl

@[simp] theorem trace_decoder_columns (kind : TraceKind) :
    Trace.CircuitLayout.decoderColumns kind = importedConstraintsDecoderColumns := rfl

@[simp] theorem trace_constraints [Fact p.Prime] (kind : TraceKind)
    (rom : Table (ZMod p) (fields 9)) :
    Trace.CircuitLayout.constraints kind rom = clockConstraints rom := rfl

end Airbender.SubwordMemory

namespace Airbender.SubwordMemory.Proofs
open Trace

/-- Reuse the complete native path/history engine with imported clock laws. -/
instance nativeClockLaws [Fact p.Prime] : Trace.Proofs.ClockLaws TraceKind p where
  finalBound _ row h := final_clock_bound h
  advance hp inverse setup row h bound := by
    have core := Verification.holds_of_sublist h
      (List.sublist_append_left (importedConstraints setup) importedConstraintsTimestampLookups)
    obtain ⟨carry, bit, low, high⟩ := timestamp_equations inverse core
    have final := final_clock_bound h
    apply Trace.Proofs.increment hp bound final bit
    · simpa [Row.columns, importedConstraintsTraceColumns, decodeTimestamp, timestampBase,
        ZMod.natCast_zmod_val] using low
    · simpa [Row.columns, importedConstraintsTraceColumns, decodeTimestamp, timestampBase,
        ZMod.natCast_zmod_val] using high
  portsClocks _ := memory_clocks
  offsets _ := rfl
  effects hp inverse _ _ h inputs := clocks hp inverse h inputs

theorem incoming_pc_bounds {p : Nat} [Fact p.Prime] (hp : Arithmetic.limbBase < p)
    {trace : NativeTrace p} {program : List ProgramEntry} (decoded : Decoded trace program) :
    ∀ row ∈ trace.rows, row.start.word.Bounded := by
  intro row member
  obtain ⟨entry, _, _, query⟩ := Trace.Proofs.decoder_member (decoded row member)
  have word : row.start.word = Arithmetic.Word.ofBitVec entry.pc :=
    Trace.Proofs.native_query_pc_word hp query
  rw [word]
  exact Arithmetic.Word.ofBitVec_bound _

theorem outgoing_pc_bounds {p : Nat} [Fact p.Prime]
    {trace : NativeTrace p} (accepted : Accepted trace) :
    ∀ row ∈ trace.rows, row.finish.word.Bounded := by
  intro row member
  have core := Verification.holds_of_sublist (accepted.constraints row member)
    (List.sublist_append_left (importedConstraints trace.rom) importedConstraintsTimestampLookups)
  have ranges := local_ranges core
  exact ⟨ranges.2.2.2.1, ranges.2.2.2.2⟩

/-- Readonly ports refresh x0. Public decoding excludes load writes to x0,
    and the native RAM tag separates stores from every register address. -/
theorem row_zero_preserving {p : Nat} [Fact p.Prime] (hp : Arithmetic.limbBase < p)
    (row : Row p TraceKind) (setup : Table (ZMod p) (fields 9))
    (core : FlatOperation.ConstraintsHoldFlat (Verification.environment row.assignment) (importedConstraints setup))
    {before : Reference.RiscV.Sail.State} {entry : ProgramEntry}
    (source : entry.SourceWith before decoderFields) (query : decoderQuery row.assignment = entry.query) :
    Trace.Proofs.RowZeroPreserving row := by
  intro port present address reads
  simp [Row.ports, importedConstraintsMemoryPorts] at present
  rcases present with rfl | rfl | rfl
  · exact reads _ (by simp [Row.ports, importedConstraintsMemoryPorts]) le_rfl address
  · exact reads _ (by simp [Row.ports, importedConstraintsMemoryPorts]) le_rfl address
  · have flag := decoder_selectors hp core (decoder_field_bounds source.fields).2.1 query 0
    change row.assignment 10 = (if entry.data.mask.testBit 0 then 1 else 0) at flag
    change Nat.pair (row.assignment 10).val
      (Nat.pair (row.assignment 27).val (row.assignment 28).val) =
      Nat.pair 0 (Nat.pair 0 0) at address
    cases store : entry.data.mask.testBit 0
    · have selected : row.assignment 10 = 0 := by simpa only [store, Bool.false_eq_true, if_false] using flag
      have register := register_address false core selected
      simp only [Bool.false_eq_true, if_false] at register
      have index := (Trace.Proofs.native_query_indices hp query).2.2
      change (row.assignment 7).val = entry.data.rd.toNat at index
      rw [selected, ZMod.val_zero] at address
      have zeroLo := (Nat.pair_eq_pair.mp (Nat.pair_eq_pair.mp address).2).1
      rw [register.1] at zeroLo
      have zero : entry.data.rd = 0 := by
        apply BitVec.eq_of_toNat_eq
        exact index.symm.trans zeroLo
      exact (decoder_load_nonzero source.fields store zero).elim
    · have selected : row.assignment 10 = 1 := by simpa only [store, if_true] using flag
      simp [selected, ZMod.val_one] at address

theorem zero_preserving {p : Nat} [Fact p.Prime] (hp : Arithmetic.limbBase < p)
    {trace : NativeTrace p} (accepted : Accepted trace)
    {before : Reference.RiscV.Sail.State} {addresses : List (BitVec 32)} {program : List ProgramEntry}
    (image : programImage before addresses = some program) (decoded : Decoded trace program) :
    Trace.Proofs.ZeroPreserving trace := by
  intro row member
  obtain ⟨entry, present, _, query⟩ := Trace.Proofs.decoder_member (decoded row member)
  have core := Verification.holds_of_sublist (accepted.constraints row member)
    (List.sublist_append_left (importedConstraints trace.rom) importedConstraintsTimestampLookups)
  exact row_zero_preserving hp row trace.rom core
    (Trace.Proofs.run_program_sources image entry present) query

/-- Public initialization and native latest-write matching derive exact x0
    tokens; no zero-read compatibility premise is added to the circuit. -/
theorem native_zero_reads {p : Nat} [Fact p.Prime]
    (hp : 2 * timestampBase + 4 < p) (inverse : (-3840 : ZMod p) * 524288 = 1)
    {trace : NativeTrace p} (accepted : Accepted trace) (boundary : ClockBoundary trace)
    {before : Reference.RiscV.Sail.State} {cells : List Cell}
    (image : initialImage before cells = some trace.initialMemory)
    {addresses : List (BitVec 32)} {program : List ProgramEntry}
    (programImage : SubwordMemory.programImage before addresses = some program)
    (decoded : Decoded trace program) :
    ∀ row ∈ trace.rows, ∀ port ∈ row.ports,
      port.address.code row.assignment = (Cell.register 0).addressCode →
      (readToken row.assignment port).value = 0 :=
  Trace.Proofs.zero_reads_of_preserving hp inverse accepted boundary image
    (zero_preserving (by dsimp [timestampBase, Arithmetic.limbBase] at *; omega)
      accepted programImage decoded)

/-- Public cell extraction, native matching and decoded x0 preservation give
    grouped Sail histories in native instruction order. ROM shadow transport
    needs its separate public-image binding before complete ISA composition. -/
theorem decoded_native_history {p : Nat} [Fact p.Prime]
    (hp : 2 * timestampBase + 4 < p) (inverse : (-3840 : ZMod p) * 524288 = 1)
    {trace : NativeTrace p} (accepted : Accepted trace) (boundary : ClockBoundary trace)
    {before : Reference.RiscV.Sail.State} {cells : List Cell}
    (image : initialImage before cells = some trace.initialMemory)
    (domain : cells.Nodup) (aligned : ∀ cell ∈ cells, cell.Aligned)
    {addresses : List (BitVec 32)} {program : List ProgramEntry}
    (programImage : SubwordMemory.programImage before addresses = some program)
    (decoded : Decoded trace program) :
    ∃ (history : TimestampSortedMemoryAccessList) (rows : List (Row p TraceKind))
      (after : Reference.RiscV.Sail.State),
      MemoryHistory trace history ∧ rows.Perm trace.rows ∧
      rows.Pairwise (fun a b => b.clock < a.clock) ∧
      Trace.SailHistory cells
        (rows.flatMap fun row => (Trace.rowEvents trace.memoryEpoch row).reverse) before after ∧
      Trace.SailStateMatches cells history after := by
  have preserves := zero_preserving (by dsimp [Arithmetic.limbBase, timestampBase] at *; omega)
    accepted programImage decoded
  exact Trace.Proofs.native_row_history hp inverse accepted boundary image domain aligned
    (Trace.Proofs.zero_writes_of_preserving hp inverse accepted boundary image preserves)

end Airbender.SubwordMemory.Proofs
