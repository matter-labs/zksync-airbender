import Human.Helpers.Context.Registries.ShiftBinop
import Slop.ShiftBinop.Timestamp
import Slop.ShiftBinop.Decoder
import Slop.Trace.RowHistory

namespace Airbender.ShiftBinop

@[simp] theorem trace_columns (kind : TraceKind) :
    Trace.CircuitLayout.columns kind = importedConstraintsTraceColumns := rfl

@[simp] theorem trace_ports (kind : TraceKind) :
    Trace.CircuitLayout.ports kind = importedConstraintsMemoryPorts := rfl

@[simp] theorem trace_decoder_columns (kind : TraceKind) :
    Trace.CircuitLayout.decoderColumns kind = importedConstraintsDecoderColumns := rfl

@[simp] theorem trace_constraints [Fact p.Prime] (kind : TraceKind)
    (rom : Table (ZMod p) (fields 9)) :
    Trace.CircuitLayout.constraints kind rom = clockConstraints := rfl

end Airbender.ShiftBinop

namespace Airbender.ShiftBinop.Proofs
open Trace

/-- Reuse the complete native path/history engine with imported clock laws. -/
instance nativeClockLaws [Fact p.Prime] : Trace.Proofs.ClockLaws TraceKind p where
  finalBound _ row h := final_clock_bound h
  advance hp inverse _ row h bound := by
    have core := Verification.holds_of_sublist h
      (List.sublist_append_left importedConstraints importedConstraintsTimestampLookups)
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

/-- Both output PC limbs are ranged by imported queries, including the
    terminal boundary. No terminal normalization premise is needed here. -/
theorem outgoing_pc_bounds {p : Nat} [Fact p.Prime]
    {trace : NativeTrace p} (accepted : Accepted trace) :
    ∀ row ∈ trace.rows, row.finish.word.Bounded := by
  intro row member
  have h := Verification.holds_of_sublist (accepted.constraints row member)
    (List.sublist_append_left importedConstraints importedConstraintsTimestampLookups)
  have ranges := local_ranges h
  exact ranges

theorem decoder_nonzero_destination {instruction : SailRV32.instruction}
    {data : Trace.DecoderData Unit} (fields : decoderFields instruction = some data) :
    data.rd ≠ 0 := by
  unfold decoderFields at fields
  split at fields
  all_goals try split at fields
  all_goals try simp only [instructionFields] at fields
  all_goals try split at fields
  all_goals try (simp only [Option.some.injEq] at fields; subst data)
  all_goals simp_all

/-- Readonly x0 accesses refresh zero, and actual decoding rejects x0
    destinations. No x0 read/write compatibility premise is supplied. -/
theorem row_zero_preserving {p : Nat} [Fact p.Prime] (hp : Arithmetic.limbBase < p)
    (row : Row p TraceKind) {before : Reference.RiscV.Sail.State} {entry : ProgramEntry}
    (source : entry.SourceWith before decoderFields) (query : decoderQuery row.assignment = entry.query) :
    Trace.Proofs.RowZeroPreserving row := by
  intro port present address reads
  simp [Row.ports, importedConstraintsMemoryPorts] at present
  rcases present with rfl | rfl | rfl
  · exact reads _ (by simp [Row.ports, importedConstraintsMemoryPorts]) le_rfl address
  · exact reads _ (by simp [Row.ports, importedConstraintsMemoryPorts]) le_rfl address
  · have index := (Trace.Proofs.native_query_indices hp query).2.2
    change (row.assignment 7).val = entry.data.rd.toNat at index
    have nativeZero : (row.assignment 7).val = 0 := by
      change Nat.pair 0 (Nat.pair (row.assignment 7).val 0) = Nat.pair 0 (Nat.pair 0 0) at address
      exact (Nat.pair_eq_pair.mp (Nat.pair_eq_pair.mp address).2).1
    have zero : entry.data.rd = 0 := by
      apply BitVec.eq_of_toNat_eq
      change entry.data.rd.toNat = 0
      exact index.symm.trans nativeZero
    exact (decoder_nonzero_destination source.fields zero).elim

theorem zero_preserving {p : Nat} [Fact p.Prime] (hp : Arithmetic.limbBase < p)
    {trace : NativeTrace p}
    {before : Reference.RiscV.Sail.State} {addresses : List (BitVec 32)}
    {program : List ProgramEntry} (image : programImage before addresses = some program)
    (decoded : Decoded trace program)
    (airbenderConfiguration : Reference.RiscV.Sail.Configured before := by find_configured) : Trace.Proofs.ZeroPreserving trace := by
  intro row member
  obtain ⟨entry, present, _, query⟩ := Trace.Proofs.decoder_member (decoded row member)
  exact row_zero_preserving hp row (Trace.Proofs.run_program_sources image entry present) query

/-- Actual public initialization and native matching produce complete Sail
    register histories, grouped in the clock-derived instruction order. -/
theorem decoded_native_history {p : Nat} [Fact p.Prime]
    (hp : 2 * timestampBase + 4 < p) (inverse : (-3840 : ZMod p) * 524288 = 1)
    {trace : NativeTrace p} (accepted : Accepted trace) (boundary : ClockBoundary trace)
    {before : Reference.RiscV.Sail.State} {cells : List Cell}
    (image : initialImage before cells = some trace.initialMemory)
    (domain : cells.Nodup) (aligned : ∀ cell ∈ cells, cell.Aligned)
    {addresses : List (BitVec 32)} {program : List ProgramEntry}
    (programImage : ShiftBinop.programImage before addresses = some program)
    (decoded : Decoded trace program)
    (airbenderConfiguration : Reference.RiscV.Sail.Configured before := by find_configured) :
    ∃ (history : TimestampSortedMemoryAccessList) (rows : List (Row p TraceKind))
      (after : Reference.RiscV.Sail.State),
      MemoryHistory trace history ∧ rows.Perm trace.rows ∧
      rows.Pairwise (fun a b => b.clock < a.clock) ∧
      Trace.SailHistory cells
        (rows.flatMap fun row => (Trace.rowEvents trace.memoryEpoch row).reverse) before after ∧
      Trace.SailStateMatches cells history after := by
  have preserves := zero_preserving (by dsimp [Arithmetic.limbBase, timestampBase] at *; omega)
    programImage decoded
  exact Trace.Proofs.native_row_history hp inverse accepted boundary image domain aligned
    (Trace.Proofs.zero_writes_of_preserving hp inverse accepted boundary image preserves)


end Airbender.ShiftBinop.Proofs
