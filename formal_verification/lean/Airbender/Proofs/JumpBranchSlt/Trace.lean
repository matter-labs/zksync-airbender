import Airbender.Review.JumpBranchSlt.Trace
import Airbender.Proofs.JumpBranchSlt.Timestamp
import Airbender.Proofs.JumpBranchSlt.Decoder
import Airbender.Proofs.Trace.RowHistory
import Airbender.Proofs.Trace.PC
import Airbender.Proofs.Trace.LatestReads
import Airbender.Proofs.Trace.MemoryHistory

namespace Airbender.JumpBranchSlt.Proofs
open Trace

/-- The shared complete-path/latest-read proofs use these checked local laws;
    no jump-specific state or memory consistency premise is added. -/
instance [Fact p.Prime] : Trace.Proofs.ClockLaws TraceKind p where
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

/-- Public decoder membership supplies every incoming PC's canonical limbs.
    It supplies no bound on the unmatched terminal PC. -/
theorem incoming_pc_bounds {p : Nat} [Fact p.Prime] (hp : Arithmetic.limbBase < p)
    {trace : NativeTrace p} {program : List ProgramEntry} (decoded : Decoded trace program) :
    ∀ row ∈ trace.rows, row.start.word.Bounded := by
  intro row member
  obtain ⟨entry, _, _, query⟩ := Trace.Proofs.decoder_member (decoded row member)
  have word : row.start.word = Arithmetic.Word.ofBitVec entry.pc :=
    Trace.Proofs.native_query_pc_word hp query
  rw [word]
  exact Arithmetic.Word.ofBitVec_bound _

/-- Matching discharges all outgoing PC bounds when the external termination
    boundary is canonical. This boundary is not derived from this JSON artifact. -/
theorem trace_pc_bounds {p : Nat} [Fact p.Prime] (hp : Arithmetic.limbBase < p)
    {trace : NativeTrace p} (accepted : Accepted trace) {program : List ProgramEntry}
    (decoded : Decoded trace program) (terminal : trace.terminal.word.Bounded) :
    ∀ row ∈ trace.rows, row.start.word.Bounded ∧ row.finish.word.Bounded := by
  have incoming := incoming_pc_bounds hp decoded
  have outgoing := Trace.Proofs.outgoing_pc_bounds accepted incoming terminal
  exact fun row member => ⟨incoming row member, outgoing row member⟩

/-- The cleanup query enforces a four-byte aligned outgoing low limb for every
    mode. It does not bound the outgoing high limb. -/
theorem outgoing_pc_aligned {p : Nat} [Fact p.Prime] (hp : 4194304 ≤ p)
    {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints) :
    (w 16).val % 4 = 0 := by
  have range := (local_ranges h).2.2.2
  have cleaned := (lookup_values hp h).2.2.2.2
  have small : (w 36).val - (w 36).val % 4 < p := by
    exact lt_of_le_of_lt (Nat.sub_le _ _) (by dsimp [Arithmetic.limbBase] at range; omega)
  rw [cleaned, ZMod.val_natCast, Nat.mod_eq_of_lt small]
  omega

/-- Public initial alignment and native matching discharge every row's PC
    alignment; only the actual public initial state is a boundary condition. -/
theorem trace_pc_alignment {p : Nat} [Fact p.Prime] (hp : 4194304 ≤ p)
    {trace : NativeTrace p} (accepted : Accepted trace)
    (initial : trace.initial.word.lo % 4 = 0) :
    (∀ row ∈ trace.rows, row.start.word.lo % 4 = 0 ∧ row.finish.word.lo % 4 = 0) ∧
      trace.terminal.word.lo % 4 = 0 := by
  have outputs : ∀ row ∈ trace.rows, row.finish.word.lo % 4 = 0 := by
    intro row member
    exact outgoing_pc_aligned hp (Verification.holds_of_sublist (accepted.constraints row member)
      (List.sublist_append_left importedConstraints importedConstraintsTimestampLookups))
  have incoming := Trace.Proofs.matched_incoming_property accepted
    (fun state => state.word.lo % 4 = 0) initial outputs
  refine ⟨?_, incoming _ List.mem_cons_self⟩
  intro row member
  exact ⟨incoming _ (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨row, member, rfl⟩)),
    outputs row member⟩

/-- Sail's projected rd=0 is exactly the native discarded-write branch.
    Comparisons to x0 route to the ADD/SUB NOP family and cannot occur here. -/
theorem decoder_zero_discarded {instruction : SailRV32.instruction}
    {data : Trace.DecoderData Unit} (fields : decoderFields instruction = some data)
    (zero : data.rd = 0) : data.mask.testBit 4 = true := by
  unfold decoderFields at fields
  split at fields
  all_goals try split at fields
  all_goals try (simp only [Option.some.injEq] at fields; subst data)
  all_goals simp_all
  all_goals decide

private theorem zero_destination {p : Nat} [Fact p.Prime] {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints)
    (discarded : w 15 = 1) : w 30 = 0 ∧ w 31 = 0 := by
  have low := Verification.assertion_of_holds h
    ⟨10, by simp [importedConstraints, FlatOperation.constraints]⟩
  have high := Verification.assertion_of_holds h
    ⟨11, by simp [importedConstraints, FlatOperation.constraints]⟩
  simp [importedConstraints, FlatOperation.constraints, Expression.eval,
    Verification.environment, discarded] at low high
  exact ⟨low, high⟩

/-- The public image, actual Sail decoding and imported equations discharge the
    shared local x0 law; no x0 read/write value is supplied as a premise. -/
theorem zero_preserving {p : Nat} [Fact p.Prime] (hp : Arithmetic.limbBase < p)
    {trace : NativeTrace p} (accepted : Accepted trace)
    {before : Reference.RiscV.Sail.State} {addresses : List (BitVec 32)}
    {program : List ProgramEntry} (image : programImage before addresses = some program)
    (decoded : Decoded trace program) : Trace.Proofs.ZeroPreserving trace := by
  intro row member port present address reads
  have h := Verification.holds_of_sublist (accepted.constraints row member)
    (List.sublist_append_left importedConstraints importedConstraintsTimestampLookups)
  have fetch := fetched hp image h (decoded row member)
  simp [Row.ports, importedConstraintsMemoryPorts] at present
  rcases present with rfl | rfl | rfl
  · exact reads _ (by simp [Row.ports, importedConstraintsMemoryPorts]) le_rfl address
  · exact reads _ (by simp [Row.ports, importedConstraintsMemoryPorts]) le_rfl address
  · obtain ⟨entry, source, query, _, _, flags⟩ := fetch
    have index := (Trace.Proofs.native_query_indices hp query).2.2
    change (row.assignment 7).val = entry.data.rd.toNat at index
    have nativeZero : (row.assignment 7).val = 0 := by
      change Nat.pair 0 (Nat.pair (row.assignment 7).val 0) = Nat.pair 0 (Nat.pair 0 0) at address
      exact (Nat.pair_eq_pair.mp (Nat.pair_eq_pair.mp address).2).1
    have zero : entry.data.rd = 0 := by
      apply BitVec.eq_of_toNat_eq
      change entry.data.rd.toNat = 0
      exact index.symm.trans nativeZero
    have mask := decoder_zero_discarded source.fields zero
    have selected : row.assignment 15 = 1 := by
      simpa [importedConstraintsDecoderColumns, mask] using flags ⟨4, by decide⟩
    obtain ⟨low, high⟩ := zero_destination h selected
    simp [writeToken, MemoryPort.writeCode, pairCode, low, high]
    rfl

/-- Complete native histories realized by actual Sail cell reads/writes, grouped
    in the derived instruction order. ISA clause execution is the next layer. -/
theorem decoded_native_history {p : Nat} [Fact p.Prime]
    (hp : 2 * timestampBase + 4 < p) (inverse : (-3840 : ZMod p) * 524288 = 1)
    {trace : NativeTrace p} (accepted : Accepted trace) (boundary : ClockBoundary trace)
    {before : Reference.RiscV.Sail.State} {cells : List Cell}
    (image : initialImage before cells = some trace.initialMemory)
    (domain : cells.Nodup) (aligned : ∀ cell ∈ cells, cell.Aligned)
    {addresses : List (BitVec 32)} {program : List ProgramEntry}
    (programImage : JumpBranchSlt.programImage before addresses = some program)
    (decoded : Decoded trace program) :
    ∃ (history : TimestampSortedMemoryAccessList) (rows : List (Row p TraceKind))
      (after : Reference.RiscV.Sail.State),
      MemoryHistory trace history ∧ rows.Perm trace.rows ∧
      rows.Pairwise (fun a b => b.clock < a.clock) ∧
      Trace.Proofs.SailHistory cells
        (rows.flatMap fun row => (Trace.Proofs.rowEvents trace.memoryEpoch row).reverse) before after ∧
      Trace.Proofs.SailStateMatches cells history after := by
  have preserves := zero_preserving (by dsimp [Arithmetic.limbBase, timestampBase] at *; omega)
    accepted programImage decoded
  exact Trace.Proofs.native_row_history hp inverse accepted boundary image domain aligned
    (Trace.Proofs.zero_writes_of_preserving hp inverse accepted boundary image preserves)

end Airbender.JumpBranchSlt.Proofs
