import Slop.JumpBranchSlt.Trace
import Slop.JumpBranchSlt.Jump
import Slop.JumpBranchSlt.Branch
import Slop.Trace.Values

namespace Airbender.JumpBranchSlt.Proofs
open Arithmetic Trace

private theorem decoder_masks {instruction : SailRV32.instruction}
    {data : DecoderData Unit} (fields : decoderFields instruction = some data) :
    data.mask = 1 ∨ data.mask = 2 ∨ data.mask = 4 ∨
      data.mask = 17 ∨ data.mask = 18 ∨ data.mask = 24 := by
  unfold decoderFields at fields
  split at fields
  all_goals try split at fields
  all_goals try (simp only [Option.some.injEq] at fields; subst data)
  all_goals simp_all

private theorem comparison_destination_bounds {p : Nat} [Fact p.Prime]
    (hp : 4194304 ≤ p) {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints)
    (selected : w 11 = 0 ∧ w 12 = 0 ∧ w 13 = 1 ∧ w 15 = 0) :
    (⟨(w 30).val, (w 31).val⟩ : Word).Bounded := by
  obtain ⟨jal, jalr, comparison, mask⟩ := selected
  have low := Verification.assertion_of_holds h
    ⟨8, by simp [importedConstraints, FlatOperation.constraints]⟩
  have high := Verification.assertion_of_holds h
    ⟨9, by simp [importedConstraints, FlatOperation.constraints]⟩
  have outputLow := Verification.assertion_of_holds h
    ⟨10, by simp [importedConstraints, FlatOperation.constraints]⟩
  have outputHigh := Verification.assertion_of_holds h
    ⟨11, by simp [importedConstraints, FlatOperation.constraints]⟩
  simp [importedConstraints, FlatOperation.constraints, Expression.eval,
    Verification.environment, jal, jalr, comparison] at low high
  have lo : w 47 = w 44 := by linear_combination -low
  have hi : w 48 = 0 := high
  simp [importedConstraints, FlatOperation.constraints, Expression.eval,
    Verification.environment, mask, lo, hi] at outputLow outputHigh
  have written : w 30 = w 44 := by linear_combination -outputLow
  have resolved := (lookup_values hp h).2.2.1
  rw [show w 31 = 0 by exact outputHigh, written, resolved]
  constructor
  · have bounded (bit : Bool) :
        (((if bit then 1 else 0 : Nat) : ZMod p)).val < limbBase := by
      cases bit <;> simp [limbBase, ZMod.val_one'' (by omega : p ≠ 1)]
    exact bounded _
  · simp [limbBase]

/-- Only the decoded native mode and equations establish destination bounds:
    comparisons write a bit, jumps a ranged link, and branches write x0. -/
theorem destination_bounds {p : Nat} [Fact p.Prime] (hp : 4194304 ≤ p)
    {w : Nat → ZMod p} {before : Reference.RiscV.Sail.State}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints)
    (fetch : Fetched w before) (initialLo : (w 0).val < limbBase) :
    (⟨(w 30).val, (w 31).val⟩ : Word).Bounded := by
  obtain ⟨entry, source, _, _, _, flags⟩ := fetch
  have f0 := flags ⟨0, by decide⟩
  have f1 := flags ⟨1, by decide⟩
  have f2 := flags ⟨2, by decide⟩
  have f3 := flags ⟨3, by decide⟩
  have f4 := flags ⟨4, by decide⟩
  rcases decoder_masks source.fields with m | m | m | m | m | m
  all_goals simp [importedConstraintsDecoderColumns, m, Nat.testBit] at f0 f1 f2 f3 f4
  · exact (jump_link hp (initial := ⟨(w 0).val, (w 1).val⟩) h
      (by simp [f0, f1]) ⟨f2, f3⟩ ⟨rfl, rfl⟩ initialLo).2
  · exact (jump_link hp (initial := ⟨(w 0).val, (w 1).val⟩) h
      (by simp [f0, f1]) ⟨f2, f3⟩ ⟨rfl, rfl⟩ initialLo).2
  · exact comparison_destination_bounds hp h ⟨f0, f1, f2, f4⟩
  all_goals
    obtain ⟨low, high⟩ := masked_destination h f4
    simp [low, high, Word.Bounded, limbBase]

/-- The two readonly ports copy their reads; actual decoding and the imported
    equations bound the destination. No source-word bound is supplied here. -/
theorem row_write_sources {p : Nat} [Fact p.Prime] (hp : 4194304 ≤ p)
    (row : Row p TraceKind)
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment row.assignment) importedConstraints)
    {before : Reference.RiscV.Sail.State} (fetch : Fetched row.assignment before)
    (initialLo : (row.assignment 0).val < limbBase) : Trace.Proofs.RowWriteSources row := by
  intro port present
  simp [Row.ports, importedConstraintsMemoryPorts] at present
  rcases present with rfl | rfl | rfl
  · exact Or.inr ⟨_, by simp [Row.ports, importedConstraintsMemoryPorts], rfl, le_rfl⟩
  · exact Or.inr ⟨_, by simp [Row.ports, importedConstraintsMemoryPorts], rfl, le_rfl⟩
  · left
    simpa [Trace.Proofs.write_word, importedConstraintsMemoryPorts] using
      destination_bounds hp h fetch initialLo

theorem write_sources {p : Nat} [Fact p.Prime] (hp : 4194304 ≤ p)
    {trace : NativeTrace p} (accepted : Accepted trace)
    {before : Reference.RiscV.Sail.State} {addresses : List (BitVec 32)}
    {program : List ProgramEntry} (image : programImage before addresses = some program)
    (decoded : Decoded trace program) : Trace.Proofs.WriteSources trace := by
  intro row member
  have h := Verification.holds_of_sublist (accepted.constraints row member)
    (List.sublist_append_left importedConstraints importedConstraintsTimestampLookups)
  exact row_write_sources hp row h (fetched (by dsimp [limbBase]; omega) image h (decoded row member))
    (incoming_pc_bounds (by dsimp [limbBase]; omega) decoded row member).1

/-- Native history derives all operand, write and terminal-register ranges from
    the actual public Sail image. Canonical terminal PC remains a separate issue. -/
theorem native_value_bounds {p : Nat} [Fact p.Prime]
    (hp : 4194304 ≤ p) (inverse : (-3840 : ZMod p) * 524288 = 1)
    {trace : NativeTrace p} (accepted : Accepted trace) (clocks : ClockBoundary trace)
    {before : Reference.RiscV.Sail.State} {cells : List Cell}
    (image : initialImage before cells = some trace.initialMemory)
    {addresses : List (BitVec 32)} {program : List ProgramEntry}
    (programImage : JumpBranchSlt.programImage before addresses = some program)
    (decoded : Decoded trace program) :
    (∀ row ∈ trace.rows, ∀ port ∈ row.ports, (readToken row.assignment port).word.Bounded) ∧
      (∀ row ∈ trace.rows, ∀ port ∈ row.ports,
        (writeToken row.columns row.assignment port).word.Bounded) ∧
      (∀ token ∈ trace.terminalMemory, token.word.Bounded) := by
  have sources := write_sources hp accepted programImage decoded
  have clockField : 2 * timestampBase + 4 < p := by dsimp [timestampBase]; omega
  have seed := Trace.Proofs.image_bounds image
  exact ⟨Trace.Proofs.read_bounds_of_sources clockField inverse accepted clocks seed sources,
    Trace.Proofs.write_bounds_of_sources clockField inverse accepted clocks seed sources,
    Trace.Proofs.terminal_bounds_of_sources clockField inverse accepted clocks seed sources⟩

end Airbender.JumpBranchSlt.Proofs
