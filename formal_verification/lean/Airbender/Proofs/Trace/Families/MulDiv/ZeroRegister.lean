import Airbender.Proofs.Trace.ZeroValues
import Airbender.Proofs.Trace.Families.MulDiv.Decoder
import Airbender.Proofs.Trace.Families.MulDiv.History
import Airbender.Proofs.Trace.RowHistory
import Airbender.Proofs.Trace.PublicImage

namespace Airbender.MulDiv.Proofs
open Arithmetic Trace Verification
open Airbender.Trace.Proofs

/-- V2 keeps original x0 opcodes and operands. Its decoded zero flag and the
    native mask equations force the actual destination write to zero. -/
theorem row_zero_write_from_reads {p : Nat} [Fact p.Prime] (hp : 32 < p)
    {row : Row p MulDivFamily} {entry : ProgramEntry}
    (constraints : FlatOperation.ConstraintsHoldFlat (Verification.environment row.assignment)
      (row.constraints ())) (query : row.decoderQuery = entry.query) :
    RowZeroPreserving row := by
  cases row with
  | mk family w =>
    cases family
    change FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      importedConstraints at constraints
    intro port present address reads
    change port ∈ importedConstraintsMemoryPorts at present
    simp [importedConstraintsMemoryPorts] at present
    rcases present with rfl | rfl | rfl
    · exact reads importedConstraintsMemoryPorts[0]
        (by change importedConstraintsMemoryPorts[0] ∈ importedConstraintsMemoryPorts
            simp [importedConstraintsMemoryPorts]) (Nat.le_refl _) address
    · exact reads importedConstraintsMemoryPorts[1]
        (by change importedConstraintsMemoryPorts[1] ∈ importedConstraintsMemoryPorts
            simp [importedConstraintsMemoryPorts]) (Nat.le_refl _) address
    · have index := congrArg (fun q : Vector (ZMod p) 10 => q[4]) query
      change w 7 = (entry.data.rd.toNat : ZMod p) at index
      have atZero : (w 7).val = 0 := by
        simpa [importedConstraintsMemoryPorts, MemoryAddress.code, pairCode,
          Cell.addressCode, Nat.pair_eq_pair] using address
      have canonical := congrArg ZMod.val index
      rw [ZMod.val_natCast_of_lt (lt_trans entry.data.rd.isLt hp), atZero] at canonical
      have zero : entry.data.rd = 0 := BitVec.eq_of_toNat_eq (by simpa using canonical.symm)
      have flag := congrArg (fun q : Vector (ZMod p) 10 => q[5]) query
      change w 8 = (if entry.data.rd = 0 then 1 else 0) at flag
      rw [if_pos zero] at flag
      have lo := assertion_of_holds constraints ⟨35, by rw [constraint_count]; decide⟩
      have hi := assertion_of_holds constraints ⟨36, by rw [constraint_count]; decide⟩
      simp [importedConstraints, FlatOperation.constraints, Expression.eval,
        environment, flag] at lo hi
      have lower : w 60 = 0 := by exact lo
      have upper : w 61 = 0 := by exact hi
      simp [writeToken, MemoryPort.writeCode,
        WordColumns.code, WordColumns.evaluate, lower, upper]
      rfl

/-- Logical decoder membership discharges x0 preservation from native v2 writes;
    no preprocessing-to-NOP rule or caller-supplied zero-value premise is used. -/
theorem decoded_zero_preserving {p : Nat} [Fact p.Prime] (hp : 256 < p)
    {trace : Data p MulDivFamily} {setup : SparseDecoderSetup Operation}
    (accepted : Accepted trace) (decoded : Decoded trace setup) : ZeroPreserving trace := by
  intro row member
  obtain ⟨entry, _, query⟩ := decoder_member (by omega) (accepted.constraints row member)
    (by simpa only [row_decoder_query] using decoded row member)
  exact row_zero_write_from_reads (by omega) (accepted.constraints row member)
    (by simpa only [row_decoder_query] using query)

theorem native_zero_writes {p : Nat} [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    {trace : Data p MulDivFamily} {setup : SparseDecoderSetup Operation}
    (accepted : Accepted trace) (boundary : ClockBoundary trace)
    {before : Reference.RiscV.Sail.State} {cells : List Cell}
    (image : initialImage before cells = some trace.initialMemory) (decoded : Decoded trace setup) :
    ∀ event ∈ trace.nativeEvents, event.2.1 = (Cell.register 0).addressCode →
      memoryWord event.2.2.2 = 0 :=
  zero_writes_of_preserving hp accepted boundary image
    (decoded_zero_preserving (by dsimp [timestampBase] at hp; omega) accepted decoded)

/-- Clock-derived grouping and the unchanged shared Clean-to-Sail realization
    derive all intermediate cell states, including discarded x0 writes. -/
theorem image_row_history {p : Nat} [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    {trace : Data p MulDivFamily} {setup : SparseDecoderSetup Operation}
    {before : Reference.RiscV.Sail.State} {cells : List Cell}
    (inputs : ImageBoundary trace before cells) (accepted : Accepted trace)
    (decoded : Decoded trace setup) (aligned : ∀ cell ∈ cells, cell.Aligned) :
    ∃ (history : TimestampSortedMemoryAccessList) (rows : List (Row p MulDivFamily))
      (after : Reference.RiscV.Sail.State),
      MemoryHistory trace history ∧ rows.Perm trace.rows ∧
      rows.Pairwise (fun a b => b.clock < a.clock) ∧
      SailHistory cells (rows.flatMap fun row => (rowEvents trace.memoryEpoch row).reverse)
        before after ∧ SailStateMatches cells history after := by
  have boundary := image_clock_boundary (by dsimp [timestampBase] at hp; omega) inputs
  exact native_row_history hp accepted boundary inputs.image inputs.domain aligned
    (native_zero_writes hp accepted boundary inputs.image decoded)

end Airbender.MulDiv.Proofs
