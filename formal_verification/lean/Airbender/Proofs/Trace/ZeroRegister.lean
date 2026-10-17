import Airbender.Proofs.Trace.ZeroValues
import Airbender.Proofs.Trace.DecoderSetup
import Airbender.Proofs.Trace.PublicImage
import Airbender.Proofs.AddSub.Result

namespace Airbender.Trace.Proofs
open Arithmetic

/-- V2 keeps original x0 opcodes and operands. Its decoded zero flag and the
    native mask equations force the actual destination write to zero. -/
theorem row_zero_write_from_reads {p : Nat} [Fact p.Prime] (hp : 32 < p)
    {row : Row p} {entry : ProgramEntry}
    (constraints : FlatOperation.ConstraintsHoldFlat (Verification.environment row.assignment)
      (row.constraints ())) (query : row.decoderQuery = entry.query) :
    RowZeroPreserving row := by
  cases row with
  | mk family w =>
    cases family
    change FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      AddSub.importedConstraints at constraints
    intro port present address reads
    change port ∈ AddSub.importedConstraintsMemoryPorts at present
    simp [AddSub.importedConstraintsMemoryPorts] at present
    rcases present with rfl | rfl | rfl
    · exact reads AddSub.importedConstraintsMemoryPorts[0]
        (by change AddSub.importedConstraintsMemoryPorts[0] ∈ AddSub.importedConstraintsMemoryPorts
            simp [AddSub.importedConstraintsMemoryPorts]) (Nat.le_refl _) address
    · exact reads AddSub.importedConstraintsMemoryPorts[1]
        (by change AddSub.importedConstraintsMemoryPorts[1] ∈ AddSub.importedConstraintsMemoryPorts
            simp [AddSub.importedConstraintsMemoryPorts]) (Nat.le_refl _) address
    · have index := congrArg (fun q : Vector (ZMod p) 10 => q[4]) query
      change w 7 = (entry.data.rd.toNat : ZMod p) at index
      have atZero : (w 7).val = 0 := by
        simpa [AddSub.importedConstraintsMemoryPorts, MemoryAddress.code, pairCode,
          Cell.addressCode, Nat.pair_eq_pair] using address
      have canonical := congrArg ZMod.val index
      rw [ZMod.val_natCast_of_lt (lt_trans entry.data.rd.isLt hp), atZero] at canonical
      have zero : entry.data.rd = 0 := BitVec.eq_of_toNat_eq (by simpa using canonical.symm)
      have flag := congrArg (fun q : Vector (ZMod p) 10 => q[5]) query
      change w 8 = (if entry.data.rd = 0 then 1 else 0) at flag
      rw [if_pos zero] at flag
      have lo := Verification.assertion_of_holds constraints
        ⟨24, by rw [AddSub.Proofs.constraint_count]; decide⟩
      have hi := Verification.assertion_of_holds constraints
        ⟨25, by rw [AddSub.Proofs.constraint_count]; decide⟩
      simp [AddSub.importedConstraints, FlatOperation.constraints, Expression.eval,
        Verification.environment, flag] at lo hi
      have lower : w 37 = 0 := lo
      have upper : w 38 = 0 := hi
      simp [writeToken, MemoryPort.writeCode,
        WordColumns.code, WordColumns.evaluate, lower, upper]
      rfl

/-- Logical decoder membership discharges x0 preservation from native v2 writes;
    no preprocessing-to-NOP rule or caller-supplied zero-value premise is used. -/
theorem decoded_zero_preserving {p : Nat} [Fact p.Prime] (hp : 256 < p)
    {trace : Data p} {setup : DecoderSetup}
    (accepted : Accepted trace) (decoded : Decoded trace setup) : ZeroPreserving trace := by
  intro row member
  obtain ⟨entry, _, query⟩ := decoder_member hp (accepted.constraints row member) (decoded row member)
  exact row_zero_write_from_reads (by omega) (accepted.constraints row member) query

theorem native_zero_writes {p : Nat} [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    {trace : Data p} {setup : DecoderSetup}
    (accepted : Accepted trace) (boundary : ClockBoundary trace)
    {before : Reference.RiscV.Sail.State} {cells : List Cell}
    (image : initialImage before cells = some trace.initialMemory) (decoded : Decoded trace setup) :
    ∀ event ∈ trace.nativeEvents, event.2.1 = (Cell.register 0).addressCode →
      memoryWord event.2.2.2 = 0 :=
  zero_writes_of_preserving hp accepted boundary image
    (decoded_zero_preserving (by dsimp [timestampBase] at hp; omega) accepted decoded)

/-- Public seed reads and accepted native matching derive actual Sail transfers
    and each intermediate Sail state. This does not yet assert instruction execution. -/
theorem image_sail_history {p : Nat} [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    {trace : Data p} {setup : DecoderSetup}
    {before : Reference.RiscV.Sail.State} {cells : List Cell}
    (inputs : ImageBoundary trace before cells) (accepted : Accepted trace)
    (decoded : Decoded trace setup) (aligned : ∀ cell ∈ cells, cell.Aligned) :
    ∃ (history : TimestampSortedMemoryAccessList) (events : List MemoryAccess)
      (seed : TimestampSortedMemoryAccessList) (after : Reference.RiscV.Sail.State),
      MemoryHistory trace history ∧ List.append (α := MemoryAccess) events seed.val = history.val ∧
      events.Perm trace.nativeEvents ∧ SailHistory cells events before after ∧
      SailStateMatches cells history after := by
  have boundary := image_clock_boundary (by dsimp [timestampBase] at hp; omega) inputs
  exact native_sail_history hp accepted boundary inputs.image inputs.domain aligned
    (native_zero_writes hp accepted boundary inputs.image decoded)

end Airbender.Trace.Proofs
