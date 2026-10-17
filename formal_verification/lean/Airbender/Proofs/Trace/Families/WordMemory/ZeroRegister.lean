import Airbender.Proofs.Trace.Families.WordMemory.Values
import Airbender.Proofs.Trace.ZeroValues
import Airbender.Proofs.Trace.RowHistory

namespace Airbender.WordMemory.Proofs
open Arithmetic Trace Verification

/-- Readonly ports copy their prior x0 value. The mixed final port either writes
    RAM or uses the decoded rd and native load mask; stores cannot target x0. -/
theorem row_zero_write_from_reads {p : Nat} [Fact p.Prime] (hp : 4194304 < p)
    {rom : WordROM} {row : Row p WordMemoryFamily} {entry : ProgramEntry WordMemoryFamily}
    (native : FlatOperation.ConstraintsHoldFlat (environment row.assignment) (row.constraints rom))
    (query : row.decoderQuery = entry.query) : Trace.Proofs.RowZeroPreserving row := by
  cases row with
  | mk family w =>
    cases family
    intro port present address reads
    change port ∈ importedConstraintsMemoryPorts at present
    simp [importedConstraintsMemoryPorts] at present
    rcases present with rfl | rfl | rfl
    · exact reads importedConstraintsMemoryPorts[0]
        (by change _ ∈ importedConstraintsMemoryPorts; simp [importedConstraintsMemoryPorts])
        (le_refl _) address
    · exact reads importedConstraintsMemoryPorts[1]
        (by change _ ∈ importedConstraintsMemoryPorts; simp [importedConstraintsMemoryPorts])
        (le_refl _) address
    · have effects := transfers hp native
      rcases effects.storeBit with load | store
      · change w 12 = 0 at load
        have space : w 32 = 1 := by simpa only [load, sub_zero] using effects.writeAddress.1
        have target : w 33 = w 7 := by
          simpa only [load, zero_mul, sub_zero, one_mul, zero_add] using effects.writeAddress.2.1
        have upper : w 34 = 0 := by simpa only [load, zero_mul] using effects.writeAddress.2.2
        have atZero : (w 7).val = 0 := by
          simpa [MemoryAddress.code, pairCode, Cell.addressCode, Nat.pair_eq_pair,
            space, target, upper] using address
        have index := congrArg (fun q : Vector (ZMod p) 10 => q[4]) query
        change w 7 = (entry.data.rd.toNat : ZMod p) at index
        have canonical := congrArg ZMod.val index
        rw [ZMod.val_natCast_of_lt (lt_trans entry.data.rd.isLt (by omega)), atZero] at canonical
        have zero : entry.data.rd = 0 := BitVec.eq_of_toNat_eq (by simpa using canonical.symm)
        have flag := congrArg (fun q : Vector (ZMod p) 10 => q[5]) query
        change w 8 = (if entry.data.rd = 0 then 1 else 0) at flag
        rw [if_pos zero] at flag
        have value := effects.load load
        simp only [flag, sub_self, zero_mul] at value
        simp [writeToken, MemoryPort.writeCode, WordColumns.code,
          WordColumns.evaluate, value.1, value.2]
        rfl
      · change w 12 = 1 at store
        have space : w 32 = 0 := by simpa only [store, sub_self] using effects.writeAddress.1
        simp [MemoryAddress.code, Cell.addressCode, Nat.pair_eq_pair, space] at address

/-- Full padded decoder membership supplies the exact x0 flag; no local zero
    answer or source-style NOP projection is assumed. -/
theorem decoded_zero_preserving {p : Nat} [Fact p.Prime] (hp : 4194304 < p)
    {trace : Data p WordMemoryFamily} {setup : DecoderSetup}
    (accepted : Accepted trace) (decoded : Decoded trace setup) : Trace.Proofs.ZeroPreserving trace := by
  intro row member
  obtain ⟨entry, _, query⟩ := decoder_member (by omega)
    (accepted.constraints row member) (decoded row member)
  exact row_zero_write_from_reads hp (accepted.constraints row member) query

theorem native_zero_writes {p : Nat} [Fact p.Prime] (hp : 4194304 < p)
    {trace : Data p WordMemoryFamily} {setup : DecoderSetup}
    (accepted : Accepted trace) (boundary : ClockBoundary trace)
    {before : Reference.RiscV.Sail.State} {cells : List Cell}
    (image : initialImage before cells = some trace.initialMemory) (decoded : Decoded trace setup) :
    ∀ event ∈ trace.nativeEvents, event.2.1 = (Cell.register 0).addressCode →
      memoryWord event.2.2.2 = 0 :=
  Trace.Proofs.zero_writes_of_preserving (by dsimp [timestampBase]; omega)
    accepted boundary image (decoded_zero_preserving hp accepted decoded)

/-- Shared Clean-to-Sail realization and clock-derived grouping, instantiated
    for every native word-memory port. The public image still tracks the full
    native RAM domain, including ROM shadows; architectural projection is separate. -/
theorem image_row_history {p : Nat} [Fact p.Prime] (hp : 4194304 < p)
    {trace : Data p WordMemoryFamily} {setup : DecoderSetup}
    {before : Reference.RiscV.Sail.State} {cells : List Cell}
    (inputs : ImageBoundary trace before cells) (accepted : Accepted trace)
    (decoded : Decoded trace setup) (aligned : ∀ cell ∈ cells, cell.Aligned) :
    ∃ (history : TimestampSortedMemoryAccessList) (rows : List (Row p WordMemoryFamily))
      (after : Reference.RiscV.Sail.State),
      MemoryHistory trace history ∧ rows.Perm trace.rows ∧
      rows.Pairwise (fun a b => b.clock < a.clock) ∧
      SailHistory cells (rows.flatMap fun row => (rowEvents trace.memoryEpoch row).reverse)
        before after ∧ SailStateMatches cells history after := by
  have boundary := Trace.Proofs.image_clock_boundary (by omega) inputs
  exact Trace.Proofs.native_row_history (by dsimp [timestampBase]; omega)
    accepted boundary inputs.image inputs.domain aligned
    (native_zero_writes hp accepted boundary inputs.image decoded)

end Airbender.WordMemory.Proofs
