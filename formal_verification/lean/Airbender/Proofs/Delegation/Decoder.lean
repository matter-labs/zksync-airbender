import Airbender.Review.Helpers.Core.FieldCapacity
import Airbender.Review.Helpers.Delegation.Decoder
import Airbender.Proofs.Trace.Program
import Airbender.Proofs.Sail.RiscV
import Airbender.Proofs.AddSub.Selectors
import Airbender.Proofs.Delegation.Requests

namespace Airbender.Delegation.Caller.Proofs
open Trace Arithmetic
set_option warningAsError true

theorem query_csr (hp : FieldCapacity.NoWrap p 65536) {w : Nat → ZMod p} {entry : ProgramEntry}
    (equal : nativeQuery w = query entry) :
    (Requests.caller w).csr = Requests.csr entry.data.family := by
  have field := congrArg (fun values : Vector (ZMod p) 9 => values[3]) equal
  change w 6 = (Requests.csr entry.data.family : ZMod p) at field
  have bound : Requests.csr entry.data.family < p := by
    cases entry.data.family <;> simp only [Requests.csr] <;> omega
  simp [Requests.caller, AddSub.importedConstraintsDecoderColumns,
    field, ZMod.val_natCast_of_lt bound]

theorem query_selected [Fact p.Prime] (hp : FieldCapacity.NoWrap p 65536) {w : Nat → ZMod p}
    {entry : ProgramEntry}
    (constraints : FlatOperation.ConstraintsHoldFlat (Verification.environment w) AddSub.importedConstraints)
    (equal : nativeQuery w = query entry) : Requests.Selected w := by
  have flags := (AddSub.Proofs.local_flags constraints).2
  have boolean : ∀ i : Fin 9, w #[10, 11, 12, 13, 14, 15, 16, 17, 18][i] = 0 ∨
      w #[10, 11, 12, 13, 14, 15, 16, 17, 18][i] = 1 := by
    intro i
    have bit := flags i
    fin_cases i <;> simpa using bit
  have packed := congrArg (fun q : Vector (ZMod p) 9 => q[8]) equal
  change (∑ i : Fin 9, (2 ^ i.val : Nat) * w #[10, 11, 12, 13, 14, 15, 16, 17, 18][i]) =
    (128 : ZMod p) at packed
  have bits := Trace.Proofs.unpack_decoder_bits (by omega) (by decide) boolean packed
  exact bits 7

theorem public_source [Fact p.Prime] {before : Reference.RiscV.Sail.State}
    {addresses : List (BitVec 32)} {program : List ProgramEntry} {w : Nat → ZMod p}
    (image : programImage before addresses = some program)
    (member : (decoderTable program).Contains #[] (nativeQuery w)) :
    ∃ entry ∈ program, entry.SourceWith before decoderFields ∧ nativeQuery w = query entry := by
  change ∃ i : Fin program.length, nativeQuery w = query (program.get i) at member
  obtain ⟨i, equal⟩ := member
  exact ⟨program.get i, List.get_mem _ _,
    Trace.Proofs.run_program_sources image _ (List.get_mem _ _), equal⟩

theorem caller_binding [Fact p.Prime] (hp : FieldCapacity.NoWrap p 65536)
    {before : Reference.RiscV.Sail.State} {addresses : List (BitVec 32)}
    {program : List ProgramEntry} {w : Nat → ZMod p}
    (constraints : FlatOperation.ConstraintsHoldFlat (Verification.environment w) AddSub.importedConstraints)
    (image : programImage before addresses = some program)
    (member : (decoderTable program).Contains #[] (nativeQuery w)) :
    Binding w before program := by
  obtain ⟨entry, entryMember, source, equal⟩ := public_source image member
  have selected := query_selected hp constraints equal
  obtain ⟨read, write, low, high⟩ := Requests.Proofs.caller_tokens constraints selected
  have sourceIndex := congrArg (fun fields : Vector (ZMod p) 9 => fields[2]) equal
  have destinationIndex := congrArg (fun fields : Vector (ZMod p) 9 => fields[4]) equal
  change w 5 = 0 at sourceIndex
  change w 7 = 0 at destinationIndex
  have zero : destination w = ⟨0, 0⟩ := by
    simp [destination, writeToken, MemoryToken.word, MemoryPort.writeCode,
      WordColumns.code, WordColumns.evaluate, AddSub.importedConstraintsMemoryPorts,
      low, high]
  refine ⟨⟨entry, entryMember, source, query_csr hp equal⟩, read, write, zero, ?_, ?_, ?_⟩
  · simp [sourceToken, readToken, AddSub.importedConstraintsMemoryPorts,
      MemoryAddress.code, Cell.addressCode, sourceIndex]
  · simp [destinationToken, writeToken, AddSub.importedConstraintsMemoryPorts,
      MemoryAddress.code, Cell.addressCode, destinationIndex]
  · intro state
    constructor
    · rfl
    · rw [zero]
      change Reference.Sail.run (SailRV32.Functions.wX_bits Reference.RiscV.Sail.zeroRegister 0) state = .ok () state
      rw [Reference.RiscV.Sail.write_zero]
      rfl

end Airbender.Delegation.Caller.Proofs
