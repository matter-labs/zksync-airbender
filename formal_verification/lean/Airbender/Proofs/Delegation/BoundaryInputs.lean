import Airbender.Review.Delegation.Memory
import Airbender.Review.Delegation.Operations
import Airbender.Review.Delegation.BoundaryMemory
import Airbender.Proofs.Trace.TransferBoundary

namespace Airbender.Delegation.Proofs
open Trace Trace.Proofs Reference.RiscV.Sail
set_option warningAsError true

def transferData (data : MemoryData p) : Transfer.Data p :=
  ⟨data.initial, data.terminal, data.steps⟩

structure BoundaryInputs (data : MemoryData p) (before : State) (cells : List Cell) : Prop
    extends Transfer.NativeInputs (transferData data) before cells where
  clockRoom : ∀ row ∈ data.rows,
    (decodeTimestamp row.assignment row.columns.invocation).lo + 2 < timestampBase

structure BoundaryOperationInputs [Fact p.Prime] (data : MemoryData p) (before : State)
    (cells : List Cell) (control : Fin 4096 → Vector Nat 6) : Prop where
  publicState : BoundaryInputs data before cells
  tables : data.setup = modeledSetup control
  rounds : ∀ row ∈ data.rows, row.family = .blakeRound →
    ∃ round, Blake2Round.Memory.RoundMask row.assignment round
  keccakActive : ∀ row ∈ data.rows, row.family = .keccak →
    row.assignment Keccak.Variables.execute = 1

theorem boundary_cell_source {data : MemoryData p} {before : State} {cells : List Cell}
    (inputs : BoundaryInputs data before cells) {cell : Cell} (member : cell ∈ cells) :
    ∃ token ∈ data.initial, ∃ value, cell.read before = .ok value before ∧
      token.address = cell.addressCode ∧ token.word = Arithmetic.Word.ofBitVec value := by
  obtain ⟨token, present, address, read, word⟩ := Transfer.native_cell_source inputs.toNativeInputs member
  exact ⟨token, present, token.word.toBitVec, read, address, word⟩

theorem boundary_readable {data : MemoryData p} {before : State} {cells : List Cell}
    (inputs : BoundaryInputs data before cells) :
    ∀ cell ∈ cells, ∃ value, cell.read before = .ok value before := by
  intro cell member
  obtain ⟨_, _, value, read, _, _⟩ := boundary_cell_source inputs member
  exact ⟨value, read⟩

theorem transfer_boundary_image {data : Transfer.Data p} {before : State} {cells : List Cell}
    (inputs : Transfer.NativeInputs data before cells) : BoundaryImage data.initial before cells := by
  refine ⟨inputs.addresses, ?_⟩
  intro token member
  obtain ⟨cell, present, code, read⟩ := inputs.reads token member
  refine ⟨cell, present, token.word.toBitVec, code, read, ?_⟩
  have bound := inputs.words token member
  apply Arithmetic.Word.eq_of_value bound (Arithmetic.Word.ofBitVec_bound _)
  rw [Arithmetic.Word.ofBitVec_value, Arithmetic.Word.toBitVec_toNat bound]

theorem boundary_image {data : MemoryData p} {before : State} {cells : List Cell}
    (inputs : Transfer.NativeInputs (transferData data) before cells) : BoundaryImage data.initial before cells :=
  transfer_boundary_image inputs

end Airbender.Delegation.Proofs

namespace Airbender.Delegation
open Trace

def MemoryInputs.toBoundaryInputs {data : MemoryData p} {before : Reference.RiscV.Sail.State}
    {cells : List Cell} (inputs : MemoryInputs data before cells) : Proofs.BoundaryInputs data before cells :=
  ⟨(⟨inputs.initialization, inputs.distinct⟩ : Trace.Proofs.Transfer.Inputs _ _ _).toNativeInputs,
    inputs.clockRoom⟩

def OperationInputs.toBoundaryInputs [Fact p.Prime] {data : MemoryData p}
    {before : Reference.RiscV.Sail.State} {cells : List Cell} {control : Fin 4096 → Vector Nat 6}
    (inputs : OperationInputs data before cells control) : Proofs.BoundaryOperationInputs data before cells control :=
  ⟨inputs.publicState.toBoundaryInputs, inputs.tables, inputs.rounds, inputs.keccakActive⟩

def BoundaryMemoryInputs.toBoundaryInputs {data : MemoryData p}
    {before : Reference.RiscV.Sail.State} {cells : List Cell}
    (inputs : BoundaryMemoryInputs data before cells) : Proofs.BoundaryInputs data before cells := by
  refine ⟨⟨⟨inputs.image.addresses, inputs.distinct, ?_⟩, ?_, inputs.clocks⟩, inputs.clockRoom⟩
  · intro token member
    obtain ⟨cell, present, value, code, read, word⟩ := inputs.image.values token member
    refine ⟨cell, present, code, ?_⟩
    change cell.read before = .ok token.word.toBitVec before
    rw [word, Arithmetic.Word.ofBitVec_roundtrip]
    exact read
  · intro token member
    obtain ⟨_, _, value, _, _, word⟩ := inputs.image.values token member
    rw [word]
    exact Arithmetic.Word.ofBitVec_bound value

end Airbender.Delegation
