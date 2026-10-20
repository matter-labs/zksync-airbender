import Slop.Blake2Round.CallCompression

namespace Airbender.Blake2Round.Proofs
open Trace Trace.Proofs Delegation.Proofs Arithmetic Reference.RiscV.Sail
set_option warningAsError true
set_option maxRecDepth 16384

private theorem encoded_read {state : State} {address : BitVec 32}
    (readable : ∃ value, (Cell.ram address).read state = .ok value state) :
    (Cell.ram address).read state = .ok (ramEncoding state address).toBitVec state := by
  obtain ⟨value, read⟩ := readable
  have bits : (ramEncoding state address).toBitVec = value := by
    rw [ramEncoding, Word.ofBitVec_roundtrip, ram_word_of_read read]
    simp
  simpa only [bits] using read

theorem block_at {state : State} {cells : List Cell} {pointer : BitVec 32} {n offset : Nat}
    (tracked : ∀ i : Fin n, Cell.ram (pointer + BitVec.ofNat 32 (4 * (offset + i.val))) ∈ cells)
    (readable : ∀ cell ∈ cells, ∃ value, cell.read state = .ok value state) :
    Compression.WordsAt state pointer offset (blockWords state pointer n offset) := by
  intro i
  simp only [blockWords, Fin.getElem_fin, Vector.getElem_ofFn]
  constructor
  · exact Word.ofBitVec_bound (BitVec.ofNat 32 (ramWord state
      (pointer + BitVec.ofNat 32 (4 * (offset + i.val)))))
  · exact encoded_read (readable _ (tracked i))

theorem compression_binding_at_boundary [Fact p.Prime] (hp : 8388608 ≤ p)
    (inverse : 64 * (-31457280 : ZMod p) = 1)
    {data : Delegation.MemoryData p} {initial : State} {cells : List Cell} {flags : Fin 8}
    (accepted : Delegation.MemoryAccepted data) (inputs : BoundaryCallInputs data initial cells flags)
    (aligned : ∀ cell ∈ cells, cell.Aligned) :
    ∃ (after : State) (statePointer messagePointer : BitVec 32)
      (input : Compression.State) (message : Vector Word 16) (output : Compression.State),
      Compression.WordMapping initial after statePointer messagePointer input output message ∧
        Delegation.TraceMapping data initial after cells ∧
        output = Compression.run flags input message := by
  obtain ⟨statePointer, messagePointer, after, stateRead, messageRead, trace, afterReadable, result⟩ :=
    call_compression hp inverse accepted inputs aligned
  obtain ⟨otherState, otherMessage, otherStateRead, otherMessageRead, tracked⟩ :=
    call_block_cells hp inverse accepted inputs aligned
  have sameState := (EStateM.Result.ok.inj (otherStateRead.symm.trans stateRead)).1
  have sameMessage := (EStateM.Result.ok.inj (otherMessageRead.symm.trans messageRead)).1
  subst otherState
  subst otherMessage
  have initialReadable := boundary_readable inputs.memory
  have stateTracked : ∀ i : Fin 8, Cell.ram (statePointer + BitVec.ofNat 32 (4 * (0 + i.val))) ∈ cells := by
    intro i
    have actual := tracked ⟨i.val, by omega⟩
    simpa only [Fin.val_mk, ite_eq_left (show i.val < 24 by omega), Nat.zero_add] using actual
  have extendedTracked : ∀ i : Fin 16, Cell.ram (statePointer + BitVec.ofNat 32 (4 * (8 + i.val))) ∈ cells := by
    intro i
    have actual := tracked ⟨8 + i.val, by omega⟩
    simpa only [Fin.val_mk, ite_eq_left (show 8 + i.val < 24 by omega)] using actual
  have messageTracked : ∀ i : Fin 16, Cell.ram (messagePointer + BitVec.ofNat 32 (4 * (0 + i.val))) ∈ cells := by
    intro i
    have actual := tracked ⟨24 + i.val, by omega⟩
    simpa only [Fin.val_mk, ite_eq_right (show ¬ 24 + i.val < 24 by omega), Nat.add_sub_cancel_left,
      Nat.zero_add] using actual
  refine ⟨after, statePointer, messagePointer, physicalState initial statePointer,
    blockWords initial messagePointer 16 0, physicalState after statePointer, ?_, trace, result⟩
  exact ⟨⟨stateRead, messageRead⟩, block_at stateTracked initialReadable,
    block_at extendedTracked initialReadable, block_at messageTracked initialReadable,
    block_at stateTracked afterReadable, block_at extendedTracked afterReadable⟩

theorem compression_binding [Fact p.Prime] (hp : 8388608 ≤ p)
    (inverse : 64 * (-31457280 : ZMod p) = 1)
    {data : Delegation.MemoryData p} {initial : State} {cells : List Cell} {flags : Fin 8}
    (accepted : Delegation.MemoryAccepted data) (inputs : CallInputs data initial cells flags)
    (aligned : ∀ cell ∈ cells, cell.Aligned) :
    ∃ (after : State) (statePointer messagePointer : BitVec 32)
      (input : Compression.State) (message : Vector Word 16) (output : Compression.State),
      Compression.WordMapping initial after statePointer messagePointer input output message ∧
        Delegation.TraceMapping data initial after cells ∧
        output = Compression.run flags input message :=
  compression_binding_at_boundary hp inverse accepted inputs.toBoundaryInputs aligned

end Airbender.Blake2Round.Proofs
