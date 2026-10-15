import Airbender.Proofs.Keccak.StateTransport

namespace Airbender.Keccak.Proofs
open Trace Trace.Proofs Delegation.Proofs Arithmetic Reference.RiscV.Sail
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000

theorem scheduled_lane_coverage (physical : Fin 31) :
    ∃ call : Fin 649, ∃ lane : Fin 6,
      (Controller.rows (Fin.ofNat 4096 ((scheduleControl ⟨call.val, by omega⟩).packed + 2048)))[lane] = physical.val := by
  have all : ∀ physical : Fin 31, ∃ call : Fin 649, ∃ lane : Fin 6,
      (Controller.rows (Fin.ofNat 4096 ((scheduleControl ⟨call.val, by omega⟩).packed + 2048)))[lane] = physical.val := by
    decide +kernel
  exact all physical

theorem call_state_cells [Fact p.Prime] (hp : 16777216 ≤ p)
    (inverse : 256 * (-7864320 : ZMod p) = 1)
    {data : Delegation.MemoryData p} {initial : State} {cells : List Cell}
    (accepted : Delegation.MemoryAccepted data) (inputs : BoundaryCallInputs data initial cells)
    (tables : data.setup = Delegation.modeledSetup Controller.rows)
    (aligned : ∀ cell ∈ cells, cell.Aligned) :
    ∃ pointer : BitVec 32, (Cell.register 11).read initial = .ok pointer initial ∧
      ∀ physical : Fin 31, ∀ half : Fin 2,
        Cell.ram (pointer + BitVec.ofNat 32 (8 * physical.val + 4 * half.val)) ∈ cells := by
  obtain ⟨_, schedule, pointer, effects⟩ := call_execution hp inverse accepted inputs tables aligned
  obtain ⟨pointer, read, pointers, _⟩ := pointer
  obtain ⟨ordered, count, permutation, _, controls⟩ := schedule
  have clockBound : 2 * timestampBase + 4 < p := by norm_num [timestampBase]; omega
  refine ⟨pointer, read, ?_⟩
  intro physical half
  obtain ⟨call, lane, coverage⟩ := scheduled_lane_coverage physical
  let row := ordered[call.val]'(by have := call.isLt; omega)
  have member : row ∈ data.rows := permutation.mem_iff.mp (List.getElem_mem _)
  have family := inputs.family row member
  have control : (row.assignment Variables.controlReadLo).val =
      (scheduleControl ⟨call.val, by omega⟩).packed := congrArg Word.lo (controls call).1
  have indices := scheduled_lane_indices call (effects row member) (inputs.active row member) control
  have index : (row.assignment (7 + lane.val)).val = physical.val := (indices lane).trans coverage
  let position : Fin 12 := ⟨2 * lane.val + half.val, by omega⟩
  let port := importedConstraintsMemoryPorts[2 + position.val]'(by change 2 + position.val < 14; omega)
  have present : port ∈ row.ports := by
    rw [Delegation.Row.ports, family]
    exact Array.getElem_mem _
  have shape : port.address = .indirect importedConstraintsIndirectPorts[position] := by
    have all : ∀ i : Fin 12, (importedConstraintsMemoryPorts[2 + i.val]'(by change 2 + i.val < 14; omega)).address =
        .indirect importedConstraintsIndirectPorts[i] := by
      intro i
      fin_cases i <;> rfl
    exact all position
  have tracked := initialized_indirect_cell_at_boundary clockBound accepted inputs.memory member present shape
  rw [(effects row member).addresses.addresses position, pointers row member, Word.ofBitVec_roundtrip] at tracked
  have div : position.val / 2 = lane.val := by dsimp [position]; have := half.isLt; omega
  have mod : position.val % 2 = half.val := by dsimp [position]; have := half.isLt; omega
  simpa only [div, mod, index] using tracked

end Airbender.Keccak.Proofs
