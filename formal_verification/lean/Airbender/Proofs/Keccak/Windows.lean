import Airbender.Review.Helpers.Core.FieldCapacity
import Airbender.Review.Helpers.Core.SerializedInverse
import Airbender.Review.Trace.Workers.Keccak.Windows
import Airbender.Proofs.Keccak.PermutationBinding
import Airbender.Proofs.Keccak.MemorySoundness
import Airbender.Proofs.Delegation.HashWindowTransport

namespace Airbender.Keccak.Proofs
open Trace Trace.Proofs Arithmetic Reference.RiscV.Sail Delegation.Proofs
set_option warningAsError true
set_option maxRecDepth 16384

theorem window_binding [Fact p.Prime] (hp : FieldCapacity.NativeWideHashCapacity p)
    (inverse : SerializedInverse.Scale256 p)
    {data : Delegation.MemoryData p} {before : State} {cells : List Cell} {lower upper : Nat}
    (accepted : Delegation.MemoryAccepted data) (inputs : WindowInputs data before cells lower upper)
    (aligned : ∀ cell ∈ cells, cell.Aligned) :
    Delegation.Caller.HashSpan.keccak.WindowResult data before cells lower upper := by
  have size : 2 * timestampBase + 4 < p := by norm_num [timestampBase]; omega
  have memoryInputs : BoundaryMemoryInputs data before cells Controller.rows :=
    ⟨inputs.memory.toBoundaryInputs, inputs.family, by rw [inputs.tables]; rfl, inputs.active⟩
  have rules := Memory.Proofs.memory_rules_at_boundary (by omega) accepted memoryInputs
  obtain ⟨start, finish, earlierEvents, spanEvents, atStart, atFinish, _,
      selectedAccepted, earlierPerm, spanPerm, earlierHistory, spanHistory, startInputs, finishInputs⟩ :=
    native_span_window_at_boundary size accepted inputs.memory.toBoundaryInputs rules aligned lower upper
  have same := empty_prefix_state inputs.prefixEmpty earlierPerm earlierHistory
  subst atStart
  let selected : Delegation.MemoryData p := ⟨data.setup, data.windowRows lower upper, start, finish⟩
  have memory : Delegation.BoundaryMemoryInputs selected before cells :=
    native_window_boundary_inputs_at_boundary inputs.memory.toBoundaryInputs startInputs
  have publicABI : NativeCallInputs selected before cells :=
    ⟨memory, inputs.controlStart,
      fun row member => inputs.family row (List.mem_of_mem_filter member),
      fun row member => inputs.active row (List.mem_of_mem_filter member), inputs.calls⟩
  have abi := publicABI.toBoundaryInputs size selectedAccepted
  obtain ⟨referenceAfter, pointer, input, output, mapping, source, result⟩ :=
    permutation_binding_at_boundary hp inverse selectedAccepted abi inputs.tables aligned
  have target : Delegation.TraceMapping selected before atFinish cells := by
    refine ⟨⟨spanEvents, spanPerm, spanHistory⟩, ?_⟩
    intro token member
    exact finishInputs.reads token member
  obtain ⟨otherPointer, otherRead, domain⟩ := call_state_cells hp inverse selectedAccepted abi inputs.tables aligned
  have samePointer := (EStateM.Result.ok.inj (mapping.pointerRead.symm.trans otherRead)).1
  subst otherPointer
  have lanes : Permutation.LanesAt atFinish pointer output := by
    intro lane
    let physical : Fin 31 := ⟨Controller.physicalLane 0 lane,
      Nat.lt_trans (Controller.Proofs.physical_bound 0 lane) (by decide)⟩
    have lowTracked : Cell.ram (pointer + BitVec.ofNat 32 (Permutation.laneOffset lane)) ∈ cells := by
      simpa only [physical, Controller.physicalLane, Permutation.laneOffset, Fin.val_zero,
        Nat.mul_zero, Nat.add_zero] using domain physical 0
    have highTracked : Cell.ram (pointer + BitVec.ofNat 32 (Permutation.laneOffset lane) + 4) ∈ cells := by
      have four : BitVec.ofNat 32 4 = (4 : BitVec 32) := by decide +kernel
      simpa only [physical, Controller.physicalLane, Permutation.laneOffset, Fin.val_one,
        Nat.mul_one, BitVec.ofNat_add, ← BitVec.add_assoc, four] using domain physical 1
    obtain ⟨low, high, lowRead, highRead, value, bound⟩ := mapping.outputLanes lane
    exact ⟨low, high,
      terminal_mapping_read source target finishInputs.addresses lowTracked lowRead,
      terminal_mapping_read source target finishInputs.addresses highTracked highRead, value, bound⟩
  refine ⟨start, finish, earlierEvents, spanEvents, before, atFinish,
    ?_, spanPerm, earlierHistory, spanHistory, selectedAccepted, memory,
    pointer, input, output, ⟨mapping.pointerRead, mapping.inputLanes, lanes⟩, target, result⟩
  simpa only [native_prefix_steps] using earlierPerm

end Airbender.Keccak.Proofs
