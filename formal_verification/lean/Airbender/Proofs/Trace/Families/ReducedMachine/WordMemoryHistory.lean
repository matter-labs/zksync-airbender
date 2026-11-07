import Airbender.Proofs.Trace.Families.ReducedMachine.WordMemoryCodeHistory
import Airbender.Review.Helpers.Memory.ReducedMachineWordMemoryHistory

namespace Airbender.ReducedMachine.NativeWordMemoryHistoryProofs
open Native NativeShadow Trace Reference.RiscV.Sail
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

/-- Full accepted native matching and meaningful public input construction
    derive every projected chronological Sail state, byte frame and replay. -/
theorem image_projected_history {trace : Data mersenne31Modulus NativeReducedFamily}
    {setup : SparseDecoderSetup WordMemoryMode} {initial : State} {cells : List Cell} {seeds : List ShadowSeed}
    {count logCapacity : Nat}
    (image : wordMemoryDecoderSetupImage initial count logCapacity = some setup)
    (inputs : ShadowImageBoundary (fixedData trace) initial cells seeds)
    (accepted : Accepted (fixedData trace)) (decoded : WordMemoryDecodedTrace (fixedData trace) setup)
    (aligned : ∀ cell ∈ cells, cell.Aligned) (capacity : count ≤ 1048576) :
    WordMemoryProjectedHistory (fixedData trace) setup initial cells := by
  obtain ⟨history,rows,after,consistent,permutation,ordered,sail,final⟩ :=
    NativeShadowHistoryProofs.projected_row_history image inputs accepted decoded aligned
  refine ⟨history,rows,after,consistent,permutation,ordered,sail,final,
    projected_history_rom_bytes inputs.architectural sail,
    (Trace.Proofs.sail_history_control_flow_csrs sail).1,?_⟩
  intro newer row older shape
  have present : row ∈ (fixedData trace).rows := permutation.mem_iff.mp (by rw [shape]; simp)
  obtain ⟨entry,member,source,query,_⟩ := NativeWordMemoryDecoderProofs.trace_decoding image accepted decoded row present
  have split : SailHistory cells
      (((newer.flatMap fun row => (rowEvents (fixedData trace).memoryEpoch row).reverse).filter
          fun event => architecturalAddress event.2.1) ++
        (((rowEvents (fixedData trace).memoryEpoch row).reverse.filter
          fun event => architecturalAddress event.2.1) ++
        ((older.flatMap fun row => (rowEvents (fixedData trace).memoryEpoch row).reverse).filter
          fun event => architecturalAddress event.2.1))) initial after := by
    simpa only [shape,List.flatMap_append,List.flatMap_cons,List.filter_append,List.append_assoc] using sail
  obtain ⟨rowAfter,past,future⟩ := Trace.Proofs.sail_history_append.mp split
  obtain ⟨rowBefore,earlier,current⟩ := Trace.Proofs.sail_history_append.mp past
  exact ⟨entry,member,rowBefore,rowAfter,source,
    entry_source_after_history inputs.architectural earlier image capacity member,query,earlier,current,future⟩

end Airbender.ReducedMachine.NativeWordMemoryHistoryProofs
