import Airbender.Proofs.Trace.Families.ReducedMachine.ArithmeticCodeHistory
import Airbender.Review.Helpers.Memory.ReducedMachineArithmetic

namespace Airbender.ReducedMachine.NativeArithmeticRegisterProofs
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false
open Native Trace Reference.RiscV.Sail Reference.Sail
open Airbender.Trace.Proofs

/-- Actual public initialization and native matching construct every Sail state.
    Readonly refreshes preserve the common pre-state even when ports alias. -/
theorem image_register_history {trace : Data mersenne31Modulus NativeReducedFamily}
    {setup : SparseDecoderSetup ArithmeticMode} {initial : State} {cells : List Cell}
    {count logCapacity : Nat}
    (image : arithmeticDecoderSetupImage initial count logCapacity = some setup)
    (inputs : ImageBoundary trace initial cells) (accepted : Accepted trace)
    (decoded : ArithmeticDecodedTrace trace setup) (aligned : ∀ cell ∈ cells, cell.Aligned) :
    ArithmeticRegisterHistory trace setup initial cells := by
  obtain ⟨history,rows,after,consistent,permutation,ordered,sail,final⟩ :=
    image_row_history image inputs accepted decoded aligned
  have clocks := image_clock_boundary (by decide) inputs
  have events : (rows.flatMap fun row => (rowEvents trace.memoryEpoch row).reverse).Perm
      trace.nativeEvents := by
    rw [native_events_projection (by decide) accepted clocks]
    exact permutation.flatMap (fun row _ => List.reverse_perm _)
  have native : ∀ event ∈ rows.flatMap (fun row => (rowEvents trace.memoryEpoch row).reverse),
      event ∈ trace.nativeEvents := fun event member => events.mem_iff.mp member
  refine ⟨history,rows,after,consistent,permutation,ordered,sail,final,
    native_history_memory image accepted decoded native sail,(sail_history_control_flow_csrs sail).1,?_⟩
  intro newer row older shape
  have present : row ∈ trace.rows := permutation.mem_iff.mp (by rw [shape]; simp)
  obtain ⟨entry,member,source,query,_⟩ := NativeArithmeticDecoderProofs.trace_decoding image accepted decoded row present
  have split : SailHistory cells
      ((newer.flatMap fun row => (rowEvents trace.memoryEpoch row).reverse) ++
        ((rowEvents trace.memoryEpoch row).reverse ++
        (older.flatMap fun row => (rowEvents trace.memoryEpoch row).reverse))) initial after := by
    simpa only [shape,List.flatMap_append,List.flatMap_cons,List.append_assoc] using sail
  obtain ⟨rowAfter,past,future⟩ := sail_history_append.mp split
  obtain ⟨rowBefore,earlier,current⟩ := sail_history_append.mp past
  have earlierNative : ∀ event ∈ older.flatMap (fun row => (rowEvents trace.memoryEpoch row).reverse),
      event ∈ trace.nativeEvents := by
    intro event member
    apply native event
    rw [shape,List.flatMap_append,List.flatMap_cons]
    exact List.mem_append_right _ (List.mem_append_right _ member)
  refine ⟨entry,member,rowBefore,rowAfter,source,
    entry_source_after_native_history image accepted decoded source earlierNative earlier,query,earlier,current,future,?_⟩
  cases row with
  | mk family w =>
    cases family
    exact ⟨NativeArithmeticPortProofs.register_reads trace.memoryEpoch (accepted.constraints _ present) source.fields query current,
      NativeArithmeticPortProofs.register_write trace.memoryEpoch (accepted.constraints _ present) source.fields query current⟩

end Airbender.ReducedMachine.NativeArithmeticRegisterProofs
