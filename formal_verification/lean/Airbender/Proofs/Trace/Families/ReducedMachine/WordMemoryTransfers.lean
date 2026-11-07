import Airbender.Proofs.ReducedMachine.NativeWordMemoryTransfers
import Airbender.Proofs.Trace.Families.ReducedMachine.WordMemoryHistory
import Airbender.Proofs.Trace.Families.ReducedMachine.ShadowValues

namespace Airbender.ReducedMachine.NativeWordMemoryTransferProofs
open Native NativeShadow Arithmetic Trace Verification Reference.RiscV.Sail
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

/-- Exact ROM byte construction, accepted native matching and public original
    decoding construct every same-pre-state transfer and numerical row effect.
    All source ranges/PC alignment/ROM reads/states are discharged internally. -/
theorem image_transfer_history {trace : Data mersenne31Modulus NativeReducedFamily}
    {setup : SparseDecoderSetup WordMemoryMode} {initial : State} {cells : List Cell} {seeds : List ShadowSeed}
    {count logCapacity : Nat}
    (image : wordMemoryDecoderSetupImage (NativeROM.state initial) count logCapacity = some setup)
    (inputs : ShadowImageBoundary (fixedData trace) (NativeROM.state initial) cells seeds)
    (accepted : Accepted (fixedData trace)) (decoded : WordMemoryDecodedTrace (fixedData trace) setup)
    (aligned : ∀ cell ∈ cells, cell.Aligned) (capacity : count ≤ 1048576) :
    WordMemoryTransferHistory (fixedData trace) setup (NativeROM.state initial) cells := by
  obtain ⟨history,rows,after,consistent,permutation,ordered,sail,final,bytes,misa,segments⟩ :=
    NativeWordMemoryHistoryProofs.image_projected_history image inputs accepted decoded aligned capacity
  have ranges := (NativeShadowRangeProofs.image_value_bounds image inputs accepted decoded).1
  refine ⟨history,rows,after,consistent,permutation,ordered,sail,final,bytes,misa,?_⟩
  intro newer row older shape
  obtain ⟨entry,member,rowBefore,rowAfter,source,laterSource,query,past,current,future⟩ := segments newer row older shape
  have present : row ∈ (fixedData trace).rows := permutation.mem_iff.mp (by rw [shape]; simp)
  refine ⟨entry,member,rowBefore,rowAfter,source,laterSource,query,past,current,future,?_,?_⟩
  · cases row with
    | mk family w =>
      cases family
      have first := ranges _ present importedConstraintsMemoryPorts[0]
        (by change _ ∈ importedConstraintsMemoryPorts; simp [importedConstraintsMemoryPorts])
      rw [Trace.Proofs.read_word] at first
      change (sourceWord w).Bounded at first
      have canonical := Trace.Proofs.native_query_pc_word (by decide : limbBase < mersenne31Modulus) query
      change initialPCWord w = Word.ofBitVec entry.pc at canonical
      have pcAligned : (initialPCWord w).lo%4 = 0 := by
        rw [canonical]
        exact (Trace.Proofs.run_sparse_setup_sources image member).2
      exact NativeWordMemoryResultProofs.decoded_result (accepted.constraints _ present) source.fields query first pcAligned
  · cases row with
    | mk family w =>
      cases family
      exact transfer (fixedData trace).memoryEpoch (accepted.constraints _ present) source.fields query
        inputs.architectural past current

end Airbender.ReducedMachine.NativeWordMemoryTransferProofs
