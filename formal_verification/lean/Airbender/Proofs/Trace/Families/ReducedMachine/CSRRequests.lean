import Airbender.Proofs.Trace.Families.ReducedMachine.CSRRegisterHistory
import Airbender.Proofs.Trace.Families.ReducedMachine.CSRValues
import Airbender.Proofs.ReducedMachine.NativeCSRSource

namespace Airbender.ReducedMachine.NativeCSRSourceProofs
open Native Trace Arithmetic Reference.RiscV.Sail
open Airbender.Trace.Proofs
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

/-- Initialized ranges and chronological GPR realization discharge all local
    source/read/state inputs. Request observations use the very same rowBefore. -/
theorem image_request_history {trace : Data mersenne31Modulus NativeReducedFamily}
    {setup : SparseDecoderSetup CSRMode} {initial : State} {cells : List Cell}
    {count logCapacity : Nat}
    (image : csrDecoderSetupImage initial count logCapacity = some setup)
    (inputs : ImageBoundary (runtimeCSRData trace) initial cells)
    (accepted : Accepted (runtimeCSRData trace)) (decoded : CSRDecodedTrace trace setup)
    (aligned : ∀ cell ∈ cells, cell.Aligned) :
    CSRRequestHistory (runtimeCSRData trace) setup initial cells := by
  obtain ⟨history,rows,after,consistent,permutation,ordered,sail,final,memory,misa,segments⟩ :=
    NativeCSRRegisterProofs.image_register_history (trace := runtimeCSRData trace) image inputs accepted decoded aligned
  have ranges := (NativeCSRRangeProofs.image_value_bounds image inputs accepted decoded).1
  refine ⟨history,rows,after,consistent,permutation,ordered,sail,final,memory,misa,?_⟩
  intro newer row older shape
  obtain ⟨entry,member,rowBefore,rowAfter,source,replay,query,past,current,future,transfer⟩ :=
    segments newer row older shape
  have present : row ∈ trace.rows := permutation.mem_iff.mp (by rw [shape]; simp)
  have holds := accepted.constraints row present
  refine ⟨entry,member,rowBefore,rowAfter,source,replay,query,past,current,future,transfer,?_⟩
  cases row with
  | mk family w =>
    cases family
    have first := ranges (.mk .reduced w) present importedConstraintsMemoryPorts[0] (by
      change _ ∈ importedConstraintsMemoryPorts; simp [importedConstraintsMemoryPorts])
    rw [read_word] at first
    change (sourceWord w).Bounded at first
    exact request_from_source holds source.fields query transfer first

end Airbender.ReducedMachine.NativeCSRSourceProofs
