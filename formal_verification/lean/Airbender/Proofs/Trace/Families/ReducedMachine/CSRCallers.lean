import Airbender.Proofs.Trace.Families.ReducedMachine.CSRRequests
import Airbender.Proofs.ReducedMachine.NativeCSRCallerClock

namespace Airbender.ReducedMachine.NativeCSRCallerProofs
open Native Trace Reference.RiscV.Sail
open Airbender.Trace.Proofs
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

private theorem sorted_map {rows : List (Row mersenne31Modulus NativeReducedFamily)}
    (ordered : rows.Pairwise (fun a b => b.clock < a.clock))
    (times : ∀ row ∈ rows, (csrCallerObservation row).clock = row.clock+3) :
    (rows.map csrCallerObservation).Pairwise (fun a b => b.clock < a.clock) := by
  induction rows with
  | nil => simp
  | cons row rest ih =>
    have ordered := List.pairwise_cons.mp ordered
    apply List.pairwise_cons.mpr
    constructor
    · intro caller member
      obtain ⟨previous,present,rfl⟩ := List.mem_map.mp member
      have left := times row (by simp)
      have right := times previous (by simp [present])
      have earlier := ordered.1 previous present
      omega
    · exact ih ordered.2 (fun previous present => times previous (by simp [present]))

/-- The same accepted initialized CSR history supplies chronological rows,
    source observations and native clocks; no caller stream is an input. -/
theorem image_callers {trace : Data mersenne31Modulus NativeReducedFamily}
    {setup : SparseDecoderSetup CSRMode} {initial : State} {cells : List Cell}
    {count logCapacity : Nat}
    (image : csrDecoderSetupImage initial count logCapacity = some setup)
    (inputs : ImageBoundary (runtimeCSRData trace) initial cells)
    (accepted : Accepted (runtimeCSRData trace)) (decoded : CSRDecodedTrace trace setup)
    (aligned : ∀ cell ∈ cells, cell.Aligned) :
    CSRRequestHistory (runtimeCSRData trace) setup initial cells ∧
      ∃ callers, CSRCallerProjection (runtimeCSRData trace) callers := by
  have history := NativeCSRSourceProofs.image_request_history image inputs accepted decoded aligned
  have originalHistory := history
  obtain ⟨memory,rows,after,consistent,permutation,ordered,rest⟩ := history
  have clocks := native_reduced_image_clocks inputs accepted
  have localClock (row : Row mersenne31Modulus NativeReducedFamily) (present : row ∈ rows) :
      (timeOfPair (csrCallerObservation row).time).Bounded ∧
        (csrCallerObservation row).clock = row.clock+3 ∧
        (csrCallerObservation row).clock%4=3 ∧ 0<(csrCallerObservation row).clock ∧
        (csrCallerObservation row).clock < (timeOfPair row.finish.timestamp).value ∧
        ∀ port ∈ row.ports, row.clock+port.clock.offset < (csrCallerObservation row).clock := by
    have actual : row ∈ trace.rows := permutation.mem_iff.mp present
    have input := clocks.1 row actual
    have effect := clocks.2.1 row actual
    cases row with
    | mk family w => cases family; exact clock input effect
  have filtered : ∀ row ∈ csrCallerRows rows, row ∈ rows ∧ (csrRequest row.assignment).multiplicity = 1 := by
    intro row present
    simpa [csrCallerRows] using present
  have selectedOrder : (csrCallerRows rows).Pairwise (fun a b => b.clock<a.clock) :=
    ordered.filter _
  refine ⟨originalHistory,csrCallers rows,rows,permutation,ordered,rfl,
    sorted_map selectedOrder (fun row present => (localClock row (filtered row present).1).2.1),?_⟩
  intro caller member
  obtain ⟨row,present,rfl⟩ := List.mem_map.mp member
  have chosen := filtered row present
  have actual : row ∈ trace.rows := permutation.mem_iff.mp chosen.1
  have holds := accepted.constraints row actual
  obtain ⟨entry,_,source,query,fields⟩ := NativeCSRDecoderProofs.trace_decoding image accepted decoded row actual
  have requests : (csrCallerObservation row).request.kind = 1991 ∧
      ∃ offset, (csrCallerObservation row).request.offsetHigh = some offset ∧ offset.val<65536 := by
    cases row with
    | mk family w => cases family; exact selected_request holds fields.mask chosen.2
  have time := localClock row chosen.1
  exact ⟨chosen.2,requests.1,requests.2,time.1,time.2.2.1,time.2.2.2.1,
    row,chosen.1,rfl,time.2.1,time.2.2.2.2.1,time.2.2.2.2.2⟩

end Airbender.ReducedMachine.NativeCSRCallerProofs
