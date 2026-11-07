import Airbender.Proofs.Trace.Families.ReducedMachine.CSRCallers
import Airbender.Proofs.ReducedMachine.NativeCSRArgument

namespace Airbender.ReducedMachine.NativeCSRArgumentProofs
open Native Trace Reference.RiscV.Sail
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

/-- Actual derived callers retain their exact source-history row origins when
    connected to the reviewed native stage2/quotient argument formulas. -/
theorem image_argument {R : Type} [CommRing R] (embed : ZMod mersenne31Modulus →+* R)
    (ch : CSRArgumentChallenges R)
    {trace : Data mersenne31Modulus NativeReducedFamily}
    {setup : SparseDecoderSetup CSRMode} {initial : State} {cells : List Cell}
    {count logCapacity : Nat}
    (image : csrDecoderSetupImage initial count logCapacity = some setup)
    (inputs : ImageBoundary (runtimeCSRData trace) initial cells)
    (accepted : Accepted (runtimeCSRData trace)) (decoded : CSRDecodedTrace trace setup)
    (aligned : ∀ cell ∈ cells, cell.Aligned) :
    CSRRequestHistory (runtimeCSRData trace) setup initial cells ∧
      ∃ callers, CSRCallerProjection (runtimeCSRData trace) callers ∧
        CSRCallerArgumentProjection embed ch (runtimeCSRData trace) callers := by
  obtain ⟨history,callers,projection⟩ := NativeCSRCallerProofs.image_callers image inputs accepted decoded aligned
  have original := projection
  obtain ⟨rows,permutation,ordered,same,sorted,members⟩ := projection
  refine ⟨history,callers,original,?_⟩
  intro caller member
  obtain ⟨_,_,_,_,_,_,row,present,rfl,rest⟩ := members caller member
  have actual : row ∈ trace.rows := permutation.mem_iff.mp present
  refine ⟨row,actual,rfl,?_,?_,?_,?_⟩
  cases row with
  | mk family w =>
    cases family
    exact caller_key embed w
  cases row with
  | mk family w =>
    cases family
    exact stage_two embed ch w
  intro tau
  exact stage_three embed ch tau row.assignment
  exact unit_scaling embed ch row.assignment

end Airbender.ReducedMachine.NativeCSRArgumentProofs
