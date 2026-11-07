import Airbender.Review.Trace.Families.ReducedMachine.CSRCallers

namespace Tests.NativeReducedCSRCallers
open Airbender Arithmetic Trace ReducedMachine Native Verification Reference.RiscV.Sail
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

private def row (low high multiplicity : Nat) : Row mersenne31Modulus NativeReducedFamily :=
  ⟨.reduced,fun i => if i=2 then low else if i=3 then high else if i=92 then multiplicity
    else if i=94 then 1991 else if i=93 then 5 else 0⟩

/-- The request observer uses slot3 after three GPR access slots. -/
theorem first_slot : (csrCallerObservation (row 4 0 1)).clock = 7 := by decide

/-- Alignment leaves room at the end of the low19-bit limb. -/
theorem last_low_limb_slot : (csrCallerObservation (row 524284 0 1)).clock = 524287 := by decide

theorem next_high_limb_slot : (csrCallerObservation (row 0 1 1)).clock = 524291 := by decide

theorem across_low_limb_boundary :
    (csrCallerObservation (row 524284 0 1)).clock+4 =
      (csrCallerObservation (row 0 1 1)).clock := by decide

/-- Only multiplicity selects a caller; zero rows are absent from this projection. -/
theorem zero_multiplicity_filtered : (csrCallers [row 4 0 0]).length = 0 := by decide

theorem selected_multiplicity_retained : (csrCallers [row 4 0 1]).length = 1 := by decide

/-- Newest-first order is retained across the actual request slots. -/
theorem adjacent_caller_order :
    (csrCallers [row 8 0 1,row 4 0 1]).Pairwise (fun a b => b.clock<a.clock) := by decide

/-- Complete initialized matching rules out clockzero for any actual row's
    local caller observation. No per-row clock bound/alignment is supplied. -/
theorem zero_caller_clock_rejected {trace : Data mersenne31Modulus NativeReducedFamily}
    {initial : State} {cells : List Cell}
    (inputs : ImageBoundary (runtimeCSRData trace) initial cells)
    (accepted : Accepted (runtimeCSRData trace))
    (row : Row mersenne31Modulus NativeReducedFamily) (present : row ∈ trace.rows)
    (bad : (csrCallerObservation row).clock = 0) : False := by
  have clocks := Airbender.Trace.Proofs.native_reduced_image_clocks inputs accepted
  have nativeInput := clocks.1 row present
  have nativeEffect := clocks.2.1 row present
  cases row with
  | mk family w =>
    cases family
    have positive := (NativeCSRCallerProofs.clock nativeInput nativeEffect).2.2.2.1
    exact (Nat.ne_of_gt positive) bad

end Tests.NativeReducedCSRCallers
