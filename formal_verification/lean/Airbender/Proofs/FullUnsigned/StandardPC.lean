import Airbender.Proofs.FullUnsigned.StandardSource

namespace Airbender.Compiler.MachineTargets.Proofs
open Trace Arithmetic Trace.Proofs Reference.RiscV.Sail
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000
variable [Fact babyBearModulus.Prime]

/-- Public standard source membership gives the original native PC retirement.
The combined request match selects the same caller and worker. -/
theorem unrolled_full_standard_pc_binding
    {initial : State} {text : List (BitVec 32)} {capacity : Nat}
    {masks : PooledFamily → NativeDecoder.ProgramRows.Mask}
    {columns : PooledFamily → List (List (ZMod babyBearModulus))}
    {trace : PooledTrace babyBearModulus} {workers : Delegation.MemoryData babyBearModulus}
    {extraSteps : List (MemoryToken babyBearModulus × MemoryToken babyBearModulus)}
    {extraRequests : List (Delegation.Requests.Request babyBearModulus)}
    (setup : UnrolledProgramSetup .fullUnsigned initial text capacity masks columns)
    (lookup : UnrolledDecoderExactLookup trace masks columns)
    (accepted : UnrolledAcceptance trace workers extraSteps extraRequests)
    (excluded : FullUnsigned.NoSpecial5Call initial text)
    (initialPC : trace.initial.word.lo < limbBase)
    (row : Trace.Row babyBearModulus PooledFamily) (member : row ∈ trace.rows)
    (family : row.family = .addSub) (selected : Delegation.Requests.Selected row.assignment)
    (worker : Delegation.Row babyBearModulus)
    (matched : Delegation.Requests.fulfillment worker = Delegation.Requests.caller row.assignment) :
    Delegation.Caller.PCBinding row.assignment initial
      (FullUnsigned.entriesWith FullUnsigned.standardDecoderFields text) := by
  obtain ⟨entry, included, _, _, query, _⟩ := unrolled_full_standard_caller_source
    setup lookup accepted excluded initialPC row member family selected worker matched
  have equations := accepted.cpuEquations row member
  simp only [Trace.Row.constraints, family, CircuitLayout.constraints] at equations
  have core := Verification.holds_of_sublist equations
    (List.sublist_append_left AddSub.importedConstraints AddSub.importedConstraintsTimestampLookups)
  apply Delegation.Caller.Proofs.pc_binding (by decide)
    (by decide +kernel : SerializedInverse.Limb16 babyBearModulus) core
    (unrolled_full_caller_image setup.image setup.size)
  change ∃ i : Fin (FullUnsigned.entriesWith FullUnsigned.standardDecoderFields text).length,
    Delegation.Caller.nativeQuery row.assignment =
      Delegation.Caller.query ((FullUnsigned.entriesWith FullUnsigned.standardDecoderFields text).get i)
  obtain ⟨i, rfl⟩ := List.mem_iff_get.mp included
  exact ⟨i, query⟩

end Airbender.Compiler.MachineTargets.Proofs
