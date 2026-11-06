import Airbender.Proofs.Trace.Families.ReducedMachine.Values

namespace Airbender.ReducedMachine.NativeShiftRangeProofs
open Native Trace
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

/-- Initialized native reads make both actual packed source keys canonical. -/
theorem image_source_keys {trace : Data mersenne31Modulus NativeReducedFamily}
    {setup : SparseDecoderSetup ShiftMode} {before : Reference.RiscV.Sail.State} {cells : List Cell}
    {count logCapacity : Nat}
    (image : shiftDecoderSetupImage before count logCapacity = some setup)
    (inputs : ImageBoundary (fixedData trace) before cells) (accepted : Accepted (fixedData trace))
    (decoded : ShiftDecodedTrace (fixedData trace) setup)
    (row : Row mersenne31Modulus NativeReducedFamily) (present : row ∈ (fixedData trace).rows) :
    ∃ entry ∈ setup.program, entry.SourceWith before shiftDecoderFields ∧
      row.decoderQuery = entry.query ∧ ShiftDecoded row.assignment entry ∧
      ∀ limb : Fin 2,
        (entry.data.family.lookupKey (source1 row.assignment)[limb] (shiftAmount row.assignment)).val =
          (source1 row.assignment)[limb].val + 65536 * (shiftAmount row.assignment).val +
            2097152 * (if entry.data.family = .left then 0 else 1) := by
  have ranges := (image_value_bounds image inputs accepted decoded).1 row present
  have bounds := ranges importedConstraintsMemoryPorts[0] (by
    cases row with
    | mk family w => cases family; change _ ∈ importedConstraintsMemoryPorts; simp [importedConstraintsMemoryPorts])
  rw [Trace.Proofs.read_word] at bounds
  change (source1 row.assignment)[0].val < 65536 ∧ (source1 row.assignment)[1].val < 65536 at bounds
  obtain ⟨entry,found,source,query,fields⟩ := NativeShiftDecoderProofs.trace_decoding image accepted decoded row present
  have native := accepted.constraints row present
  refine ⟨entry,found,source,query,fields,?_⟩
  obtain ⟨useRegister,mask⟩ := fields.mask
  have amount : (shiftAmount row.assignment).val < 32 := by
    cases row with
    | mk family w =>
      cases family
      exact (NativeShiftRoutingProofs.amount native entry.data.family useRegister mask).2.2.1
  intro limb
  have bound : (source1 row.assignment)[limb].val < 65536 := by
    fin_cases limb
    · exact bounds.1
    · exact bounds.2
  simpa only [NativeShiftNaturalProofs.keyNat] using
    NativeShiftNaturalProofs.canonical_key entry.data.family _ _ bound amount

end Airbender.ReducedMachine.NativeShiftRangeProofs
