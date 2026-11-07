import Airbender.Proofs.Trace.Families.ReducedMachine.BranchValues
import Airbender.Proofs.ReducedMachine.NativeBranchPC
import Airbender.Review.Circuits.ReducedMachine.BranchResult

namespace Airbender.ReducedMachine.NativeBranchRangeProofs
open Native Trace Arithmetic
open Airbender.Trace.Proofs
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

/-- Public original decoding/history discharge every local branch numerical
    range, alignment and parity input. Chosen condition/target/PC are derived. -/
theorem image_branch_results {trace : Data mersenne31Modulus NativeReducedFamily}
    {setup : SparseDecoderSetup BranchMode} {before : Reference.RiscV.Sail.State} {cells : List Cell}
    {count logCapacity : Nat}
    (image : branchDecoderSetupImage before count logCapacity = some setup)
    (inputs : ImageBoundary (fixedData trace) before cells) (accepted : Accepted (fixedData trace))
    (decoded : BranchDecodedTrace (fixedData trace) setup)
    (row : Row mersenne31Modulus NativeReducedFamily) (present : row ∈ (fixedData trace).rows) :
    ∃ entry ∈ setup.program, entry.SourceWith before branchDecoderFields ∧
      row.decoderQuery = entry.query ∧ BranchDecoded row.assignment entry ∧ BranchNumericalEffects row.assignment := by
  have ranges := (image_value_bounds image inputs accepted decoded).1 row present
  obtain ⟨entry,found,source,query,fields⟩ := NativeBranchDecoderProofs.trace_decoding image accepted decoded row present
  refine ⟨entry,found,source,query,fields,?_⟩
  cases row with
  | mk family w =>
    cases family
    change BranchDecoded w entry at fields
    change decoderQuery w = entry.query at query
    have native := accepted.constraints (⟨.reduced,w⟩ : Row mersenne31Modulus NativeReducedFamily) present
    have first := ranges importedConstraintsMemoryPorts[0] (by
      change _ ∈ importedConstraintsMemoryPorts; simp [importedConstraintsMemoryPorts])
    have second := ranges importedConstraintsMemoryPorts[1] (by
      change _ ∈ importedConstraintsMemoryPorts; simp [importedConstraintsMemoryPorts])
    rw [Trace.Proofs.read_word] at first second
    change (sourceWord w).Bounded at first
    change (⟨(w 37).val,(w 38).val⟩ : Word).Bounded at second
    have routing := NativeBranchFieldProofs.source native fields.mask
    have low := congrArg (fun v : Vector (ZMod mersenne31Modulus) 2 => v[0]) routing
    have high := congrArg (fun v : Vector (ZMod mersenne31Modulus) 2 => v[1]) routing
    change w 47 = w 37 at low
    change w 48 = w 38 at high
    have right : (operandWord w).Bounded := by
      simpa [operandWord,source2,Word.Bounded,low,high] using second
    have canonical := native_query_pc_word (by decide : limbBase < mersenne31Modulus) query
    change initialPCWord w = Word.ofBitVec entry.pc at canonical
    have pc : (initialPCWord w).Bounded := by rw [canonical]; exact Word.ofBitVec_bound _
    have aligned : (initialPCWord w).lo % 4 = 0 := by
      rw [canonical]
      exact (run_sparse_setup_sources image found).2
    have immediate := NativeBranchDecoderProofs.immediate_word source.fields query
    have offset : (branchOffsetWord w).Bounded := by
      rw [immediate]
      exact (NativeBranchDecoderProofs.field_bounds source.fields).1
    have even : (branchOffsetWord w).lo % 2 = 0 := by
      rw [immediate]
      exact NativeBranchDecoderProofs.offset_even source
    have tagBound : branchFunct3 entry.data.family < mersenne31Modulus := by
      have tags := NativeBranchDecoderProofs.tags entry.data.family
      simp only [List.mem_cons,List.mem_nil_iff,or_false] at tags
      change _ < 2147483647
      omega
    have tags : (w 11).val ∈ [0,1,4,5,6,7] := by
      rw [fields.funct3,ZMod.val_natCast_of_lt tagBound]
      exact NativeBranchDecoderProofs.tags _
    have condition := NativeBranchConditionProofs.resolution native fields.mask tags first right
    have pcResult := NativeBranchPCProofs.effects native fields.mask tags first right pc offset aligned even
    exact ⟨condition.1,condition.2,NativeBranchPCProofs.target_bounds native,
      NativeBranchPCProofs.target_result native fields.mask pc offset,pcResult.1,pcResult.2⟩

end Airbender.ReducedMachine.NativeBranchRangeProofs
