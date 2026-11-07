import Airbender.Proofs.Trace.Families.ReducedMachine.UnifiedValues
import Airbender.Proofs.Trace.Families.ReducedMachine.ShadowHistory
import Airbender.Review.Helpers.Memory.ReducedMachineUnified

namespace Airbender.ReducedMachine.NativeUnifiedHistoryProofs
open Native NativeShadow NativeShadowProofs Arithmetic Trace Verification Reference.RiscV.Sail
open Airbender.Trace.Proofs
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

/-- Original full unified membership derives every actual local x0 rule. -/
theorem decoded_zero_preserving {trace : Data mersenne31Modulus NativeReducedFamily}
    {setup : SparseDecoderSetup UnifiedMode} {before : State} {count logCapacity : Nat}
    (image : unifiedDecoderSetupImage before count logCapacity = some setup)
    (accepted : Accepted (fixedData trace)) (decoded : UnifiedDecodedTrace (fixedData trace) setup) :
    ZeroPreserving (fixedData trace) := by
  intro row present
  obtain ⟨entry,_,source,query⟩ := NativeUnifiedDecoderProofs.trace_decoding image accepted decoded row present
  exact NativeUnifiedLocalProofs.row_zero_preserving row (accepted.constraints row present) source.fields query

/-- Full original public membership selects every actual three-port domain;
    neither a profile nor an expected domain is supplied per row. -/
theorem decoded_port_domains {trace : Data mersenne31Modulus NativeReducedFamily}
    {setup : SparseDecoderSetup UnifiedMode} {before : State} {count logCapacity : Nat}
    (image : unifiedDecoderSetupImage before count logCapacity = some setup)
    (accepted : Accepted (fixedData trace)) (decoded : UnifiedDecodedTrace (fixedData trace) setup)
    (row : Row mersenne31Modulus NativeReducedFamily) (present : row ∈ (fixedData trace).rows) :
    ∃ entry ∈ setup.program, entry.SourceWith before unifiedDecoderFields ∧
      row.decoderQuery = entry.query ∧ ∀ i : Fin 3,
        architecturalAddress (importedConstraintsMemoryPorts[i].address.code row.assignment) =
          (unifiedPortDomains row.assignment entry)[i] := by
  obtain ⟨entry,member,source,query⟩ := NativeUnifiedDecoderProofs.trace_decoding image accepted decoded row present
  refine ⟨entry,member,source,query,?_⟩
  cases row with
  | mk family w =>
    cases family
    exact NativeUnifiedLocalProofs.port_domains (accepted.constraints _ present) source.fields query

/-- The common actual x0 law propagates through full native matching, including
    independent shadow seeds. No expected read/write or zero rule is public. -/
theorem shadow_zero_writes {trace : Data mersenne31Modulus NativeReducedFamily}
    {setup : SparseDecoderSetup UnifiedMode} {before : State} {cells : List Cell} {seeds : List ShadowSeed}
    {count logCapacity : Nat}
    (image : unifiedDecoderSetupImage before count logCapacity = some setup)
    (inputs : ShadowImageBoundary (fixedData trace) before cells seeds)
    (accepted : Accepted (fixedData trace)) (decoded : UnifiedDecodedTrace (fixedData trace) setup) :
    ∀ event ∈ (fixedData trace).nativeEvents, event.2.1 = (Cell.register 0).addressCode →
      memoryWord event.2.2.2 = 0 := by
  have preserves := decoded_zero_preserving image accepted decoded
  have reads := zero_reads_from_seeds (by decide) accepted (shadow_clock_boundary (by decide) inputs)
    (fun _ present address => NativeShadowHistoryProofs.shadow_initial_zero inputs present address) preserves
  exact zero_writes_from_reads reads preserves

/-- All seven profiles share ONE initialized chronological projected Sail
    realization; only whole ROM-shadow addresses are erased from Sail transfers. -/
theorem projected_row_history {trace : Data mersenne31Modulus NativeReducedFamily}
    {setup : SparseDecoderSetup UnifiedMode} {before : State} {cells : List Cell} {seeds : List ShadowSeed}
    {count logCapacity : Nat}
    (image : unifiedDecoderSetupImage before count logCapacity = some setup)
    (inputs : ShadowImageBoundary (fixedData trace) before cells seeds)
    (accepted : Accepted (fixedData trace)) (decoded : UnifiedDecodedTrace (fixedData trace) setup)
    (aligned : ∀ cell ∈ cells, cell.Aligned) :
    ∃ (history : TimestampSortedMemoryAccessList) (rows : List (Row mersenne31Modulus NativeReducedFamily)) (after : State),
      MemoryHistory (fixedData trace) history ∧ rows.Perm (fixedData trace).rows ∧
      rows.Pairwise (fun a b => b.clock < a.clock) ∧
      SailHistory cells ((rows.flatMap fun row => (rowEvents (fixedData trace).memoryEpoch row).reverse).filter
        fun event => architecturalAddress event.2.1) before after ∧ SailStateMatches cells history after := by
  have boundary := shadow_clock_boundary (by decide) inputs
  obtain ⟨history,events,after,checked,permutation,sorted,actual,final⟩ :=
    projected_native_sail_history (by decide) accepted boundary (shadow_image_unique inputs) architecturalAddress
      (shadow_image_projection inputs) (List.nodup_append.mp inputs.domain).1 aligned inputs.architectural
      (NativeShadowHistoryProofs.shadow_event_cells (by decide) inputs accepted)
      (shadow_zero_writes image inputs accepted decoded)
  obtain ⟨rows,rowPermutation,ordered,groupedSorted,grouped⟩ := native_row_order (by decide) accepted boundary
  have same := List.Perm.eq_of_pairwise' groupedSorted sorted (grouped.trans permutation.symm)
  exact ⟨history,rows,after,checked,rowPermutation,ordered,same.symm ▸ actual,final⟩

end Airbender.ReducedMachine.NativeUnifiedHistoryProofs
