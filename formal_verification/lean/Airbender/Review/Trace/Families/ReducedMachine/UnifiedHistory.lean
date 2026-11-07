import Airbender.Proofs.Trace.Families.ReducedMachine.UnifiedProjectedHistory

namespace Airbender.ReducedMachine.Native
open Trace NativeShadow Reference.RiscV.Sail
set_option autoImplicit false

/-- Common original source construction/full native matching derive all mixed
    chronological projected states, read/write realization, x0, ROM-byte/misa
    frames and stateful replay. Arbitrary logical public code is not equated with
    fixed native ROM. Retained mixed instruction execution remains separate. -/
theorem public_unified_history {trace : Data mersenne31Modulus NativeReducedFamily}
    {setup : SparseDecoderSetup UnifiedMode} {before : State} {cells : List Cell} {seeds : List ShadowSeed}
    {count logCapacity : Nat}
    (image : unifiedDecoderSetupImage before count logCapacity = some setup)
    (inputs : ShadowImageBoundary (fixedData trace) before cells seeds)
    (accepted : Accepted (fixedData trace)) (decoded : UnifiedDecodedTrace (fixedData trace) setup)
    (aligned : ∀ cell ∈ cells, cell.Aligned) (capacity : count ≤ 1048576) :
    UnifiedProjectedHistory (fixedData trace) setup before cells :=
  NativeUnifiedHistoryProofs.image_projected_history image inputs accepted decoded aligned capacity

/-- Original source construction and full native acceptance derive every mixed
    actual port domain, preserving both readonly refreshes and SW memory writes. -/
theorem public_unified_port_domains {trace : Data mersenne31Modulus NativeReducedFamily}
    {setup : SparseDecoderSetup UnifiedMode} {before : State} {count logCapacity : Nat}
    (image : unifiedDecoderSetupImage before count logCapacity = some setup)
    (accepted : Accepted (fixedData trace)) (decoded : UnifiedDecodedTrace (fixedData trace) setup)
    (row : Row mersenne31Modulus NativeReducedFamily) (present : row ∈ (fixedData trace).rows) :
    ∃ entry ∈ setup.program, entry.SourceWith before unifiedDecoderFields ∧
      row.decoderQuery = entry.query ∧ ∀ i : Fin 3,
        architecturalAddress (importedConstraintsMemoryPorts[i].address.code row.assignment) =
          (unifiedPortDomains row.assignment entry)[i] :=
  NativeUnifiedHistoryProofs.decoded_port_domains image accepted decoded row present

end Airbender.ReducedMachine.Native
