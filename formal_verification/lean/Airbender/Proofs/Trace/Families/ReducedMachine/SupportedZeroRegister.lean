import Airbender.Proofs.Trace.ZeroValues
import Airbender.Proofs.Trace.Families.ReducedMachine.SupportedDecoder
import Airbender.Proofs.Trace.Families.ReducedMachine.History
import Airbender.Proofs.ReducedMachine.NativeSupportedLocal

namespace Airbender.ReducedMachine.NativeSupportedRegisterProofs
open Native Arithmetic Trace Verification
open Airbender.Trace.Proofs
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

/-- Actual original public decoding derives local preservation for every row. -/
theorem decoded_zero_preserving {trace : Data mersenne31Modulus NativeReducedFamily}
    {setup : SparseDecoderSetup SupportedMode} {initial : Reference.RiscV.Sail.State} {count logCapacity : Nat}
    (image : supportedDecoderSetupImage initial count logCapacity = some setup)
    (accepted : Accepted (fixedData trace)) (decoded : SupportedDecodedTrace (fixedData trace) setup) : ZeroPreserving (fixedData trace) := by
  intro row member
  obtain ⟨entry,_,source,query⟩ := NativeSupportedDecoderProofs.trace_decoding image accepted decoded row member
  cases row with
  | mk family w =>
    cases family
    exact NativeSupportedLocalProofs.row_zero_preserving _ (accepted.constraints _ member) source.fields query

/-- Public seeds and native matching propagate the proved x0 rule through all
    reads and writes. No expected zero read/write is supplied per row. -/
theorem native_zero_writes {trace : Data mersenne31Modulus NativeReducedFamily}
    {setup : SparseDecoderSetup SupportedMode} {initial : Reference.RiscV.Sail.State} {cells : List Cell}
    {count logCapacity : Nat}
    (image : supportedDecoderSetupImage initial count logCapacity = some setup)
    (accepted : Accepted (fixedData trace)) (boundary : ClockBoundary (fixedData trace))
    (seeds : initialImage initial cells = some (fixedData trace).initialMemory)
    (decoded : SupportedDecodedTrace (fixedData trace) setup) :
    ∀ event ∈ (fixedData trace).nativeEvents, event.2.1 = (Cell.register 0).addressCode →
      memoryWord event.2.2.2 = 0 :=
  zero_writes_of_preserving (by decide) accepted boundary seeds
    (decoded_zero_preserving image accepted decoded)

/-- Unchanged shared Clean-to-Sail realization constructs every state in native
    clock order, retaining actual mixed-port addresses and masked writes. -/
theorem image_row_history {trace : Data mersenne31Modulus NativeReducedFamily}
    {setup : SparseDecoderSetup SupportedMode} {initial : Reference.RiscV.Sail.State} {cells : List Cell}
    {count logCapacity : Nat}
    (image : supportedDecoderSetupImage initial count logCapacity = some setup)
    (inputs : ImageBoundary (fixedData trace) initial cells) (accepted : Accepted (fixedData trace))
    (decoded : SupportedDecodedTrace (fixedData trace) setup) (aligned : ∀ cell ∈ cells, cell.Aligned) :
    ∃ (history : TimestampSortedMemoryAccessList)
      (rows : List (Row mersenne31Modulus NativeReducedFamily)) (after : Reference.RiscV.Sail.State),
      MemoryHistory (fixedData trace) history ∧ rows.Perm (fixedData trace).rows ∧
      rows.Pairwise (fun a b => b.clock < a.clock) ∧
      SailHistory cells (rows.flatMap fun row => (rowEvents (fixedData trace).memoryEpoch row).reverse)
        initial after ∧ SailStateMatches cells history after := by
  have boundary := image_clock_boundary (by decide) inputs
  exact native_row_history (by decide) accepted boundary inputs.image inputs.domain aligned
    (native_zero_writes image accepted boundary inputs.image decoded)

end Airbender.ReducedMachine.NativeSupportedRegisterProofs
