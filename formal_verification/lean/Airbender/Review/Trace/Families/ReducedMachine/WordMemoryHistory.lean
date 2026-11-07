import Airbender.Proofs.Trace.Families.ReducedMachine.WordMemoryHistory

namespace Airbender.ReducedMachine.Native
open Trace NativeShadow Reference.RiscV.Sail
set_option autoImplicit false

/-- Original public decoding, independent architectural/shadow seeds and full
    native acceptance derive chronological architectural Sail states, all native
    matching, ROM-byte/misa frames and stateful decoder replay. Public code fits
    the native ROM prefix; aligned tracked cells are input locations, not read/
    write/state answers. Retained LOAD/STORE execution remains separate. -/
theorem public_word_memory_shadow_history {trace : Data mersenne31Modulus NativeReducedFamily}
    {setup : SparseDecoderSetup WordMemoryMode} {initial : State} {cells : List Cell} {seeds : List ShadowSeed}
    {count logCapacity : Nat}
    (image : wordMemoryDecoderSetupImage initial count logCapacity = some setup)
    (inputs : ShadowImageBoundary (fixedData trace) initial cells seeds)
    (accepted : Accepted (fixedData trace)) (decoded : WordMemoryDecodedTrace (fixedData trace) setup)
    (aligned : ∀ cell ∈ cells, cell.Aligned) (capacity : count ≤ 1048576) :
    WordMemoryProjectedHistory (fixedData trace) setup initial cells :=
  NativeWordMemoryHistoryProofs.image_projected_history image inputs accepted decoded aligned capacity

end Airbender.ReducedMachine.Native
