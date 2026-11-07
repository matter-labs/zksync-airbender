import Airbender.Proofs.Trace.Families.ReducedMachine.WordMemoryTransfers

namespace Airbender.ReducedMachine.Native
open Trace NativeShadow Reference.RiscV.Sail
set_option autoImplicit false

/-- Actual initialized matching and original public construction derive all
    original same-pre-state GPR/RAM/ROM transfers, native masked/unmasked writes,
    numerical addresses/PCs, chronological states and decoder replay. The exact
    native ROM bytes are constructed, not equated with arbitrary public images.
    Retained virtual-memory checks/clauses/normal/fetched execution are separate. -/
theorem public_word_memory_transfers {trace : Data mersenne31Modulus NativeReducedFamily}
    {setup : SparseDecoderSetup WordMemoryMode} {initial : State} {cells : List Cell} {seeds : List ShadowSeed}
    {count logCapacity : Nat}
    (image : wordMemoryDecoderSetupImage (NativeROM.state initial) count logCapacity = some setup)
    (inputs : ShadowImageBoundary (fixedData trace) (NativeROM.state initial) cells seeds)
    (accepted : Accepted (fixedData trace)) (decoded : WordMemoryDecodedTrace (fixedData trace) setup)
    (aligned : ∀ cell ∈ cells, cell.Aligned) (capacity : count ≤ 1048576) :
    WordMemoryTransferHistory (fixedData trace) setup (NativeROM.state initial) cells :=
  NativeWordMemoryTransferProofs.image_transfer_history image inputs accepted decoded aligned capacity

end Airbender.ReducedMachine.Native
