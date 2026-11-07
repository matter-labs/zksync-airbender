import Airbender.Proofs.Trace.Families.ReducedMachine.WordMemoryAddressDomains

namespace Airbender.ReducedMachine.Native
open Trace NativeShadow Reference.RiscV.Sail
set_option autoImplicit false

/-- Full native matching roots each effective RAM address in real architectural
    inputs and each ROM-shadow address in independent public shadow seeds. The
    exact native port projection is derived; no local domain/value is supplied. -/
theorem public_word_memory_address_domains {trace : Data mersenne31Modulus NativeReducedFamily}
    {setup : SparseDecoderSetup WordMemoryMode} {initial : State} {cells : List Cell} {seeds : List ShadowSeed}
    {count logCapacity : Nat}
    (image : wordMemoryDecoderSetupImage initial count logCapacity = some setup)
    (inputs : ShadowImageBoundary (fixedData trace) initial cells seeds)
    (accepted : Accepted (fixedData trace)) (decoded : WordMemoryDecodedTrace (fixedData trace) setup)
    (row : Row mersenne31Modulus NativeReducedFamily) (present : row ∈ (fixedData trace).rows) :
    (64 ≤ (wordMemoryAddressWord row.assignment).hi →
      Cell.ram (wordMemoryAddressWord row.assignment).toBitVec ∈ cells) ∧
    ((wordMemoryAddressWord row.assignment).hi < 64 →
      ∃ seed ∈ seeds, seed.1 = (wordMemoryAddressWord row.assignment).toBitVec) :=
  NativeWordMemoryHistoryProofs.initialized_address_domains image inputs accepted decoded row present

end Airbender.ReducedMachine.Native
