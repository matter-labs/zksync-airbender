import Airbender.Proofs.Trace.Families.ReducedMachine.ShadowImage
import Airbender.Proofs.Mersenne31

namespace Airbender.ReducedMachine.Native
open Trace NativeShadow
set_option autoImplicit false

/-- Constructed architectural reads and independent public native shadow seeds
    derive the complete seed projection/uniqueness/clocks/ranges. No ROM byte read
    is fabricated from a shadow value; physical boot enforcement is separate. -/
theorem public_shadow_initialization {trace : Data mersenne31Modulus NativeReducedFamily}
    {before : Reference.RiscV.Sail.State} {cells : List Cell} {seeds : List ShadowSeed}
    (inputs : ShadowImageBoundary trace before cells seeds) :
    initialImage before cells = some (trace.initialMemory.filter fun token => architecturalAddress token.address) ∧
      (trace.initialMemory.map MemoryToken.address).Nodup ∧ ClockBoundary trace ∧
      (∀ token ∈ trace.initialMemory, token.word.Bounded) := NativeShadowProofs.seed_initialization (by decide) inputs

end Airbender.ReducedMachine.Native
