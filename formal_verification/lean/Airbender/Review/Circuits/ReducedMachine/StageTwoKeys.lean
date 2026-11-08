import Airbender.Review.Circuits.ReducedMachine.AddressSupport

namespace Airbender.NativeStageTwoKeys
open Airbender.Blake2Worker.Native
abbrev F := ZMod mersenne31Modulus

/-- Derived canonical pointer-base reads and no u16 carry at every actual
    active indirect port. No RAM-only/permission/alignment premise is supplied. -/
def IndirectBounds (w : Nat → F) : Prop := ∀ slot : Fin 43,
  match (keyDescriptor slot).location with
  | .register _ => True
  | .indirect base offset => (w base[0]).val < 65536 ∧
      (w base[1]).val < 65536 ∧ (w base[0]).val + offset < 65536

/-- Agreement of the existing modeled native STAGE2 helper keys and raw
    quotient keys. Rust memory, extension arithmetic, LDE/compiler refinement,
    current word-value bounds and worker/Sail semantics remain separate. -/
structure Effects {Setup R : Type} [Field R]
    (proofs : List (Airbender.NativeInitializationBatch.Proof R)) (batch : WorkerBatch Setup R)
    (inputs : Airbender.ReducedMachine.NativeMemoryBoundary.PublicBoundary) : Prop where
  addresses : Airbender.NativeAddressSupport.Effects proofs batch inputs
  indirects : ∀ w ∈ Airbender.NativeTokenLedger.workerRows batch, w constraintsABI.multiplicity = 1 → IndirectBounds w
  keys : ∀ w ∈ Airbender.NativeTokenLedger.workerRows batch, ∀ slot : Fin 43, ∀ write,
    stageTwoMemoryKey w slot write = some (quotientMemoryKey w slot write)
end Airbender.NativeStageTwoKeys
