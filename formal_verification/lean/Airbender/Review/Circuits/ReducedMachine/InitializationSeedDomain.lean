import Airbender.Review.Circuits.ReducedMachine.InitializationLedger
import Airbender.Review.Helpers.Memory.InitialImage

namespace Airbender.NativeInitializationSeedDomain
open Airbender.NativeInitializationLedger
open Airbender.NativeInitializationBatch (Proof mainProofs)

/-- Actual ordinary rows after the proved six-field padding cancellation. This
    domain is observed from the SAME native proof list, not a public cell list. -/
def sources {R : Type} [Field R] (proofs : List (Proof R)) : List (Nat → F) :=
  (Airbender.NativeTokenLedger.mainRows (mainProofs proofs)).filter fun w => !paddingRow w

def tokens {R : Type} [Field R] (proofs : List (Proof R)) (write : Bool) : List (Trace.MemoryToken mersenne31Modulus) :=
  (sources proofs).map fun w => Airbender.NativeInitializationLedger.initializationToken w write

/-- Interpret the proved native RAM32 address as a canonical public-cell type.
    No Sail read, public-domain identity or architectural ROM value is supplied. -/
def cell (token : Trace.MemoryToken mersenne31Modulus) : Trace.Cell :=
  .ram (BitVec.ofNat 32 (addressValue token))

def cells {R : Type} [Field R] (proofs : List (Proof R)) : List Trace.Cell := (tokens proofs true).map cell

/-- Consequences of complete existing acceptance: actual observed seeds have
    unique addresses and exactly encode zero-valued canonical RAM cells. This
    is not ImageBoundary or ShadowImageBoundary on an independent public domain. -/
structure Effects {R : Type} [Field R] (proofs : List (Proof R)) : Prop where
  canonical : ∀ token ∈ tokens proofs true, ZeroSeed token
  addresses : ((tokens proofs true).map Trace.MemoryToken.address).Nodup
  domain : (cells proofs).Nodup
  encoding : tokens proofs true = (cells proofs).map (fun c => c.initialToken (p := mersenne31Modulus) 0)

end Airbender.NativeInitializationSeedDomain
