import Airbender.Review.Helpers.Memory.PublicImage
import Airbender.Review.Helpers.Memory.Projection
import Airbender.Review.Helpers.Context.WordMemory

namespace Airbender.WordMemory
open Trace

/-- Native RAM slots in the four-MiB ROM prefix. Their permutation values are
    separate from the physical bytes used by native ROM lookups and Sail. -/
def shadow (address : Nat) : Prop :=
  (Nat.unpair address).1 = 1 ∧ (Nat.unpair (Nat.unpair address).2).2 < 64

instance (address : Nat) : Decidable (shadow address) := inferInstanceAs
  (Decidable ((Nat.unpair address).1 = 1 ∧ (Nat.unpair (Nat.unpair address).2).2 < 64))

/-- Retain all GPRs and RAM outside the native ROM-shadow prefix. -/
def architecturalAddress (address : Nat) : Bool := !decide (shadow address)

/-- A public native shadow address and its initial RV32 value. Physical native
    boot/profile enforcement remains separate; no Sail byte read is performed. -/
abbrev ShadowSeed := BitVec 32 × BitVec 32

def shadowTokens (seeds : List ShadowSeed) : List (MemoryToken p) :=
  seeds.map fun seed => (Cell.ram seed.1).initialToken seed.2

/-- Read architectural cells from Sail, then retain independently supplied
    native shadow seeds. Every seed clock is zero and all words are canonical. -/
def shadowInitialImage (before : Reference.RiscV.Sail.State) (cells : List Cell)
    (seeds : List ShadowSeed) : Option (List (MemoryToken p)) :=
  (initialImage before cells).map (fun tokens => tokens ++ shadowTokens seeds)

/-- Logical public initialization with separate architectural and native-shadow
    domains. Native acceptance still matches every shadow token and timestamp.
    This does not assert the physical zero-boot profile or ROM-table binding. -/
structure ShadowImageBoundary {p : Nat} [Fact p.Prime]
    (trace : Data p WordMemoryFamily) (before : Reference.RiscV.Sail.State)
    (cells : List Cell) (seeds : List ShadowSeed) : Prop where
  domain : (cells ++ seeds.map (fun seed => Cell.ram seed.1)).Nodup
  architectural : ∀ cell ∈ cells, architecturalAddress cell.addressCode = true
  shadows : ∀ seed ∈ seeds, seed.1.toNat < 4194304
  image : shadowInitialImage before cells seeds = some trace.initialMemory
  initial : initialState before (4, 0) = some trace.initial

end Airbender.WordMemory
