import Airbender.Review.Helpers.Memory.Initialization
import Airbender.Review.Helpers.Memory.ShadowImage

namespace Airbender.Trace.ROMView

/-- Native initialization: zero values for all tracked GPR/RAM slots, including
    ROM slots, with zero prior timestamps. The address domain is public. -/
def nativeBootImage {p : Nat} (cells : List Cell) : List (MemoryToken p) :=
  cells.map fun cell => cell.initialToken 0

end Airbender.Trace.ROMView

namespace Airbender.WordMemory
open Trace

/-- Public shadow addresses have the native zero value and prior timestamp.
    Physical ROM bytes remain separate; no Sail shadow read is performed. -/
def bootShadowSeeds (addresses : List (BitVec 32)) : List ShadowSeed :=
  addresses.map fun address => (address, 0)

/-- The fixed native zero-boot profile over a public address domain. This replaces
    arbitrary shadow values and initial seed/PC reads with the original initial
    Sail profile and native zero tokens. Rust/argument enforcement stays separate. -/
structure NativeBootBoundary {p : Nat} [Fact p.Prime]
    (trace : Data p WordMemoryFamily) (before : Reference.RiscV.Sail.State)
    (cells : List Cell) (shadows : List (BitVec 32)) : Prop where
  domain : (cells ++ shadows.map Cell.ram).Nodup
  architectural : ∀ cell ∈ cells, architecturalAddress cell.addressCode = true
  shadowsInROM : ∀ address ∈ shadows, address.toNat < 4194304
  profile : InitialProfile before cells
  seed : trace.initialMemory = ROMView.nativeBootImage (cells ++ shadows.map Cell.ram)
  initial : trace.initial = PCState.boundary 0 (4, 0)

end Airbender.WordMemory
