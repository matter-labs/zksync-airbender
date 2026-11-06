import Slop.Trace.Family.Timestamps
import Slop.Trace.ROM
import Human.Helpers.Context.FamilyLayout
import Human.Helpers.Memory.ValueBoundary

namespace Airbender.Trace.ROM.Proofs
open Arithmetic

theorem value_boundary {p : Nat} [Fact p.Prime] (hp : limbBase < p)
    {trace : Data p} {before : Reference.RiscV.Sail.State} {cells : List Cell}
    (image : initialImage before cells = some trace.initialMemory)
    (setup : trace.rom = table cells trace.initialMemory) : ValueBoundary trace := by
  constructor
  · exact Trace.Proofs.image_bounds image
  · intro query contains inactive
    rw [setup] at contains
    exact disabled (by dsimp [limbBase] at hp; omega) image contains inactive
  · intro query contains
    rw [setup] at contains
    exact bounds hp image contains

end Airbender.Trace.ROM.Proofs
