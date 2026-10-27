import Airbender.Review.Helpers.Core.FieldCapacity
import Airbender.Review.Helpers.Core.SerializedInverse
import Airbender.Proofs.Bigint.MemorySoundness

namespace Airbender.Bigint.Memory

/-- The sixteen actual indirect addresses follow x10/x11's aligned 32-byte
    blocks. Pointer bounds come from public Sail initialization and accepted
    writes/reads; data-limb bounds are derived, while memory inputs retain
    clockRoom and invocationHigh. RAM-only ABI
    and full request/response execution are separate obligations. -/
theorem addresses_soundness [Fact p.Prime] (hp : FieldCapacity.AtLeast p 2097152)
    (inverse : SerializedInverse.Scale32 p) (data : Delegation.MemoryData p)
    (before : Reference.RiscV.Sail.State) (cells : List Trace.Cell) :
    (circuitModel data).SoundnessUnder (InterfaceAssumptions data before cells) Addresses.spec :=
  Proofs.addresses_soundness hp inverse data before cells

end Airbender.Bigint.Memory
