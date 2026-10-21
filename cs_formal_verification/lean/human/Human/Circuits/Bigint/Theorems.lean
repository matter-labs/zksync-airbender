import Human.Circuits.Bigint.Memory

-- The statements proven in slop/Slop/Final/Circuits/Bigint/Theorems.lean (checked by verify.sh).

namespace Airbender.Bigint.Memory

/-- The sixteen actual indirect addresses follow x10/x11's aligned 32-byte
    blocks. Pointer bounds come from public Sail initialization and accepted
    writes/reads; no per-row range premise remains in this claim. RAM-only ABI
    and full request/response execution are separate obligations. -/
def AddressesSoundnessClaim : Prop :=
  ∀ {p : Nat} [Fact p.Prime] (hp : 2097152 ≤ p) (inverse : 32 * (-62914560 : ZMod p) = 1) (data : Delegation.MemoryData p) (before : Reference.RiscV.Sail.State) (cells : List Trace.Cell),
    (circuitModel data).SoundnessUnder (InterfaceAssumptions data before cells) Addresses.spec

end Airbender.Bigint.Memory
