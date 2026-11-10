module
public import Human.Circuits.Bigint.RVMemory

@[expose] public section

-- The statements proven in slop/Slop/Final/Circuits/Bigint/RVTheorems.lean (checked by verify.sh). The public starting point is an `RV.State`; RAM cells are RAM at any address, INCLUDING READ-WRITE
-- ACCESS TO THE SHADOW RAM BELOW `ROM_END` (`RV.State.delegationRAM`): no pointer is required to be at or above
-- `ROM_END`.

namespace Airbender.Bigint.Memory

/-- The sixteen actual indirect addresses follow x10/x11's aligned 32-byte
    blocks; pointer bounds come from the public `RV.State` initialization and accepted writes/reads. RAM cells include
    READ-WRITE ACCESS TO THE SHADOW RAM BELOW `ROM_END` (`RV.State.delegationRAM`). -/
def RVAddressesSoundnessClaim : Prop :=
  ∀ {p : Nat} [Fact p.Prime] (_hp : 2097152 ≤ p) (_inverse : 32 * (-62914560 : ZMod p) = 1) (data : Delegation.MemoryData p) (before : RV.State) (cells : List Trace.Cell),
    (circuitModel data).SoundnessUnder (RVInterfaceAssumptions data before cells) Addresses.spec

end Airbender.Bigint.Memory
