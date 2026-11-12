module
public import Human.Circuits.Bigint.RVMemory
public import Human.Helpers.Core.BabyBearPrime

@[expose] public section

-- The statements proven in proven/Proven/Final/Circuits/Bigint/RVTheorems.lean (checked by verify.sh). The public starting point is an `RV.State`; RAM cells are RAM at any address, INCLUDING READ-WRITE
-- ACCESS TO THE SHADOW RAM BELOW `ROM_END` (`RV.State.delegationRAM`): no pointer is required to be at or above
-- `ROM_END`.

namespace Airbender.Bigint.Memory

/-- The sixteen actual indirect addresses follow x10/x11's aligned 32-byte
    blocks; pointer bounds come from the public `RV.State` initialization and accepted writes/reads. RAM cells include
    READ-WRITE ACCESS TO THE SHADOW RAM BELOW `ROM_END` (`RV.State.delegationRAM`). -/
def RVAddressesSoundnessClaim : Prop :=
  ∀ (data : Delegation.MemoryData babyBearModulus) (before : RV.State) (cells : List Trace.Cell),
    (circuitModel data).SoundnessUnder (RVInterfaceAssumptions data before cells) Addresses.spec

end Airbender.Bigint.Memory
