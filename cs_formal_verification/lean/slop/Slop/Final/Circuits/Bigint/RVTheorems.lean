module
public import Slop.Bigint.RVMemorySoundness
public import Slop.Blake2G.Soundness
public import Human.Circuits.Bigint.RVTheorems

@[expose] public section

namespace Airbender.Bigint.Memory

/-- RV sibling of `addresses_soundness` (statement of `RVAddressesSoundnessClaim`): the sixteen actual indirect
    addresses follow x10/x11's aligned 32-byte blocks, from a public `RV.State` whose RAM cells include READ-WRITE
    ACCESS TO THE SHADOW RAM BELOW `ROM_END`. -/
theorem rv_addresses_soundness [Fact p.Prime] (_hp : 2097152 ≤ p)
    (inverse : 32 * (-62914560 : ZMod p) = 1) (data : Delegation.MemoryData p)
    (before : RV.State) (cells : List Trace.Cell) :
    (circuitModel data).SoundnessUnder (RVInterfaceAssumptions data before cells) Addresses.spec := by
  -- the serialized inverse fixes p = BabyBear, above the proof's 2^24 alignment capacity
  have field : p = babyBearModulus :=
    Blake2G.Proofs.serialized_field (by linear_combination inverse)
  exact Proofs.rv_addresses_soundness (by rw [field]; unfold babyBearModulus; norm_num)
    inverse data before cells

end Airbender.Bigint.Memory
