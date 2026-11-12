module
public import Proven.Bigint.RVMemorySoundness
public import Proven.Blake2G.Soundness
public import Proven.Final.Generic.Circuits.Bigint.RVTheorems
public import Proven.Field.BabyBearInstance

@[expose] public section

namespace Airbender.Bigint.Memory

/-- RV sibling of `addresses_soundness` (statement of `RVAddressesSoundnessClaim`): the sixteen actual indirect
    addresses follow x10/x11's aligned 32-byte blocks, from a public `RV.State` whose RAM cells include READ-WRITE
    ACCESS TO THE SHADOW RAM BELOW `ROM_END`. -/
private theorem rv_addresses_soundness_generic [Fact p.Prime] (_hp : 2097152 ≤ p)
    (inverse : 32 * (-62914560 : ZMod p) = 1) (data : Delegation.MemoryData p)
    (before : RV.State) (cells : List Trace.Cell) :
    (circuitModel data).SoundnessUnder (RVInterfaceAssumptions data before cells) Addresses.spec := by
  -- the serialized inverse fixes p = BabyBear, above the proof's 2^24 alignment capacity
  have field : p = babyBearModulus :=
    Blake2G.Proofs.serialized_field (by linear_combination inverse)
  exact Proofs.rv_addresses_soundness (by rw [field]; unfold babyBearModulus; norm_num)
    inverse data before cells

theorem rv_addresses_soundness : Airbender.Bigint.Memory.RVAddressesSoundnessClaim := by babybear_instance rv_addresses_soundness_generic

end Airbender.Bigint.Memory
