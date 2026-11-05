import Slop.Bigint.MemorySoundness
import Slop.Blake2G.Soundness

namespace Airbender.Bigint.Memory

/-- The sixteen actual indirect addresses follow x10/x11's aligned 32-byte
    blocks. Pointer bounds come from public Sail initialization and accepted
    writes/reads; no per-row range premise remains in this claim. RAM-only ABI
    and full request/response execution are separate obligations. -/
theorem addresses_soundness [Fact p.Prime] (_hp : 2097152 ≤ p)
    (inverse : 32 * (-62914560 : ZMod p) = 1) (data : Delegation.MemoryData p)
    (before : Reference.RiscV.Sail.State) (cells : List Trace.Cell) :
    (circuitModel data).SoundnessUnder (InterfaceAssumptions data before cells) Addresses.spec := by
  -- the serialized inverse fixes p = BabyBear, above the proof's 2^24 alignment capacity
  have field : p = babyBearModulus :=
    Blake2G.Proofs.serialized_field (by linear_combination inverse)
  exact Proofs.addresses_soundness (by rw [field]; unfold babyBearModulus; norm_num)
    inverse data before cells

end Airbender.Bigint.Memory
