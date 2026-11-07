import Human.Trace.RVSoundness
import Slop.Trace.RVPooled.Soundness
import Slop.Trace.RVPooledLawsProof

namespace Airbender.Trace

/-- Every accepted six-family trace booted from the public state `initial` (RAM seeded by the inits/teardowns
    instances `inits`) is a run of our spec reaching its terminal PC and tracked cell values. -/
theorem rv_pooled_native_soundness : RVPooledNativeSoundnessClaim := by
  intro trace initial cells program inits inputs accepted decoded
  exact Proofs.rv_pooled_trace_execution Proofs.rvPooledLaws (by decide) (by decide) inputs
    (Proofs.rv_boot_seed inputs) accepted decoded

/-- Under the boot inputs every tracked RAM cell of the starting state reads 0 (`RV.State.RamStartsZero` for the
    tracked cells), from the inits/teardowns circuit's `Init` tokens. -/
theorem boot_ram_zero : BootRamZeroClaim := by
  intro trace initial cells program inits projection inputs
  exact Proofs.boot_ram_zero inputs

end Airbender.Trace
