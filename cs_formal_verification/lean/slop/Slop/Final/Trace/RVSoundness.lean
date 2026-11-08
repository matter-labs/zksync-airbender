module
public import Human.Trace.RVSoundness
public import Slop.Trace.RVPooled.Soundness
public import Slop.Trace.RVPooled.OracleSoundness
public import Slop.Trace.RVPooledLawsProof

@[expose] public section

namespace Airbender.Trace

/-- Every accepted six-family trace booted from the public state `initial` (RAM seeded by the inits/teardowns
    instances `inits`) is a run of our spec reaching its terminal PC and tracked cell values. -/
theorem rv_pooled_native_soundness : RVPooledNativeSoundnessClaim := by
  intro trace initial cells program inits inputs accepted decoded
  exact Proofs.rv_pooled_trace_execution Proofs.rvPooledLaws (by decide) (by decide) inputs
    (Proofs.rv_boot_seed inputs) accepted decoded

/-- Under the boot inputs every tracked RAM cell of the starting state reads 0 (Airbender's zero starting RAM for the
    tracked cells), from the inits/teardowns circuit's `Init` tokens. -/
theorem boot_ram_zero : BootRamZeroClaim := by
  intro trace initial cells program inits projection inputs
  exact Proofs.boot_ram_zero inputs

/-- The six families plus the CSR 0x7C0 read/write forms: the input stream is `initial.input`, the read rows' values
    are its words in clock order (`StreamPorts`), and the run consumes exactly the trace's reads. -/
theorem NonDeterminism.Pooled.rv_native_soundness : NonDeterminism.Pooled.RVNativeSoundnessClaim := by
  intro trace initial cells program inits inputs accepted decoded ports
  exact Proofs.rv_oracle_trace_execution Proofs.rvPooledLaws.clockLaws (by decide) (by decide) inputs
    (Proofs.rv_boot_seed inputs) accepted decoded ports

end Airbender.Trace
