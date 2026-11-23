module
public import Human.Trace.Families.AddSub.RVTheorems
public import Proven.Trace.Family.RVExecution

@[expose] public section

namespace Airbender.Trace

/-- ADD/SUB and word-memory rows, in native time order, are a run of `RV.step` from the public starting state
    reaching the terminal PC and cell values (LW to x0 is a no-op in our spec: the Airbender profile). -/
theorem rv_airbender_soundness : RVAirbenderSoundnessClaim := by
  intro trace initial cells program inputs accepted decoded
  exact Proofs.rv_family_execution (by decide) (by decide) inputs accepted decoded

/-- The same rows from native boot, RAM seeded by the inits/teardowns instances (no ROM view: ROM-range RAM tokens are
    the shadow RAM, zero at boot). -/
theorem rv_native_boot_soundness : RVNativeBootSoundnessClaim := by
  intro trace initial cells program inits inputs accepted decoded
  exact Proofs.rv_family_execution (by decide) (by decide) (Proofs.rv_family_boot_boundary inputs)
    accepted decoded

end Airbender.Trace
