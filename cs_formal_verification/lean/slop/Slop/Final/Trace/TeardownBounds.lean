module
public import Human.Trace.TeardownBounds
public import Slop.Trace.WriteSites
public import Slop.Trace.RVPooledBoot
public import Slop.Trace.RVPooled.Oracle
public import Slop.UnifiedReduced.RV.Execution

@[expose] public section

/-! The teardown-bound claims of `Human.Trace.TeardownBounds`: under `MemoryArgumentReadsBounded`, a teardown value is
    an `Init` tuple's zero or a write of the booted trace, which its history bounds. -/

namespace Airbender.Trace

/-- Six pooled families: every write of the booted, accepted, decoded trace is bounded (seeds from the RV image, write
    rules of the standard or extended table), so every teardown tuple carries a bounded word. -/
theorem teardowns_bounded : TeardownsBoundedClaim := by
  intro trace initial cells program inits projection table inputs accepted decoded reads
  obtain ⟨addresses, programImage⟩ := inputs.programImage
  have clocks := (inputs.native (by decide) (Proofs.rv_boot_seed inputs)).clocks
  have rules : Proofs.WriteBoundsFromReads trace := by
    rcases table with rfl | rfl
    · exact RVValues.rv_pooled_write_rules (by decide) accepted inputs.wordTable inputs.subwordSetup programImage
        decoded
    · exact Proofs.rv_oracle_write_rules (by decide) accepted inputs.wordTable inputs.subwordSetup programImage
        decoded
  exact InitsTeardowns.Proofs.teardowns_bounded reads (Proofs.row_writes_bounded
    (Proofs.write_bounds_of_rules (by decide) (by decide) accepted clocks (RVValues.rv_image_bounds inputs.image)
      rules))

end Airbender.Trace

namespace Airbender.UnifiedReduced
open Trace

/-- The unified reduced machine: every write of the booted, accepted trace is bounded (seeds from the RV image), so
    every teardown tuple carries a bounded word. -/
theorem teardowns_bounded : TeardownsBoundedClaim := by
  intro trace initial cells program inits inputs accepted reads
  have clocks := Trace.ROMView.native_clocks (by decide) (Proofs.RV.rv_boot_seed inputs) inputs.initialPC
  exact InitsTeardowns.Proofs.teardowns_bounded reads (Trace.Proofs.row_writes_bounded
    (Proofs.RV.rv_value_bounds (by decide) (by decide) accepted clocks inputs.image).2.1)

end Airbender.UnifiedReduced
