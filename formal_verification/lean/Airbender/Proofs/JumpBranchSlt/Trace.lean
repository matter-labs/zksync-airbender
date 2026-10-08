import Airbender.Review.JumpBranchSlt.Trace
import Airbender.Proofs.JumpBranchSlt.Timestamp
import Airbender.Proofs.Trace.LatestReads
import Airbender.Proofs.Trace.MemoryHistory

namespace Airbender.JumpBranchSlt.Proofs
open Trace

/-- The shared complete-path/latest-read proofs use these checked local laws;
    no jump-specific state or memory consistency premise is added. -/
instance [Fact p.Prime] : Trace.Proofs.ClockLaws TraceKind p where
  finalBound _ row h := final_clock_bound h
  advance hp inverse _ row h bound := by
    have core := Verification.holds_of_sublist h
      (List.sublist_append_left importedConstraints importedConstraintsTimestampLookups)
    obtain ⟨carry, bit, low, high⟩ := timestamp_equations inverse core
    have final := final_clock_bound h
    apply Trace.Proofs.increment hp bound final bit
    · simpa [Row.columns, importedConstraintsTraceColumns, decodeTimestamp, timestampBase,
        ZMod.natCast_zmod_val] using low
    · simpa [Row.columns, importedConstraintsTraceColumns, decodeTimestamp, timestampBase,
        ZMod.natCast_zmod_val] using high
  portsClocks _ := memory_clocks
  offsets _ := rfl
  effects hp inverse _ _ h inputs := clocks hp inverse h inputs

end Airbender.JumpBranchSlt.Proofs
