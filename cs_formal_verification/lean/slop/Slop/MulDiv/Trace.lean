module
public import Human.Helpers.Context.Registries.MulDiv
public import Slop.MulDiv.Timestamp
public import Slop.Trace.RowHistory
public import Slop.MulDiv
public import Slop.Defs.Helpers.Context.Columns

@[expose] public section

namespace Airbender.MulDiv

@[simp] theorem trace_columns (kind : TraceKind) :
    Trace.CircuitLayout.columns kind = importedConstraintsTraceColumns := by rfl

@[simp] theorem trace_ports (kind : TraceKind) :
    Trace.CircuitLayout.ports kind = importedConstraintsMemoryPorts := by rfl

end Airbender.MulDiv

namespace Airbender.MulDiv.Proofs
open Trace

/-- Reuse the complete native path/history engine with imported clock laws. -/
instance nativeClockLaws [Fact p.Prime] : Trace.Proofs.ClockLaws TraceKind p where
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

/-- Both output PC limbs are ranged by imported queries, including the
    terminal boundary. No terminal normalization premise is needed here. -/
theorem outgoing_pc_bounds {p : Nat} [Fact p.Prime]
    {trace : NativeTrace p} (accepted : Accepted trace) :
    ∀ row ∈ trace.rows, row.finish.word.Bounded := by
  intro row member
  have h := Verification.holds_of_sublist (accepted.constraints row member)
    (List.sublist_append_left importedConstraints importedConstraintsTimestampLookups)
  have ranges := local_ranges h
  exact ⟨ranges ⟨6, by decide⟩, ranges ⟨7, by decide⟩⟩

end Airbender.MulDiv.Proofs
