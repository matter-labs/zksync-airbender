module
public import Human.Helpers.Context.Registries.SubwordMemory
public import Slop.SubwordMemory.Timestamp
public import Slop.Trace.RowHistory
public import Slop.SubwordMemory

@[expose] public section

namespace Airbender.SubwordMemory

@[simp] theorem trace_columns (kind : TraceKind) :
    Trace.CircuitLayout.columns kind = importedConstraintsTraceColumns := by rfl

@[simp] theorem trace_ports (kind : TraceKind) :
    Trace.CircuitLayout.ports kind = importedConstraintsMemoryPorts := by rfl

end Airbender.SubwordMemory

namespace Airbender.SubwordMemory.Proofs
open Trace

/-- Reuse the complete native path/history engine with imported clock laws. -/
instance nativeClockLaws [Fact p.Prime] : Trace.Proofs.ClockLaws TraceKind p where
  finalBound _ row h := final_clock_bound h
  advance hp inverse setup row h bound := by
    have core := Verification.holds_of_sublist h
      (List.sublist_append_left (importedConstraints setup) importedConstraintsTimestampLookups)
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

end Airbender.SubwordMemory.Proofs
