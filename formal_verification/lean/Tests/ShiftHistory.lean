import Tests.ShiftHistoryFixture

namespace Tests.ShiftHistory
open Airbender Trace ShiftBinop Tests.ShiftHistoryFixture Tests.ShiftHistoryRows
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

/-- Twenty-four complete initialized native traces construct actual Clean history
    from original Sail register/PC seed reads and logical native acceptance. -/
theorem public_history (sample : Fin 24) : ∃ history, MemoryHistory (trace sample) history :=
  (ShiftBinop.public_memory_soundness (public_inputs sample) (accepted sample)).1

theorem latest (sample : Fin 24) :
    ∀ port ∈ (nativeRow sample).ports, LatestRead (trace sample) (nativeRow sample) port :=
  (ShiftBinop.public_memory_soundness (public_inputs sample) (accepted sample)).2
    _ (by simp [trace])

/-- Initialization and native matching derive prior-clock bounds and alignment;
    the public claim needs no separately supplied local clock premise. -/
theorem derived_clocks (sample : Fin 24) :
    ClockInputs (nativeRow sample).columns (assignment sample) :=
  Trace.Proofs.clock_inputs (by decide) (accepted sample)
    (Trace.Proofs.image_clock_boundary (by decide) (public_inputs sample))
    (nativeRow sample) (by simp [trace])

theorem native_clock_advances (sample : Fin 24) :
    (decodeTimestamp (assignment sample) importedConstraintsTraceColumns.finalTime).value = 8 := by
  have advance := ShiftBinop.Proofs.clock_advance (by decide)
    (native_constraints sample) (derived_clocks sample).initial
  have initial : (decodeTimestamp (assignment sample)
      importedConstraintsTraceColumns.initialTime).value = 4 := by
    fin_cases sample <;> decide
  simpa only [initial] using advance

/-- The repaired immediate/x0 alias reads exactly the readonly refresh time. -/
theorem x0_alias_clock (sample : Fin 6) :
    (decodeTimestamp (assignment ⟨18 + sample.val, by omega⟩)
      importedConstraintsMemoryPorts[2].clock.previous).value = 5 := by
  fin_cases sample <;> decide

end Tests.ShiftHistory
