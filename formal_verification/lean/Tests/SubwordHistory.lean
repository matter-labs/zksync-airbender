import Tests.SubwordHistoryStale

namespace Tests.SubwordHistory
open Airbender Trace SubwordMemory Tests.SubwordHistoryFixture Tests.SubwordHistoryRows
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

theorem public_history (sample : Fin 8) : ∃ history, MemoryHistory (trace sample) history :=
  (SubwordMemory.public_memory_soundness (public_inputs sample) (accepted sample)).1

theorem latest (sample : Fin 8) :
    ∀ port ∈ (nativeRow sample).ports, LatestRead (trace sample) (nativeRow sample) port :=
  (SubwordMemory.public_memory_soundness (public_inputs sample) (accepted sample)).2
    _ (by simp [trace])

theorem derived_clocks (sample : Fin 8) : ClockInputs (nativeRow sample).columns (assignment sample) :=
  Trace.Proofs.clock_inputs (by decide) (accepted sample)
    (Trace.Proofs.image_clock_boundary (by decide) (public_inputs sample))
    (nativeRow sample) (by simp [trace])

theorem native_clock_advances (sample : Fin 8) :
    (decodeTimestamp (assignment sample) importedConstraintsTraceColumns.finalTime).value = 8 := by
  have advance := SubwordMemory.Proofs.clock_advance (by decide)
    (native_constraints sample) (derived_clocks sample).initial
  have initial : (decodeTimestamp (assignment sample) importedConstraintsTraceColumns.initialTime).value = 4 := by
    fin_cases sample <;> decide +kernel
  simpa only [initial] using advance

/-- The alias consumes the source's readonly refresh, not its initial token. -/
theorem alias_clock :
    (decodeTimestamp (assignment ⟨7,by decide⟩) importedConstraintsMemoryPorts[2].clock.previous).value = 4 := by
  decide +kernel

theorem actual_store_writes :
    assignment ⟨4,by decide⟩ 39 = 17767 ∧ assignment ⟨4,by decide⟩ 40 = 43981 ∧
    assignment ⟨5,by decide⟩ 39 = 4779 ∧ assignment ⟨5,by decide⟩ 40 = 35277 := by
  decide +kernel

theorem actual_x0_write : assignment ⟨3,by decide⟩ 39 = 0 ∧ assignment ⟨3,by decide⟩ 40 = 0 := by
  decide +kernel

/-- Project native matching to timestamp multiplicities first; the missing
    readonly-refresh consumer is rejected without reducing word/address values. -/
theorem stale_alias_rejected : ¬Accepted Tests.SubwordHistoryStale.staleTrace := by
  intro h
  have count := (h.memory.map MemoryToken.time).count_eq ((4 : ZMod mersenne31Modulus),0)
  revert count
  decide +kernel

end Tests.SubwordHistory
