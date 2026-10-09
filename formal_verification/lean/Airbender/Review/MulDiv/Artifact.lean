import Airbender.Import.Embed

namespace Airbender.MulDiv

-- Retained equations, fixed queries and native trace/decoder metadata.
-- Logical matching and modeled fixed-table provenance remain external.
import_clean importedConstraints from "../../cs/compiled_circuits/unsigned_mul_div_layout_no_caches_gkr.json" mul_div_lookups trace_metadata

def clockConstraints {p : Nat} [Fact p.Prime] : List (FlatOperation (ZMod p)) :=
  importedConstraints ++ importedConstraintsTimestampLookups

theorem timestamp_count {p : Nat} [Fact p.Prime] :
    (FlatOperation.lookups (importedConstraintsTimestampLookups (p := p))).length = 8 := rfl

theorem clock_columns : importedConstraintsTraceColumns =
    (⟨4, #v[0, 1], #v[14, 15], #v[2, 3], #v[16, 17],
      #[⟨0, #v[18, 19], 65⟩, ⟨1, #v[22, 23], 66⟩, ⟨2, #v[30, 31], 67⟩]⟩ :
      Trace.TraceColumns) := rfl

theorem memory_ports : importedConstraintsMemoryPorts =
    (#[⟨⟨0, #v[18, 19], 65⟩, .register 5, #v[20, 21], none⟩,
       ⟨⟨1, #v[22, 23], 66⟩, .register 6, #v[24, 25], none⟩,
       ⟨⟨2, #v[30, 31], 67⟩, .register 7, #v[26, 27], some #v[28, 29]⟩] :
      Array Trace.MemoryPort) := rfl

theorem memory_clocks : importedConstraintsMemoryPorts.map Trace.MemoryPort.clock =
    importedConstraintsTraceColumns.ports := by
  simp [importedConstraintsMemoryPorts, importedConstraintsTraceColumns]

theorem decoder_columns : importedConstraintsDecoderColumns =
    (⟨5, 6, 7, #v[8, 9], none, #[10, 11, 12, 13]⟩ : Trace.DecoderColumns) := rfl

theorem constraint_count {p : Nat} [Fact p.Prime] :
    (FlatOperation.constraints (importedConstraints (p := p))).length = 43 := rfl

theorem lookup_count {p : Nat} [Fact p.Prime] :
    (FlatOperation.lookups (importedConstraints (p := p))).length = 16 := rfl

/-- Guard numeric proof roles against changes in the imported metadata. -/
theorem variable_roles :
    importedConstraintsVariableNames.lookup 0 = some "initial_pc[0]" ∧
    importedConstraintsVariableNames.lookup 1 = some "initial_pc[1]" ∧
    importedConstraintsVariableNames.lookup 4 = some "Execute flag for cycle" ∧
    importedConstraintsVariableNames.lookup 5 = some "rs1 index from decoder" ∧
    importedConstraintsVariableNames.lookup 6 = some "rs2 index from decoder" ∧
    importedConstraintsVariableNames.lookup 7 = some "rd index from decoder" ∧
    importedConstraintsVariableNames.lookup 10 = some "family_bit[0]" ∧
    importedConstraintsVariableNames.lookup 11 = some "family_bit[1]" ∧
    importedConstraintsVariableNames.lookup 12 = some "family_bit[2]" ∧
    importedConstraintsVariableNames.lookup 13 = some "family_bit[3]" ∧
    importedConstraintsVariableNames.lookup 14 = some "final_pc[0]" ∧
    importedConstraintsVariableNames.lookup 15 = some "final_pc[1]" ∧
    importedConstraintsVariableNames.lookup 16 = some "final_ts[0]" ∧
    importedConstraintsVariableNames.lookup 17 = some "final_ts[1]" ∧
    importedConstraintsVariableNames.lookup 20 = some "rs1 read_value[0]" ∧
    importedConstraintsVariableNames.lookup 21 = some "rs1 read_value[1]" ∧
    importedConstraintsVariableNames.lookup 24 = some "rs2 read_value[0]" ∧
    importedConstraintsVariableNames.lookup 25 = some "rs2 read_value[1]" ∧
    importedConstraintsVariableNames.lookup 28 = some "rd[0]" ∧
    importedConstraintsVariableNames.lookup 29 = some "rd[1]" ∧
    importedConstraintsVariableNames.lookup 32 = some "RS2 is zero out var" ∧
    importedConstraintsVariableNames.lookup 33 = some "Divisor byte 0" ∧
    importedConstraintsVariableNames.lookup 34 = some "Divisor byte 2" ∧
    importedConstraintsVariableNames.lookup 35 = some "Quotient byte 0" ∧
    importedConstraintsVariableNames.lookup 36 = some "Quotient byte 2" ∧
    importedConstraintsVariableNames.lookup 37 = some "Extra U16 witness low" ∧
    importedConstraintsVariableNames.lookup 38 = some "Extra U16 witness high" ∧
    importedConstraintsVariableNames.lookup 39 = some "Remainder comparison U16 witness low" ∧
    importedConstraintsVariableNames.lookup 40 = some "Remainder comparison U16 witness high" ∧
    importedConstraintsVariableNames.lookup 41 = some "Intermediate carry witness[0]" ∧
    importedConstraintsVariableNames.lookup 42 = some "Intermediate carry witness[1]" ∧
    importedConstraintsVariableNames.lookup 43 = some "Intermediate carry witness[2]" ∧
    importedConstraintsVariableNames.lookup 44 = some "divisor is zero if division at layer 1" ∧
    importedConstraintsVariableNames.lookup 45 = some "low[0] at layer 1" ∧
    importedConstraintsVariableNames.lookup 46 = some "low[1] at layer 1" ∧
    importedConstraintsVariableNames.lookup 47 = some "high[0] at layer 1" ∧
    importedConstraintsVariableNames.lookup 48 = some "high[1] at layer 1" ∧
    importedConstraintsVariableNames.lookup 49 = some "quotient[0] at layer 1" ∧
    importedConstraintsVariableNames.lookup 50 = some "quotient[1] at layer 1" ∧
    importedConstraintsVariableNames.lookup 51 = some "remainder[0] at layer 1" ∧
    importedConstraintsVariableNames.lookup 52 = some "remainder[1] at layer 1" ∧
    importedConstraintsVariableNames.lookup 53 = some "divisor[0] at layer 1" ∧
    importedConstraintsVariableNames.lookup 54 = some "divisor[1] at layer 1" ∧
    importedConstraintsVariableNames.lookup 55 = some "is division family at layer 1" ∧
    importedConstraintsVariableNames.lookup 56 = some "Remainder comparison U16 witness low at layer 1" ∧
    importedConstraintsVariableNames.lookup 57 = some "Remainder comparison U16 witness high at layer 1" ∧
    importedConstraintsVariableNames.lookup 58 = some "divisor byte 0 at layer 1" ∧
    importedConstraintsVariableNames.lookup 59 = some "divisor byte 2 at layer 1" ∧
    importedConstraintsVariableNames.lookup 60 = some "quotient byte 0 at layer 1" ∧
    importedConstraintsVariableNames.lookup 61 = some "quotient byte 2 at layer 1" ∧
    importedConstraintsVariableNames.lookup 62 = some "intermediate carry witness[0] at layer 1" ∧
    importedConstraintsVariableNames.lookup 63 = some "intermediate carry witness[1] at layer 1" ∧
    importedConstraintsVariableNames.lookup 64 = some "intermediate carry witness[2] at layer 1" := by
  repeat' apply And.intro
  all_goals decide

end Airbender.MulDiv
