module
public import Human.Circuits.Keccak.Artifact
import all Init.Data.Array.DecidableEq -- until Lean 4.35 exposes Array/Vector ofFn/DecidableEq (lean4#14989, #14988, #14270)
import all Init.Data.Vector.Basic -- until Lean 4.35 exposes Array/Vector ofFn/DecidableEq (lean4#14989, #14988, #14270)

@[expose] public section

namespace Airbender.Keccak

set_option maxRecDepth 16384

theorem timestamp_count {p : Nat} [Fact p.Prime] :
    (FlatOperation.lookups (importedConstraintsTimestampLookups (p := p))).length = 30 := by rfl

theorem delegation_columns : importedConstraintsDelegationColumns =
    (⟨0, #v[1, 2], (Vector.ofFn (fun i : Fin 14 =>
      Trace.TimestampPort.mk 2 #v[222 + 3 * i.val, 223 + 3 * i.val]
        (224 + 3 * i.val))).toArray⟩ : Delegation.ClockColumns) := by decide

theorem memory_clocks : importedConstraintsMemoryPorts.map Trace.MemoryPort.clock =
    importedConstraintsDelegationColumns.ports := by
  simp [importedConstraintsMemoryPorts, importedConstraintsDelegationColumns]

theorem constraint_count {p : Nat} [Fact p.Prime] (setup : Table (ZMod p) (fields 8)) :
    (FlatOperation.constraints (importedConstraints setup)).length = 187 := by rfl

theorem port_layout : importedConstraintsIndirectPorts =
    Vector.ofFn (fun i : Fin 12 => Verification.IndirectPort.mk 11 i.val #v[13, 14]
      8 (some (7 + i.val / 2)) (4 * (i.val % 2))
      #v[15 + 4 * i.val, 16 + 4 * i.val]
      (some #v[17 + 4 * i.val, 18 + 4 * i.val])) := by decide

theorem variable_roles :
    importedConstraintsVariableNames.lookup 0 = some "Execute flag for cycle" ∧
    importedConstraintsVariableNames.lookup 3 = some "x10 control register read/write read[0]" ∧
    importedConstraintsVariableNames.lookup 4 = some "x10 control register read/write read[1]" ∧
    importedConstraintsVariableNames.lookup 5 = some "x10 control register read/write write[0]" ∧
    importedConstraintsVariableNames.lookup 6 = some "x10 control register read/write write[0]" ∧
    importedConstraintsVariableNames.lookup 13 = some "x11 indirect access read[0]" ∧
    importedConstraintsVariableNames.lookup 14 = some "x11 indirect access read[1]" := by decide

end Airbender.Keccak
