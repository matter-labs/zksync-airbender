import Airbender.Review.Bigint.Artifact

namespace Airbender.Bigint

set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

theorem timestamp_count {p : Nat} [Fact p.Prime] :
    (FlatOperation.lookups (importedConstraintsTimestampLookups (p := p))).length = 40 := rfl

theorem delegation_columns : importedConstraintsDelegationColumns =
    (⟨0, #v[1, 2], (Vector.ofFn (fun i : Fin 19 =>
      Trace.TimestampPort.mk 2 #v[217 + 3 * i.val, 218 + 3 * i.val]
        (219 + 3 * i.val))).toArray⟩ : Delegation.ClockColumns) := by decide

theorem memory_clocks : importedConstraintsMemoryPorts.map Trace.MemoryPort.clock =
    importedConstraintsDelegationColumns.ports := by
  simp [importedConstraintsMemoryPorts, importedConstraintsDelegationColumns]

theorem constraint_count {p : Nat} [Fact p.Prime] (setup : Table (ZMod p) (fields 3)) :
    (FlatOperation.constraints (importedConstraints setup)).length = 136 := rfl

theorem lookup_count {p : Nat} [Fact p.Prime] (setup : Table (ZMod p) (fields 3)) :
    (FlatOperation.lookups (importedConstraints setup)).length = 95 := rfl

theorem control_roles :
    importedConstraintsVariableNames.lookup 55 = some "control read/write from x12 read[0]" ∧
    importedConstraintsVariableNames.lookup 56 = some "control read/write from x12 read[1]" ∧
    importedConstraintsVariableNames.lookup 57 = some "control read/write from x12 write[0]" ∧
    importedConstraintsVariableNames.lookup 58 = some "control read/write from x12 write[0]" := by decide

theorem operand_roles (i : Fin 16) :
    importedConstraintsVariableNames.lookup Variables.leftLimbs[i] =
      some s!"state read/write from x10 indirect access {i.val / 2} read[{i.val % 2}]" ∧
    importedConstraintsVariableNames.lookup Variables.rightLimbs[i] =
      some s!"input read from x11 indirect access {i.val / 2} read[{i.val % 2}]" ∧
    importedConstraintsVariableNames.lookup Variables.writtenLimbs[i] =
      some s!"state read/write from x10 indirect access {i.val / 2} write[{i.val % 2}]" := by
  fin_cases i <;> decide

end Airbender.Bigint
