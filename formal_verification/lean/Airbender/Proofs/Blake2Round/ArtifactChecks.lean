import Airbender.Review.Blake2Round.Artifact

namespace Airbender.Blake2Round

set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

theorem state_port_layout (i : Fin 24) : importedConstraintsIndirectPorts[i.val] =
    Verification.IndirectPort.mk 10 i.val #v[3, 4] 0 none (4 * i.val)
      #v[5 + 4 * i.val, 6 + 4 * i.val] (some #v[7 + 4 * i.val, 8 + 4 * i.val]) := by
  fin_cases i <;> rfl

theorem message_port_layout (i : Fin 16) : importedConstraintsIndirectPorts[24 + i.val] =
    Verification.IndirectPort.mk 11 i.val #v[101, 102] 0 none (4 * i.val)
      #v[103 + 2 * i.val, 104 + 2 * i.val] none := by
  fin_cases i <;> rfl

theorem timestamp_count {p : Nat} [Fact p.Prime] :
    (FlatOperation.lookups (importedConstraintsTimestampLookups (p := p))).length = 88 := rfl

theorem delegation_columns : importedConstraintsDelegationColumns =
    (⟨0, #v[1, 2], (Vector.ofFn (fun i : Fin 43 =>
      Trace.TimestampPort.mk 2 #v[740 + 3 * i.val, 741 + 3 * i.val]
        (742 + 3 * i.val))).toArray⟩ : Delegation.ClockColumns) := by decide

theorem memory_clocks : importedConstraintsMemoryPorts.map Trace.MemoryPort.clock =
    importedConstraintsDelegationColumns.ports := by
  simp [importedConstraintsMemoryPorts, importedConstraintsDelegationColumns]

theorem constraint_count {p : Nat} [Fact p.Prime] (setup : Table (ZMod p) (fields 4)) :
    (FlatOperation.constraints (importedConstraints setup)).length = 352 := rfl

theorem lookup_count {p : Nat} [Fact p.Prime] (setup : Table (ZMod p) (fields 4)) :
    (FlatOperation.lookups (importedConstraints setup)).length = 210 := rfl

theorem variable_roles :
    importedConstraintsVariableNames.lookup 0 = some "Execute flag for cycle" ∧
    importedConstraintsVariableNames.lookup 135 = some "control read/write from x12 read[0]" ∧
    importedConstraintsVariableNames.lookup 136 = some "control read/write from x12 read[1]" ∧
    importedConstraintsVariableNames.lookup 137 = some "control read/write from x12 write[0]" ∧
    importedConstraintsVariableNames.lookup 138 = some "control read/write from x12 write[0]" ∧
    importedConstraintsVariableNames.lookup 152 = some "perform final xor flag" := by
  repeat' apply And.intro
  all_goals decide

theorem pointer_roles :
    importedConstraintsVariableNames.lookup 3 = some "state read/write from x10 read[0]" ∧
    importedConstraintsVariableNames.lookup 4 = some "state read/write from x10 read[1]" ∧
    importedConstraintsVariableNames.lookup 101 = some "input read from x11 read[0]" ∧
    importedConstraintsVariableNames.lookup 102 = some "input read from x11 read[1]" := by
  repeat' apply And.intro
  all_goals decide

theorem preparation_roles :
    (∀ i : Fin 8,
      importedConstraintsVariableNames.lookup Variables.stateReads[i].1 =
        some s!"state read/write from x10 indirect access {i.val} read[0]" ∧
      importedConstraintsVariableNames.lookup Variables.stateReads[i].2 =
        some s!"state read/write from x10 indirect access {i.val} read[1]") ∧
    (∀ i : Fin 16,
      importedConstraintsVariableNames.lookup Variables.extendedReads[i].1 =
        some s!"state read/write from x10 indirect access {8 + i.val} read[0]" ∧
      importedConstraintsVariableNames.lookup Variables.extendedReads[i].2 =
        some s!"state read/write from x10 indirect access {8 + i.val} read[1]") ∧
    (∀ i : Fin 16,
      importedConstraintsVariableNames.lookup Variables.messageReads[i].1 =
        some s!"input read from x11 indirect access {i.val} read[0]" ∧
      importedConstraintsVariableNames.lookup Variables.messageReads[i].2 =
        some s!"input read from x11 indirect access {i.val} read[1]") := by
  refine ⟨?_, ?_, ?_⟩
  all_goals intro i
  all_goals fin_cases i <;>
    simp only [Variables.stateReads, Variables.extendedReads, Variables.messageReads,
      Fin.getElem_fin, Vector.getElem_ofFn] <;> decide

end Airbender.Blake2Round
