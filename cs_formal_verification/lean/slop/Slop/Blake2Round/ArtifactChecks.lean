module
public import Human.Circuits.Blake2Round.Artifact
public import Mathlib.Data.Nat.Bitwise
public import Slop.CleanCore.Circuit.Operations

@[expose] public section

namespace Airbender.Blake2Round

set_option maxRecDepth 16384

theorem state_port_layout (i : Fin 24) : importedConstraintsIndirectPorts[i.val] =
    Verification.IndirectPort.mk 10 i.val #v[3, 4] 0 none (4 * i.val)
      #v[5 + 4 * i.val, 6 + 4 * i.val] (some #v[7 + 4 * i.val, 8 + 4 * i.val]) := by
  fin_cases i <;> rfl

theorem message_port_layout (i : Fin 16) : importedConstraintsIndirectPorts[24 + i.val] =
    Verification.IndirectPort.mk 11 i.val #v[101, 102] 0 none (4 * i.val)
      #v[103 + 2 * i.val, 104 + 2 * i.val] none := by
  fin_cases i <;> rfl

theorem timestamp_count {p : Nat} [Fact p.Prime] :
    (FlatOperation.lookups (importedConstraintsTimestampLookups (p := p))).length = 89 := by rfl

theorem delegation_columns : importedConstraintsDelegationColumns =
    (⟨0, #v[1, 2], (Vector.ofFn (fun i : Fin 43 =>
      Trace.TimestampPort.mk 2 #v[632 + 3 * i.val, 633 + 3 * i.val]
        (634 + 3 * i.val))).toArray⟩ : Delegation.ClockColumns) := by decide

theorem memory_clocks : importedConstraintsMemoryPorts.map Trace.MemoryPort.clock =
    importedConstraintsDelegationColumns.ports := by
  simp [importedConstraintsMemoryPorts, importedConstraintsDelegationColumns]

theorem constraint_count {p : Nat} [Fact p.Prime] (setup : Table (ZMod p) (fields 6)) :
    (FlatOperation.constraints (importedConstraints setup)).length = 220 := by rfl

theorem lookup_count {p : Nat} [Fact p.Prime] (setup : Table (ZMod p) (fields 6)) :
    (FlatOperation.lookups (importedConstraints setup)).length = 194 := by rfl

end Airbender.Blake2Round
