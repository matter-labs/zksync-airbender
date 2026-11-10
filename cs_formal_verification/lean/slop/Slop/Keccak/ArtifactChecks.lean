module
public import Human.Circuits.Keccak.Artifact
public import Slop.CleanCore.Circuit.Operations

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

end Airbender.Keccak
