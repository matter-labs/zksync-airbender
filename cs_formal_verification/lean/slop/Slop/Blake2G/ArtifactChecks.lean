module
public import Human.Circuits.Blake2G.Artifact
public import Slop.CleanCore.Circuit.Operations

@[expose] public section

namespace Airbender.Blake2G

theorem indirect_port_layout : importedConstraintsIndirectPorts = #v[
    Verification.IndirectPort.mk 10 0 #v[13, 14] 4 (some 7) 0 #v[15, 16] (some #v[17, 18]),
    Verification.IndirectPort.mk 10 1 #v[13, 14] 4 (some 8) 0 #v[19, 20] (some #v[21, 22]),
    Verification.IndirectPort.mk 10 2 #v[13, 14] 4 (some 9) 0 #v[23, 24] (some #v[25, 26]),
    Verification.IndirectPort.mk 10 3 #v[13, 14] 4 (some 10) 0 #v[27, 28] (some #v[29, 30]),
    Verification.IndirectPort.mk 11 0 #v[31, 32] 4 (some 11) 0 #v[33, 34] none,
    Verification.IndirectPort.mk 11 1 #v[31, 32] 4 (some 12) 0 #v[35, 36] none] := by rfl

theorem timestamp_count {p : Nat} [Fact p.Prime] :
    (FlatOperation.lookups (importedConstraintsTimestampLookups (p := p))).length = 21 := by rfl

theorem delegation_columns : importedConstraintsDelegationColumns =
    (⟨0, #v[1, 2], (Vector.ofFn (fun i : Fin 9 =>
      Trace.TimestampPort.mk 2 #v[83 + 3 * i.val, 84 + 3 * i.val]
        (85 + 3 * i.val))).toArray⟩ : Delegation.ClockColumns) := by decide

theorem memory_clocks : importedConstraintsMemoryPorts.map Trace.MemoryPort.clock =
    importedConstraintsDelegationColumns.ports := by
  simp [importedConstraintsMemoryPorts, importedConstraintsDelegationColumns]

theorem constraint_count {p : Nat} [Fact p.Prime] (setup : Table (ZMod p) (fields 9)) :
    (FlatOperation.constraints (importedConstraints setup)).length = 32 := by rfl

theorem lookup_count {p : Nat} [Fact p.Prime] (setup : Table (ZMod p) (fields 9)) :
    (FlatOperation.lookups (importedConstraints setup)).length = 21 := by rfl

end Airbender.Blake2G
