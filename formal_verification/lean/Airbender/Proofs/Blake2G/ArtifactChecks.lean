import Airbender.Review.Circuits.Blake2G.Artifact

namespace Airbender.Blake2G

theorem indirect_port_layout : importedConstraintsIndirectPorts = #v[
    Verification.IndirectPort.mk 10 0 #v[13, 14] 4 (some 7) 0 #v[15, 16] (some #v[17, 18]),
    Verification.IndirectPort.mk 10 1 #v[13, 14] 4 (some 8) 0 #v[19, 20] (some #v[21, 22]),
    Verification.IndirectPort.mk 10 2 #v[13, 14] 4 (some 9) 0 #v[23, 24] (some #v[25, 26]),
    Verification.IndirectPort.mk 10 3 #v[13, 14] 4 (some 10) 0 #v[27, 28] (some #v[29, 30]),
    Verification.IndirectPort.mk 11 0 #v[31, 32] 4 (some 11) 0 #v[33, 34] none,
    Verification.IndirectPort.mk 11 1 #v[31, 32] 4 (some 12) 0 #v[35, 36] none] := rfl

theorem timestamp_count {p : Nat} [Fact p.Prime] :
    (FlatOperation.lookups (importedConstraintsTimestampLookups (p := p))).length = 21 := rfl

theorem delegation_columns : importedConstraintsDelegationColumns =
    (⟨0, #v[1, 2], (Vector.ofFn (fun i : Fin 9 =>
      Trace.TimestampPort.mk 2 #v[83 + 3 * i.val, 84 + 3 * i.val]
        (85 + 3 * i.val))).toArray⟩ : Delegation.ClockColumns) := by decide

theorem memory_clocks : importedConstraintsMemoryPorts.map Trace.MemoryPort.clock =
    importedConstraintsDelegationColumns.ports := by
  simp [importedConstraintsMemoryPorts, importedConstraintsDelegationColumns]

theorem constraint_count {p : Nat} [Fact p.Prime] (setup : Table (ZMod p) (fields 9)) :
    (FlatOperation.constraints (importedConstraints setup)).length = 32 := rfl

theorem lookup_count {p : Nat} [Fact p.Prime] (setup : Table (ZMod p) (fields 9)) :
    (FlatOperation.lookups (importedConstraints setup)).length = 21 := rfl

theorem variable_roles :
    importedConstraintsVariableNames.lookup 0 = some "Execute flag for cycle" ∧
    importedConstraintsVariableNames.lookup 1 = some "delegation_invocation_ts[0]" ∧
    importedConstraintsVariableNames.lookup 2 = some "delegation_invocation_ts[1]" ∧
    importedConstraintsVariableNames.lookup 3 = some "control read/write from x12 read[0]" ∧
    importedConstraintsVariableNames.lookup 4 = some "control read/write from x12 read[1]" ∧
    importedConstraintsVariableNames.lookup 5 = some "control read/write from x12 write[0]" ∧
    importedConstraintsVariableNames.lookup 6 = some "control read/write from x12 write[0]" ∧
    importedConstraintsVariableNames.lookup 7 = some "x10 offset 0" ∧
    importedConstraintsVariableNames.lookup 8 = some "x10 offset 1" ∧
    importedConstraintsVariableNames.lookup 9 = some "x10 offset 2" ∧
    importedConstraintsVariableNames.lookup 10 = some "x10 offset 3" ∧
    importedConstraintsVariableNames.lookup 11 = some "x11 offset 0" ∧
    importedConstraintsVariableNames.lookup 12 = some "x11 offset 1" ∧
    importedConstraintsVariableNames.lookup 13 = some "state read/write from x10 read[0]" ∧
    importedConstraintsVariableNames.lookup 14 = some "state read/write from x10 read[1]" ∧
    importedConstraintsVariableNames.lookup 15 = some "state read/write from x10 indirect access 0 read[0]" ∧
    importedConstraintsVariableNames.lookup 16 = some "state read/write from x10 indirect access 0 read[1]" ∧
    importedConstraintsVariableNames.lookup 17 = some "state read/write from x10 indirect access 0 write[0]" ∧
    importedConstraintsVariableNames.lookup 18 = some "state read/write from x10 indirect access 0 write[1]" ∧
    importedConstraintsVariableNames.lookup 19 = some "state read/write from x10 indirect access 1 read[0]" ∧
    importedConstraintsVariableNames.lookup 20 = some "state read/write from x10 indirect access 1 read[1]" ∧
    importedConstraintsVariableNames.lookup 21 = some "state read/write from x10 indirect access 1 write[0]" ∧
    importedConstraintsVariableNames.lookup 22 = some "state read/write from x10 indirect access 1 write[1]" ∧
    importedConstraintsVariableNames.lookup 23 = some "state read/write from x10 indirect access 2 read[0]" ∧
    importedConstraintsVariableNames.lookup 24 = some "state read/write from x10 indirect access 2 read[1]" ∧
    importedConstraintsVariableNames.lookup 25 = some "state read/write from x10 indirect access 2 write[0]" ∧
    importedConstraintsVariableNames.lookup 26 = some "state read/write from x10 indirect access 2 write[1]" ∧
    importedConstraintsVariableNames.lookup 27 = some "state read/write from x10 indirect access 3 read[0]" ∧
    importedConstraintsVariableNames.lookup 28 = some "state read/write from x10 indirect access 3 read[1]" ∧
    importedConstraintsVariableNames.lookup 29 = some "state read/write from x10 indirect access 3 write[0]" ∧
    importedConstraintsVariableNames.lookup 30 = some "state read/write from x10 indirect access 3 write[1]" ∧
    importedConstraintsVariableNames.lookup 31 = some "input read from x11 read[0]" ∧
    importedConstraintsVariableNames.lookup 32 = some "input read from x11 read[1]" ∧
    importedConstraintsVariableNames.lookup 33 = some "input read from x11 indirect access 0 read[0]" ∧
    importedConstraintsVariableNames.lookup 34 = some "input read from x11 indirect access 0 read[1]" ∧
    importedConstraintsVariableNames.lookup 35 = some "input read from x11 indirect access 1 read[0]" ∧
    importedConstraintsVariableNames.lookup 36 = some "input read from x11 indirect access 1 read[1]" ∧
    importedConstraintsVariableNames.lookup 37 = some "Variable at cs/src/gkr_circuits/delegation/blake2_round_with_extended_control/legacy/g_function.rs::33" ∧
    importedConstraintsVariableNames.lookup 38 = some "Variable at cs/src/gkr_circuits/delegation/blake2_round_with_extended_control/legacy/g_function.rs::33" ∧
    importedConstraintsVariableNames.lookup 39 = some "Variable at cs/src/gkr_circuits/delegation/blake2_round_with_extended_control/legacy/g_function.rs::35" ∧
    importedConstraintsVariableNames.lookup 40 = some "Variable at cs/src/gkr_circuits/delegation/blake2_round_with_extended_control/legacy/g_function.rs::35" ∧
    importedConstraintsVariableNames.lookup 49 = some "Variable at cs/src/gkr_circuits/delegation/blake2_round_with_extended_control/legacy/g_function.rs::204" ∧
    importedConstraintsVariableNames.lookup 50 = some "Variable at cs/src/gkr_circuits/delegation/blake2_round_with_extended_control/legacy/g_function.rs::206" ∧
    importedConstraintsVariableNames.lookup 65 = some "Variable at cs/src/gkr_circuits/delegation/blake2_round_with_extended_control/legacy/g_function.rs::434" ∧
    importedConstraintsVariableNames.lookup 66 = some "Variable at cs/src/gkr_circuits/delegation/blake2_round_with_extended_control/legacy/g_function.rs::434" ∧
    importedConstraintsVariableNames.lookup 67 = some "Variable at cs/src/gkr_circuits/delegation/blake2_round_with_extended_control/legacy/g_function.rs::436" ∧
    importedConstraintsVariableNames.lookup 68 = some "Variable at cs/src/gkr_circuits/delegation/blake2_round_with_extended_control/legacy/g_function.rs::436" ∧
    importedConstraintsVariableNames.lookup 75 = some "Variable at cs/src/gkr_circuits/delegation/blake2_round_with_extended_control/legacy/g_function.rs::552" ∧
    importedConstraintsVariableNames.lookup 76 = some "Variable at cs/src/gkr_circuits/delegation/blake2_round_with_extended_control/legacy/g_function.rs::554" ∧
    importedConstraintsVariableNames.lookup 85 = some "indirect access query 0, register access intermediate timestamp borrow" ∧
    importedConstraintsVariableNames.lookup 88 = some "indirect access query 0, indirect access 0 intermediate timestamp borrow" ∧
    importedConstraintsVariableNames.lookup 91 = some "indirect access query 0, indirect access 1 intermediate timestamp borrow" ∧
    importedConstraintsVariableNames.lookup 94 = some "indirect access query 0, indirect access 2 intermediate timestamp borrow" ∧
    importedConstraintsVariableNames.lookup 97 = some "indirect access query 0, indirect access 3 intermediate timestamp borrow" ∧
    importedConstraintsVariableNames.lookup 100 = some "indirect access query 1, register access intermediate timestamp borrow" ∧
    importedConstraintsVariableNames.lookup 103 = some "indirect access query 1, indirect access 0 intermediate timestamp borrow" ∧
    importedConstraintsVariableNames.lookup 106 = some "indirect access query 1, indirect access 1 intermediate timestamp borrow" ∧
    importedConstraintsVariableNames.lookup 109 = some "indirect access query 2, register access intermediate timestamp borrow" := by
  repeat' apply And.intro
  all_goals decide

end Airbender.Blake2G
