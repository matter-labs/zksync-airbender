import Airbender.Import.Embed

namespace Airbender.Blake2G

-- The supplied tagged setup is an explicit interface, not a witness-generation hint.
import_clean importedConstraints from "../../cs/compiled_circuits/blake2_g_function_layout_no_caches_gkr.json" blake_g_lookups

theorem constraint_count {p : Nat} [Fact p.Prime] (setup : Table (ZMod p) (fields 9)) :
    (FlatOperation.constraints (importedConstraints setup)).length = 32 := rfl

theorem lookup_count {p : Nat} [Fact p.Prime] (setup : Table (ZMod p) (fields 9)) :
    (FlatOperation.lookups (importedConstraints setup)).length = 21 := rfl

namespace Variables
abbrev execute := 0
abbrev controlReadHi := 4
abbrev controlWriteHi := 6
abbrev statePointerLo := 13
abbrev messagePointerLo := 31
abbrev booleanColumns := #v[0, 37, 38, 39, 40, 49, 50, 65, 66, 67, 68, 75, 76,
  85, 88, 91, 94, 97, 100, 103, 106, 109]
end Variables

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
    importedConstraintsVariableNames.lookup 37 = some "Variable at cs/src/gkr_circuits/delegation/blake2_round_with_extended_control/g_function.rs::33" ∧
    importedConstraintsVariableNames.lookup 38 = some "Variable at cs/src/gkr_circuits/delegation/blake2_round_with_extended_control/g_function.rs::33" ∧
    importedConstraintsVariableNames.lookup 39 = some "Variable at cs/src/gkr_circuits/delegation/blake2_round_with_extended_control/g_function.rs::35" ∧
    importedConstraintsVariableNames.lookup 40 = some "Variable at cs/src/gkr_circuits/delegation/blake2_round_with_extended_control/g_function.rs::35" ∧
    importedConstraintsVariableNames.lookup 49 = some "Variable at cs/src/gkr_circuits/delegation/blake2_round_with_extended_control/g_function.rs::204" ∧
    importedConstraintsVariableNames.lookup 50 = some "Variable at cs/src/gkr_circuits/delegation/blake2_round_with_extended_control/g_function.rs::206" ∧
    importedConstraintsVariableNames.lookup 65 = some "Variable at cs/src/gkr_circuits/delegation/blake2_round_with_extended_control/g_function.rs::434" ∧
    importedConstraintsVariableNames.lookup 66 = some "Variable at cs/src/gkr_circuits/delegation/blake2_round_with_extended_control/g_function.rs::434" ∧
    importedConstraintsVariableNames.lookup 67 = some "Variable at cs/src/gkr_circuits/delegation/blake2_round_with_extended_control/g_function.rs::436" ∧
    importedConstraintsVariableNames.lookup 68 = some "Variable at cs/src/gkr_circuits/delegation/blake2_round_with_extended_control/g_function.rs::436" ∧
    importedConstraintsVariableNames.lookup 75 = some "Variable at cs/src/gkr_circuits/delegation/blake2_round_with_extended_control/g_function.rs::552" ∧
    importedConstraintsVariableNames.lookup 76 = some "Variable at cs/src/gkr_circuits/delegation/blake2_round_with_extended_control/g_function.rs::554" ∧
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
