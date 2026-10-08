import Airbender.Import.Embed

namespace Airbender.Keccak

set_option maxRecDepth 16384

-- All fixed queries use the supplied tagged setup. Its rows remain an explicit
-- interface; this import does not reconstruct or assume the Keccak operations.
import_clean importedConstraints from "../../cs/compiled_circuits/keccak_special5_layout_no_caches_gkr.json" keccak_lookups

theorem constraint_count {p : Nat} [Fact p.Prime] (setup : Table (ZMod p) (fields 8)) :
    (FlatOperation.constraints (importedConstraints setup)).length = 187 := rfl

theorem lookup_count {p : Nat} [Fact p.Prime] (setup : Table (ZMod p) (fields 8)) :
    (FlatOperation.lookups (importedConstraints setup)).length = 42 := rfl

/-- Twelve 32-bit writes encode six 64-bit lane accesses through x11.
    Lane indices are scaled by eight bytes; the second word adds four bytes. -/
theorem port_layout : importedConstraintsIndirectPorts =
    Vector.ofFn (fun i : Fin 12 => Verification.IndirectPort.mk 11 i.val #v[13, 14]
      8 (some (7 + i.val / 2)) (4 * (i.val % 2))
      #v[15 + 4 * i.val, 16 + 4 * i.val]
      (some #v[17 + 4 * i.val, 18 + 4 * i.val])) := by decide

namespace Variables
abbrev execute := 0
abbrev controlReadLo := 3
abbrev controlReadHi := 4
abbrev controlWriteLo := 5
abbrev controlWriteHi := 6
abbrev statePointerLo := 13
abbrev statePointerHi := 14
abbrev modeColumns := #v[63, 64, 65, 66, 67, 68, 69]
abbrev iterationColumns := #v[70, 71, 72, 73, 74]
abbrev roundColumns := #v[75, 76, 77, 78, 79]
end Variables

theorem variable_roles :
    importedConstraintsVariableNames.lookup 0 = some "Execute flag for cycle" ∧
    importedConstraintsVariableNames.lookup 3 = some "x10 control register read/write read[0]" ∧
    importedConstraintsVariableNames.lookup 4 = some "x10 control register read/write read[1]" ∧
    importedConstraintsVariableNames.lookup 5 = some "x10 control register read/write write[0]" ∧
    importedConstraintsVariableNames.lookup 6 = some "x10 control register read/write write[0]" ∧
    importedConstraintsVariableNames.lookup 13 = some "x11 indirect access read[0]" ∧
    importedConstraintsVariableNames.lookup 14 = some "x11 indirect access read[1]" := by decide

end Airbender.Keccak
