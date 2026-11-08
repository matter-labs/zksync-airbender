module
public import Human.Import.TranscribeCommand
public import Human.Import.Exec.InitsTeardowns
public import Human.Import.InitsTeardownsLayout

@[expose] public section

namespace Airbender.InitsTeardowns

-- The inits/teardowns sets inlined into the unified reduced machine (two sets of
-- 2^23 rows, output `InitsAndTeardownsProduct`). Its constraints are imported by
-- `Human.Circuits.UnifiedReduced.Artifact`.
-- The artifact, transcribed (trusted: `Human/Import/TranscribeCommand.lean`).
import_circuit unifiedLayoutCircuit from "../../cs/compiled_circuits/unified_reduced_machine_layout_no_caches_gkr.json"
-- Its inits/teardowns layout as a literal term, fixed by `UnifiedImportClaim`.
set_option maxRecDepth 8192 in
import_inits_teardowns unifiedLayout from unifiedLayoutCircuit

/-- The imported layout is the meaning (`Human/Import/InitsTeardownsLayout.lean`) of the artifact. -/
def UnifiedImportClaim : Prop := unifiedLayoutCircuit.initsTeardownsLayout false = .ok unifiedLayout

end Airbender.InitsTeardowns
