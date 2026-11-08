module
public import Human.Import.TranscribeCommand
public import Human.Import.Exec.InitsTeardowns
public import Human.Import.InitsTeardownsLayout

@[expose] public section

namespace Airbender.InitsTeardowns

-- The standalone inits/teardowns circuit: eight sets of 2^24 rows, two word bits,
-- no constraints or lookups (the importer refuses anything else).
-- The artifact, transcribed (trusted: `Human/Import/TranscribeCommand.lean`).
import_circuit importedLayoutCircuit from "../../cs/compiled_circuits/inits_and_teardowns_layout_no_caches_gkr.json"
-- Its inits/teardowns layout as a literal term, fixed by `StandaloneImportClaim`.
import_inits_teardowns importedLayout from importedLayoutCircuit standalone

/-- The imported layout is the meaning (`Human/Import/InitsTeardownsLayout.lean`) of the artifact. -/
def StandaloneImportClaim : Prop := importedLayoutCircuit.initsTeardownsLayout true = .ok importedLayout

end Airbender.InitsTeardowns
