import Human.Import.InitsTeardowns

namespace Airbender.InitsTeardowns

-- The standalone inits/teardowns circuit: eight sets of 2^24 rows, two word bits,
-- no constraints or lookups (the importer refuses anything else).
import_inits_teardowns importedLayout from "../../cs/compiled_circuits/inits_and_teardowns_layout_no_caches_gkr.json" standalone

end Airbender.InitsTeardowns
