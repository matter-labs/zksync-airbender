import Human.Import.InitsTeardowns

namespace Airbender.InitsTeardowns

-- The inits/teardowns sets inlined into the unified reduced machine (two sets of
-- 2^23 rows, output `InitsAndTeardownsProduct`). Its constraints are imported by
-- `Human.Circuits.UnifiedReduced.Artifact`.
set_option maxRecDepth 8192 in
import_inits_teardowns unifiedLayout from "../../cs/compiled_circuits/unified_reduced_machine_layout_no_caches_gkr.json"

end Airbender.InitsTeardowns
