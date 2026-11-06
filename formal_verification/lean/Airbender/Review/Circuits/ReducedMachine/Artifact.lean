import Airbender.Import.Embed

namespace Airbender.ReducedMachine

-- Combined native v2 CPU: all row equations, scalar/timestamp queries and all
-- four tagged query fields. This parameter is the fixed setup table, not witness
-- data; no native setup correspondence or argument enforcement follows here.
import_clean importedConstraints from "../../cs/reduced_machine_preprocessed_layout.json" reduced_machine_lookups trace_metadata

end Airbender.ReducedMachine
