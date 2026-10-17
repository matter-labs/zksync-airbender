import Airbender.Import.InitializationEmbed

namespace Airbender.Initialization
set_option warningAsError true
set_option Elab.async false

import_ram_initialization standalone from
  "../../cs/compiled_circuits/inits_and_teardowns_layout_no_caches_gkr.json"

import_ram_initialization unified from
  "../../cs/compiled_circuits/unified_reduced_machine_layout_no_caches_gkr.json" unified_inline

end Airbender.Initialization
