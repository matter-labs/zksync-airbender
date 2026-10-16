import Airbender.Import.SetupTemplateEmbed

namespace Airbender.Keccak
set_option Elab.async false

import_setup_templates rotationTemplates from "artifacts/setup/keccak.json"
  native_table_id 40 physical_column 2
  row_offsets [393216, 458752, 524288, 589824, 655360,
    720896, 786432, 851968, 917504, 983040]

end Airbender.Keccak
