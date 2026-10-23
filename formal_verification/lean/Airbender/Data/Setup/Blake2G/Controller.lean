import Airbender.Import.SetupEmbed

namespace Airbender.Blake2G

/- Native controller data, including its key and discriminator columns. The
   importer selects the exported region by ID and checks every sliced value. -/
import_setup_region controllerData from "artifacts/setup/blake-g.json" native_table_id 28

end Airbender.Blake2G
