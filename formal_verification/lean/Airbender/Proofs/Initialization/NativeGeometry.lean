import Airbender.Proofs.Initialization.Native
import Airbender.Proofs.Initialization.Geometry

namespace Airbender.Initialization.Proofs
set_option warningAsError true
set_option Elab.async false

theorem standalone_geometry : Geometry standalone.layout := by
  constructor <;> decide +kernel

theorem unified_geometry : Geometry unified.layout := by
  constructor <;> decide +kernel

end Airbender.Initialization.Proofs
