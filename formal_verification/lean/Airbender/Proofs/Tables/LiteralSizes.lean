import Airbender.Import.SetupEmbed

namespace Airbender.Setup.Proofs
set_option warningAsError true

/-- Read literal-array geometry without reducing its stored elements. -/
theorem raw_literal_size {α : Type} (values : List α) :
    (Array.mk values).size = values.length := rfl

end Airbender.Setup.Proofs
