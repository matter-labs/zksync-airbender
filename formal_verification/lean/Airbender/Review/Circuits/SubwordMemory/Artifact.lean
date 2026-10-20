import Airbender.Import.Embed

namespace Airbender.SubwordMemory
set_option autoImplicit false

-- All 51 native equations, two scalar and eight timestamp queries, two constant
-- and two witness-selected queries, and state/port/decoder/setup metadata.
-- Subword limb selection, operation routing, public decoding, initialized history
-- and original Sail execution are subsequent claims, not import assumptions.
import_clean importedConstraints from "../../cs/subword_only_load_store_preprocessed_layout.json" subword_memory_lookups trace_metadata

end Airbender.SubwordMemory
