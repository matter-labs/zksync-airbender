import Airbender.Import.Embed

namespace Airbender.ShiftBinop

-- Complete native local row projection: 50 equations, scalar/timestamp queries,
-- all four witness-selected tagged lookups, and state/memory/decoder/setup metadata.
-- The tagged table retains the exact compilation CSR profile (nondeterminism, empty delegation list).
-- Runtime CSR setup binding, instruction semantics and argument enforcement remain separate.
import_clean importedConstraints from "../../cs/shift_binop_csrrw_preprocessed_layout.json" shift_binop_lookups trace_metadata

end Airbender.ShiftBinop
