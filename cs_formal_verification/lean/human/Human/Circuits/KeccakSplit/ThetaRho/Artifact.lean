module
public import Human.Import.Embed

@[expose] public section

namespace Airbender.Keccak.Split.ThetaRho

set_option maxRecDepth 16384

/- The no-cache theta+rho worker (CSR 0x7CC): its equations (including the grouped
   timestamp equations), the alignment query and all 50 fixed-table queries over the
   supplied setup, plus its grouped clock and memory-port metadata. -/
import_clean importedConstraints from "../../cs/compiled_circuits/keccak_theta_rho_layout_no_caches_gkr.json" keccak_theta_rho_lookups split_delegation_timestamps

/-- The operation core plus the invocation timestamp query. -/
def clockConstraints {p : Nat} [Fact p.Prime] (setup : Table (ZMod p) (fields 9)) :
    List (FlatOperation (ZMod p)) :=
  importedConstraints setup ++ importedConstraintsTimestampLookups

end Airbender.Keccak.Split.ThetaRho
