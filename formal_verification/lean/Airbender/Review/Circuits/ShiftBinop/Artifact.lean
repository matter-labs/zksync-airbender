import Airbender.Import.Embed

namespace Airbender.ShiftBinop

inductive Operation where
  | xor | or | and | sll | srl | sra | rev8
  deriving DecidableEq

def Operation.tag : Operation → Nat
  | .xor => 4 | .or => 6 | .and => 7
  | .sll => 1 | .srl => 2 | .sra => 3 | .rev8 => 5

def Operation.isShift : Operation → Bool
  | .sll | .srl | .sra | .rev8 => true
  | _ => false

-- All retained equations, both range queries and all five dynamic-tag lookups.
-- Native trace/decoder metadata is imported; logical matching and setup fidelity
-- remain external boundaries.
import_clean importedConstraints from "../../cs/compiled_circuits/shift_binop_layout_no_caches_gkr.json" shift_binop_lookups trace_metadata

def clockConstraints {p : Nat} [Fact p.Prime] : List (FlatOperation (ZMod p)) :=
  importedConstraints ++ importedConstraintsTimestampLookups

end Airbender.ShiftBinop
