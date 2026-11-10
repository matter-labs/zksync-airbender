import Airbender.Import.SetupEmbed
import Airbender.Review.Helpers.Tables.Lookups
import Airbender.Review.Circuits.JumpBranchSlt.Tables.Control

namespace Airbender.Bigint

/- Actual native fixed-table rows, selected by the exported region extent.
    JSON parsing/emission and cryptographic query binding remain external. -/
import_setup_generic importedSetup from "artifacts/setup/bigint.json"

def setupRow (index : Fin 1390592) : Nat × Nat × Nat :=
  let value (column : Fin 3) := (importedSetup.columns[column].get? index.val).getD 0
  (value 0, value 1, value 2)

private def setupOffset (tag : Nat) : Nat :=
  ((importedSetupRegions.find? (fun region => region.id == tag)).map (·.offset)).getD 0

def setupTable {p : Nat} [Fact p.Prime] : Table (ZMod p) (fields 3) := .fromStatic {
  name := "Airbender.Bigint"
  length := 1390592
  row i := #v[((setupRow i).1 : ZMod p), ((setupRow i).2.1 : ZMod p), ((setupRow i).2.2 : ZMod p)]
  index x := match x[2].val with
    | 22 => setupOffset 22 + x[0].val * 512 + x[1].val
    | 23 => setupOffset 23 + x[0].val * 1024 + x[1].val
    | 24 => setupOffset 24 + x[0].val
    | 25 => setupOffset 25 + x[0].val
    | 26 => setupOffset 26 + x[0].val
    | 41 => setupOffset 41 + x[0].val
    | _ => 0
  Spec x := ∃ i : Fin 1390592, x = #v[((setupRow i).1 : ZMod p), ((setupRow i).2.1 : ZMod p), ((setupRow i).2.2 : ZMod p)]
  contains_iff _ := Iff.rfl
}

end Airbender.Bigint
