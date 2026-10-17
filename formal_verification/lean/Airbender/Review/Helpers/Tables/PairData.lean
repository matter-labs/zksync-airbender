import Airbender.Review.Helpers.Tables.Range
import Airbender.Import.SetupRegionEmbed

namespace Airbender.Verification
open Setup
set_option Elab.async false
set_option maxRecDepth 32768

/- The native region retains every physical column and its exported ID/offset.
   Existing pair-shaped Clean interfaces project its first two columns. -/
import_setup_slice regZeroData from "artifacts/setup/jump-branch.json" native_table_id 1
import_setup_slice signData from "artifacts/setup/jump-branch.json" native_table_id 5
import_setup_slice jumpCleanupData from "artifacts/setup/jump-branch.json" native_table_id 2
import_setup_slice conditionalData from "artifacts/setup/jump-branch.json" native_table_id 31
import_setup_slice lowByteData from "artifacts/setup/mul-div.json" native_table_id 41

def setupPairRow (data : TableData width) (wide : 2 ≤ width)
    (index : Fin data.length) : Nat × Nat :=
  (((data.columns[0]'(by omega)).get? (data.offset + index.val)).getD 0,
   ((data.columns[1]'(by omega)).get? (data.offset + index.val)).getD 0)

def setupPairTable {p : Nat} [Fact p.Prime] (name : String)
    (data : TableData width) (wide : 2 ≤ width) : Table (ZMod p) fieldPair := .fromStatic {
  name := name
  length := data.length
  row i := (((setupPairRow data wide i).1 : ZMod p),
    ((setupPairRow data wide i).2 : ZMod p))
  index entry := entry.1.val
  Spec entry := ∃ i : Fin data.length,
    entry = (((setupPairRow data wide i).1 : ZMod p),
      ((setupPairRow data wide i).2 : ZMod p))
  contains_iff _ := Iff.rfl
}


def setupTripleRow (data : TableData width) (wide : 3 ≤ width)
    (index : Fin data.length) : Nat × Nat × Nat :=
  (((data.columns[0]'(by omega)).get? (data.offset + index.val)).getD 0,
   ((data.columns[1]'(by omega)).get? (data.offset + index.val)).getD 0,
   ((data.columns[2]'(by omega)).get? (data.offset + index.val)).getD 0)

def setupTripleTable {p : Nat} [Fact p.Prime] (name : String)
    (data : TableData width) (wide : 3 ≤ width) : Table (ZMod p) fieldTriple := .fromStatic {
  name := name
  length := data.length
  row i := (((setupTripleRow data wide i).1 : ZMod p),
    ((setupTripleRow data wide i).2.1 : ZMod p),
    ((setupTripleRow data wide i).2.2 : ZMod p))
  index entry := entry.1.val
  Spec entry := ∃ i : Fin data.length,
    entry = (((setupTripleRow data wide i).1 : ZMod p),
      ((setupTripleRow data wide i).2.1 : ZMod p),
      ((setupTripleRow data wide i).2.2 : ZMod p))
  contains_iff _ := Iff.rfl
}

end Airbender.Verification
