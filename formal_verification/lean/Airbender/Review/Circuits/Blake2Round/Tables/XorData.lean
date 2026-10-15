import Airbender.Import.SetupEmbed

set_option maxRecDepth 131072
set_option maxHeartbeats 2000000

namespace Airbender.Blake2Round

/- Actual native fixed regions. Every key, output, padding and tag column is
   sliced by exported ID and checked against the complete parsed artifact. -/
import_setup_region xor8Data from "artifacts/setup/blake-round.json" native_table_id 4
import_setup_region xor3Data from "artifacts/setup/blake-round.json" native_table_id 17
import_setup_region xor4Data from "artifacts/setup/blake-round.json" native_table_id 18
import_setup_region xor7Data from "artifacts/setup/blake-round.json" native_table_id 19
import_setup_region xor9Data from "artifacts/setup/blake-round.json" native_table_id 20

def xorData (kind : Fin 5) : Setup.TableData 4 :=
  #v[xor8Data, xor3Data, xor4Data, xor7Data, xor9Data][kind]

def xorRegion (kind : Fin 5) : Setup.Region :=
  #v[xor8DataRegion, xor3DataRegion, xor4DataRegion, xor7DataRegion, xor9DataRegion][kind]

def xorRegionRow (kind : Fin 5) (index : Nat) : Vector Nat 4 :=
  (xorData kind).columns.map fun column => (column.get? index).getD 0

end Airbender.Blake2Round
