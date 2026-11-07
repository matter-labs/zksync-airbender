import Airbender.Import.SetupEmbed

set_option maxRecDepth 131072
set_option maxHeartbeats 2000000

namespace Airbender.Blake2Round

/- Actual native fixed regions. Every key, output, padding and tag column is
   sliced by exported ID and checked against the complete parsed artifact. -/
import_setup_region xor8Data from "artifacts/setup/blake-round.json" native_table_id 4
import_setup_region xor7Data from "artifacts/setup/blake-round.json" native_table_id 19
import_setup_region xor9Data from "artifacts/setup/blake-round.json" native_table_id 20
import_setup_region xor8CarryData from "artifacts/setup/blake-round.json" native_table_id 55
import_setup_region xor7CarryData from "artifacts/setup/blake-round.json" native_table_id 56
import_setup_region xor4x3Data from "artifacts/setup/blake-round.json" native_table_id 57

def xorData (kind : Fin 6) : Setup.TableData 6 :=
  #v[xor8Data, xor7Data, xor9Data, xor8CarryData, xor7CarryData, xor4x3Data][kind]

def xorRegion (kind : Fin 6) : Setup.Region :=
  #v[xor8DataRegion, xor7DataRegion, xor9DataRegion, xor8CarryDataRegion,
    xor7CarryDataRegion, xor4x3DataRegion][kind]

def xorRegionRow (kind : Fin 6) (index : Nat) : Vector Nat 6 :=
  (xorData kind).columns.map fun column => (column.get? index).getD 0

end Airbender.Blake2Round
