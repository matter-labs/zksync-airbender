import Airbender.Review.Circuits.Keccak.Tables.RotationData

namespace Airbender.Keccak
set_option Elab.async false
set_option maxRecDepth 131072
set_option maxHeartbeats 2000000

/- Every physical fixed-table column comes from its native exported region. -/
import_setup_region zeroData from "artifacts/setup/keccak.json" native_table_id 0
import_setup_region xorData from "artifacts/setup/keccak.json" native_table_id 4
import_setup_region iotaData from "artifacts/setup/keccak.json" native_table_id 38
import_setup_region chiData from "artifacts/setup/keccak.json" native_table_id 39
import_setup_region rotationRawData from "artifacts/setup/keccak.json" native_table_id 40
share_setup_literals rotationData from rotationRawData using
  [rotationTemplates0, rotationTemplates1, rotationTemplates2, rotationTemplates3,
   rotationTemplates4, rotationTemplates5, rotationTemplates6, rotationTemplates7,
   rotationTemplates8, rotationTemplates9]

def fixedData (kind : Fin 5) : Setup.TableData 8 :=
  #v[zeroData, xorData, iotaData, chiData, rotationData][kind]

def fixedRegion (kind : Fin 5) : Setup.Region :=
  #v[zeroDataRegion, xorDataRegion, iotaDataRegion, chiDataRegion, rotationDataRegion][kind]

def fixedRow (kind : Fin 5) (index : Nat) : Vector Nat 8 :=
  (fixedData kind).columns.map fun column => (column.get? index).getD 0

end Airbender.Keccak
