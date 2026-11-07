import Airbender.Proofs.GKRProtocol.QueryFrameChecks.BigintCached.Data
import Airbender.Import.GKRProtocol.NumericQueryFrameIndexImport
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport

namespace Airbender.Compiler.QueryFrameChecks.BigintCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

set_option exponentiation.threshold 4096 in
numeric_query_frame_index views := NumericQueryFrameChecks.index data
numeric_data_binding coordinates_index_binding : views.coordinates = NumericQueryFrameChecks.coordinateMask data.coordinates
numeric_data_binding placement_index_binding : views.placement.toList = data.placement
numeric_data_binding nativeAddress_index_binding : views.nativeAddress.toList = data.nativeAddress
numeric_data_binding returnedAddress_index_binding : views.returnedAddress.toList = data.returnedAddress

end Airbender.Compiler.QueryFrameChecks.BigintCached
