import Airbender.Proofs.Tables.AlignedSampleChecks.Data
import Airbender.Data.Tables.Shift.Column0
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport

namespace Airbender.Verification.AlignedSampleChecks
open Airbender Airbender.Compiler PackedSetupEquality PackedSetupSamples
set_option warningAsError true
set_option Elab.async false

numeric_data_binding conditionalBinding : (conditionalData.columns[1]).blocks.toList = conditionalBlocks.map BlockCode.decode

numeric_data_binding positionBinding : byteShiftColumn0.blocks.toList = positionBlocks.map BlockCode.decode

end Airbender.Verification.AlignedSampleChecks
