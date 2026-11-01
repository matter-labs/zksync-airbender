import Airbender.Proofs.GKRProtocol.SubwordRegionLengths.Column4.Data
import Airbender.Review.Helpers.Tables.Subword
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport

namespace Airbender.Compiler.SubwordRegionLengths.Column4
open Airbender Airbender.Compiler
open PackedSetupEquality PackedSetupLengths
set_option warningAsError true
set_option Elab.async false

numeric_data_binding binding0 : (Airbender.Verification.subwordZeroData.columns[(4 : Nat)]).blocks.toList = region0.map BlockCode.decode

numeric_data_binding binding1 : (Airbender.Verification.storePlaceData.columns[(4 : Nat)]).blocks.toList = region1.map BlockCode.decode

numeric_data_binding binding2 : (Airbender.Verification.storeClearData.columns[(4 : Nat)]).blocks.toList = region2.map BlockCode.decode

numeric_data_binding binding3 : (Airbender.Verification.loadHalfData.columns[(4 : Nat)]).blocks.toList = region3.map BlockCode.decode

numeric_data_binding binding4 : (Airbender.Verification.loadByteData.columns[(4 : Nat)]).blocks.toList = region4.map BlockCode.decode

end Airbender.Compiler.SubwordRegionLengths.Column4
