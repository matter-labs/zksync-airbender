import Airbender.Import.GKRProtocol.DecoderArgumentsImport
import Airbender.Proofs.GKRProtocol.CleanArithmeticNative.MulDivCached
import Airbender.Proofs.GKRProtocol.FunctionalLinksNative.MulDivCached
import Airbender.Proofs.GKRProtocol.LookupSourceNative.MulDivCached
import Airbender.Review.Circuits.MulDiv.Artifact

namespace Airbender.Compiler.DecoderArgumentsNative.MulDivCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_decoder_arguments native from "artifacts/compiler/mul-div-cached.json"
  certificate "artifacts/compiler/lookup/mul-div-cached.json"
  clean_model Airbender.Compiler.CleanArithmeticNative.MulDivCached.native
  base_model Airbender.Compiler.FullArithmeticNative.MulDivCached.native
  lookup_model Airbender.Compiler.LookupNative.MulDivCached.native
  query_model Airbender.Compiler.LookupSourceNative.MulDivCached.native
  links_model Airbender.Compiler.FunctionalLinksNative.MulDivCached.native
  source_query Airbender.Compiler.LookupSourceNative.MulDivCached.native.query16
  trace_columns Airbender.MulDiv.importedConstraintsTraceColumns
  decoder_columns Airbender.MulDiv.importedConstraintsDecoderColumns

end Airbender.Compiler.DecoderArgumentsNative.MulDivCached
