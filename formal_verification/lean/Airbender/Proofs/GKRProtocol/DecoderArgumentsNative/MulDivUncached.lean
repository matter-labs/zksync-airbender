import Airbender.Import.GKRProtocol.DecoderArgumentsImport
import Airbender.Proofs.GKRProtocol.CleanArithmeticNative.MulDivUncached
import Airbender.Proofs.GKRProtocol.FunctionalLinksNative.MulDivUncached
import Airbender.Proofs.GKRProtocol.LookupSourceNative.MulDivUncached
import Airbender.Review.Circuits.MulDiv.Artifact

namespace Airbender.Compiler.DecoderArgumentsNative.MulDivUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_decoder_arguments native from "artifacts/compiler/mul-div-uncached.json"
  certificate "artifacts/compiler/lookup/mul-div-uncached.json"
  clean_model Airbender.Compiler.CleanArithmeticNative.MulDivUncached.native
  base_model Airbender.Compiler.FullArithmeticNative.MulDivUncached.native
  lookup_model Airbender.Compiler.LookupNative.MulDivUncached.native
  query_model Airbender.Compiler.LookupSourceNative.MulDivUncached.native
  links_model Airbender.Compiler.FunctionalLinksNative.MulDivUncached.native
  source_query Airbender.Compiler.LookupSourceNative.MulDivUncached.native.query16
  trace_columns Airbender.MulDiv.importedConstraintsTraceColumns
  decoder_columns Airbender.MulDiv.importedConstraintsDecoderColumns

end Airbender.Compiler.DecoderArgumentsNative.MulDivUncached
