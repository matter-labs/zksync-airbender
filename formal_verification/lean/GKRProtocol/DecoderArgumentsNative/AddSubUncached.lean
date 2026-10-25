import GKRProtocol.DecoderArgumentsImport
import GKRProtocol.CleanArithmeticNative.AddSubUncached
import GKRProtocol.FunctionalLinksNative.AddSubUncached
import GKRProtocol.LookupSourceNative.AddSubUncached
import Airbender.Review.Circuits.AddSub.Artifact

namespace Airbender.Compiler.DecoderArgumentsNative.AddSubUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_decoder_arguments native from "artifacts/compiler/add-sub-uncached.json"
  certificate "artifacts/compiler/lookup/add-sub-uncached.json"
  clean_model Airbender.Compiler.CleanArithmeticNative.AddSubUncached.native
  base_model Airbender.Compiler.FullArithmeticNative.AddSubUncached.native
  lookup_model Airbender.Compiler.LookupNative.AddSubUncached.native
  query_model Airbender.Compiler.LookupSourceNative.AddSubUncached.native
  links_model Airbender.Compiler.FunctionalLinksNative.AddSubUncached.native
  source_query Airbender.Compiler.LookupSourceNative.AddSubUncached.native.query14
  trace_columns Airbender.AddSub.importedConstraintsTraceColumns
  decoder_columns Airbender.AddSub.importedConstraintsDecoderColumns

end Airbender.Compiler.DecoderArgumentsNative.AddSubUncached
