import Airbender.Import.GKRProtocol.DecoderArgumentsImport
import Airbender.Proofs.GKRProtocol.CleanArithmeticNative.UnifiedCached
import Airbender.Proofs.GKRProtocol.FunctionalLinksNative.UnifiedCached
import Airbender.Proofs.GKRProtocol.LookupSourceNative.UnifiedCached
import Airbender.Review.Circuits.UnifiedReduced.Artifact

namespace Airbender.Compiler.DecoderArgumentsNative.UnifiedCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_decoder_arguments native from "artifacts/compiler/unified-cached.json"
  certificate "artifacts/compiler/lookup/unified-cached.json"
  clean_model Airbender.Compiler.CleanArithmeticNative.UnifiedCached.native
  base_model Airbender.Compiler.FullArithmeticNative.UnifiedCached.native
  lookup_model Airbender.Compiler.LookupNative.UnifiedCached.native
  query_model Airbender.Compiler.LookupSourceNative.UnifiedCached.native
  links_model Airbender.Compiler.FunctionalLinksNative.UnifiedCached.native
  source_query Airbender.Compiler.LookupSourceNative.UnifiedCached.native.query20
  trace_columns Airbender.UnifiedReduced.importedConstraintsTraceColumns
  decoder_columns Airbender.UnifiedReduced.importedConstraintsDecoderColumns

end Airbender.Compiler.DecoderArgumentsNative.UnifiedCached
