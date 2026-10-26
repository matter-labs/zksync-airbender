import Airbender.Import.GKRProtocol.DecoderArgumentsImport
import Airbender.Proofs.GKRProtocol.CleanArithmeticNative.UnifiedUncached
import Airbender.Proofs.GKRProtocol.FunctionalLinksNative.UnifiedUncached
import Airbender.Proofs.GKRProtocol.LookupSourceNative.UnifiedUncached
import Airbender.Review.Circuits.UnifiedReduced.Artifact

namespace Airbender.Compiler.DecoderArgumentsNative.UnifiedUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_decoder_arguments native from "artifacts/compiler/unified-uncached.json"
  certificate "artifacts/compiler/lookup/unified-uncached.json"
  clean_model Airbender.Compiler.CleanArithmeticNative.UnifiedUncached.native
  base_model Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native
  lookup_model Airbender.Compiler.LookupNative.UnifiedUncached.native
  query_model Airbender.Compiler.LookupSourceNative.UnifiedUncached.native
  links_model Airbender.Compiler.FunctionalLinksNative.UnifiedUncached.native
  source_query Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.query20
  trace_columns Airbender.UnifiedReduced.importedConstraintsTraceColumns
  decoder_columns Airbender.UnifiedReduced.importedConstraintsDecoderColumns

end Airbender.Compiler.DecoderArgumentsNative.UnifiedUncached
