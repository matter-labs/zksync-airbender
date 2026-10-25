import GKRProtocol.DecoderArgumentsImport
import GKRProtocol.CleanArithmeticNative.WordMemoryUncached
import GKRProtocol.FunctionalLinksNative.WordMemoryUncached
import GKRProtocol.LookupSourceNative.WordMemoryUncached
import Airbender.Review.Circuits.WordMemory.Artifact

namespace Airbender.Compiler.DecoderArgumentsNative.WordMemoryUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_decoder_arguments native from "artifacts/compiler/word-memory-uncached.json"
  certificate "artifacts/compiler/lookup/word-memory-uncached.json"
  clean_model Airbender.Compiler.CleanArithmeticNative.WordMemoryUncached.native
  base_model Airbender.Compiler.FullArithmeticNative.WordMemoryUncached.native
  lookup_model Airbender.Compiler.LookupNative.WordMemoryUncached.native
  query_model Airbender.Compiler.LookupSourceNative.WordMemoryUncached.native
  links_model Airbender.Compiler.FunctionalLinksNative.WordMemoryUncached.native
  source_query Airbender.Compiler.LookupSourceNative.WordMemoryUncached.native.query10
  trace_columns Airbender.WordMemory.importedConstraintsTraceColumns
  decoder_columns Airbender.WordMemory.importedConstraintsDecoderColumns

end Airbender.Compiler.DecoderArgumentsNative.WordMemoryUncached
