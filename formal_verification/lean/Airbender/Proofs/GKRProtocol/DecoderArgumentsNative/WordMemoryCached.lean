import Airbender.Import.GKRProtocol.DecoderArgumentsImport
import Airbender.Proofs.GKRProtocol.CleanArithmeticNative.WordMemoryCached
import Airbender.Proofs.GKRProtocol.FunctionalLinksNative.WordMemoryCached
import Airbender.Proofs.GKRProtocol.LookupSourceNative.WordMemoryCached
import Airbender.Review.Circuits.WordMemory.Artifact

namespace Airbender.Compiler.DecoderArgumentsNative.WordMemoryCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_decoder_arguments native from "artifacts/compiler/word-memory-cached.json"
  certificate "artifacts/compiler/lookup/word-memory-cached.json"
  clean_model Airbender.Compiler.CleanArithmeticNative.WordMemoryCached.native
  base_model Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native
  lookup_model Airbender.Compiler.LookupNative.WordMemoryCached.native
  query_model Airbender.Compiler.LookupSourceNative.WordMemoryCached.native
  links_model Airbender.Compiler.FunctionalLinksNative.WordMemoryCached.native
  source_query Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.query10
  trace_columns Airbender.WordMemory.importedConstraintsTraceColumns
  decoder_columns Airbender.WordMemory.importedConstraintsDecoderColumns

end Airbender.Compiler.DecoderArgumentsNative.WordMemoryCached
