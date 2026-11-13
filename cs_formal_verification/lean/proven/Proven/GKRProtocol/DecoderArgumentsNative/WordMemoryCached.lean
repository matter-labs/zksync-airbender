module
import all Mathlib.Data.List.Sort
public import Proven.Import.GKRProtocol.DecoderArgumentsImport
public import Proven.GKRProtocol.CleanArithmeticNative.WordMemoryCached
public import Proven.GKRProtocol.FunctionalLinksNative.WordMemoryCached
public import Proven.GKRProtocol.LookupSourceNative.WordMemoryCached
public import Human.Circuits.WordMemory.Artifact

@[expose] public section
set_option warningAsError true

namespace Airbender.Compiler.DecoderArgumentsNative.WordMemoryCached
open Airbender Airbender.Compiler
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
