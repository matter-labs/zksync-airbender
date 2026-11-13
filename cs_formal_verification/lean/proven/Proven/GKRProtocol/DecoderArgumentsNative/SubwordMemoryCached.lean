module
import all Mathlib.Data.List.Sort
public import Proven.Import.GKRProtocol.DecoderArgumentsImport
public import Proven.GKRProtocol.CleanArithmeticNative.SubwordMemoryCached
public import Proven.GKRProtocol.FunctionalLinksNative.SubwordMemoryCached
public import Proven.GKRProtocol.LookupSourceNative.SubwordMemoryCached
public import Human.Circuits.SubwordMemory.Artifact

@[expose] public section
set_option warningAsError true

namespace Airbender.Compiler.DecoderArgumentsNative.SubwordMemoryCached
open Airbender Airbender.Compiler
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_decoder_arguments native from "artifacts/compiler/subword-memory-cached.json"
  certificate "artifacts/compiler/lookup/subword-memory-cached.json"
  clean_model Airbender.Compiler.CleanArithmeticNative.SubwordMemoryCached.native
  base_model Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native
  lookup_model Airbender.Compiler.LookupNative.SubwordMemoryCached.native
  query_model Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native
  links_model Airbender.Compiler.FunctionalLinksNative.SubwordMemoryCached.native
  source_query Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.query12
  trace_columns Airbender.SubwordMemory.importedConstraintsTraceColumns
  decoder_columns Airbender.SubwordMemory.importedConstraintsDecoderColumns

end Airbender.Compiler.DecoderArgumentsNative.SubwordMemoryCached
