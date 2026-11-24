module
import all Mathlib.Data.List.Sort
public import Proven.Import.GKRProtocol.DecoderArgumentsImport
public import Proven.GKRProtocol.CleanArithmeticNative.UnifiedCached
public import Proven.GKRProtocol.FunctionalLinksNative.UnifiedCached
public import Proven.GKRProtocol.LookupSourceNative.UnifiedCached
public import Human.Circuits.UnifiedReduced.Artifact

@[expose] public section
set_option warningAsError true

namespace Airbender.Compiler.DecoderArgumentsNative.UnifiedCached
open Airbender Airbender.Compiler
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
