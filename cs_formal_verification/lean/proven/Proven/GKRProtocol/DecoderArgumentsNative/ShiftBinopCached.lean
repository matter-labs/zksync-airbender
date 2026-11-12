module
import all Mathlib.Data.List.Sort
public import Proven.Import.GKRProtocol.DecoderArgumentsImport
public import Proven.GKRProtocol.CleanArithmeticNative.ShiftBinopCached
public import Proven.GKRProtocol.FunctionalLinksNative.ShiftBinopCached
public import Proven.GKRProtocol.LookupSourceNative.ShiftBinopCached
public import Human.Circuits.ShiftBinop.Artifact

@[expose] public section
set_option warningAsError true

namespace Airbender.Compiler.DecoderArgumentsNative.ShiftBinopCached
open Airbender Airbender.Compiler
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_decoder_arguments native from "artifacts/compiler/shift-binop-cached.json"
  certificate "artifacts/compiler/lookup/shift-binop-cached.json"
  clean_model Airbender.Compiler.CleanArithmeticNative.ShiftBinopCached.native
  base_model Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native
  lookup_model Airbender.Compiler.LookupNative.ShiftBinopCached.native
  query_model Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native
  links_model Airbender.Compiler.FunctionalLinksNative.ShiftBinopCached.native
  source_query Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.query10
  trace_columns Airbender.ShiftBinop.importedConstraintsTraceColumns
  decoder_columns Airbender.ShiftBinop.importedConstraintsDecoderColumns

end Airbender.Compiler.DecoderArgumentsNative.ShiftBinopCached
