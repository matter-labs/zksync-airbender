import Airbender.Import.GKRProtocol.DecoderArgumentsImport
import Airbender.Proofs.GKRProtocol.CleanArithmeticNative.ShiftBinopCached
import Airbender.Proofs.GKRProtocol.FunctionalLinksNative.ShiftBinopCached
import Airbender.Proofs.GKRProtocol.LookupSourceNative.ShiftBinopCached
import Airbender.Review.Circuits.ShiftBinop.Artifact

namespace Airbender.Compiler.DecoderArgumentsNative.ShiftBinopCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
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
