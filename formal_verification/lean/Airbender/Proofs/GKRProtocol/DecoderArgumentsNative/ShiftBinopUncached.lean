import Airbender.Import.GKRProtocol.DecoderArgumentsImport
import Airbender.Proofs.GKRProtocol.CleanArithmeticNative.ShiftBinopUncached
import Airbender.Proofs.GKRProtocol.FunctionalLinksNative.ShiftBinopUncached
import Airbender.Proofs.GKRProtocol.LookupSourceNative.ShiftBinopUncached
import Airbender.Review.Circuits.ShiftBinop.Artifact

namespace Airbender.Compiler.DecoderArgumentsNative.ShiftBinopUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_decoder_arguments native from "artifacts/compiler/shift-binop-uncached.json"
  certificate "artifacts/compiler/lookup/shift-binop-uncached.json"
  clean_model Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native
  base_model Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native
  lookup_model Airbender.Compiler.LookupNative.ShiftBinopUncached.native
  query_model Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native
  links_model Airbender.Compiler.FunctionalLinksNative.ShiftBinopUncached.native
  source_query Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.query10
  trace_columns Airbender.ShiftBinop.importedConstraintsTraceColumns
  decoder_columns Airbender.ShiftBinop.importedConstraintsDecoderColumns

end Airbender.Compiler.DecoderArgumentsNative.ShiftBinopUncached
