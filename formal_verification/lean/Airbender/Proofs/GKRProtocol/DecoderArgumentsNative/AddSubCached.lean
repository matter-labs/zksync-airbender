import Airbender.Import.GKRProtocol.DecoderArgumentsImport
import Airbender.Proofs.GKRProtocol.CleanArithmeticNative.AddSubCached
import Airbender.Proofs.GKRProtocol.FunctionalLinksNative.AddSubCached
import Airbender.Proofs.GKRProtocol.LookupSourceNative.AddSubCached
import Airbender.Review.Circuits.AddSub.Artifact

namespace Airbender.Compiler.DecoderArgumentsNative.AddSubCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_decoder_arguments native from "artifacts/compiler/add-sub-cached.json"
  certificate "artifacts/compiler/lookup/add-sub-cached.json"
  clean_model Airbender.Compiler.CleanArithmeticNative.AddSubCached.native
  base_model Airbender.Compiler.FullArithmeticNative.AddSubCached.native
  lookup_model Airbender.Compiler.LookupNative.AddSubCached.native
  query_model Airbender.Compiler.LookupSourceNative.AddSubCached.native
  links_model Airbender.Compiler.FunctionalLinksNative.AddSubCached.native
  source_query Airbender.Compiler.LookupSourceNative.AddSubCached.native.query14
  trace_columns Airbender.AddSub.importedConstraintsTraceColumns
  decoder_columns Airbender.AddSub.importedConstraintsDecoderColumns

end Airbender.Compiler.DecoderArgumentsNative.AddSubCached
