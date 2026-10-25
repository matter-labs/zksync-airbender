import GKRProtocol.DecoderArgumentsImport
import GKRProtocol.CleanArithmeticNative.JumpBranchCached
import GKRProtocol.FunctionalLinksNative.JumpBranchCached
import GKRProtocol.LookupSourceNative.JumpBranchCached
import Airbender.Review.Circuits.JumpBranchSlt.Artifact

namespace Airbender.Compiler.DecoderArgumentsNative.JumpBranchCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_decoder_arguments native from "artifacts/compiler/jump-branch-cached.json"
  certificate "artifacts/compiler/lookup/jump-branch-cached.json"
  clean_model Airbender.Compiler.CleanArithmeticNative.JumpBranchCached.native
  base_model Airbender.Compiler.FullArithmeticNative.JumpBranchCached.native
  lookup_model Airbender.Compiler.LookupNative.JumpBranchCached.native
  query_model Airbender.Compiler.LookupSourceNative.JumpBranchCached.native
  links_model Airbender.Compiler.FunctionalLinksNative.JumpBranchCached.native
  source_query Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.query12
  trace_columns Airbender.JumpBranchSlt.importedConstraintsTraceColumns
  decoder_columns Airbender.JumpBranchSlt.importedConstraintsDecoderColumns

end Airbender.Compiler.DecoderArgumentsNative.JumpBranchCached
