import GKRProtocol.DecoderArgumentsImport
import GKRProtocol.CleanArithmeticNative.JumpBranchUncached
import GKRProtocol.FunctionalLinksNative.JumpBranchUncached
import GKRProtocol.LookupSourceNative.JumpBranchUncached
import Airbender.Review.Circuits.JumpBranchSlt.Artifact

namespace Airbender.Compiler.DecoderArgumentsNative.JumpBranchUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_decoder_arguments native from "artifacts/compiler/jump-branch-uncached.json"
  certificate "artifacts/compiler/lookup/jump-branch-uncached.json"
  clean_model Airbender.Compiler.CleanArithmeticNative.JumpBranchUncached.native
  base_model Airbender.Compiler.FullArithmeticNative.JumpBranchUncached.native
  lookup_model Airbender.Compiler.LookupNative.JumpBranchUncached.native
  query_model Airbender.Compiler.LookupSourceNative.JumpBranchUncached.native
  links_model Airbender.Compiler.FunctionalLinksNative.JumpBranchUncached.native
  source_query Airbender.Compiler.LookupSourceNative.JumpBranchUncached.native.query12
  trace_columns Airbender.JumpBranchSlt.importedConstraintsTraceColumns
  decoder_columns Airbender.JumpBranchSlt.importedConstraintsDecoderColumns

end Airbender.Compiler.DecoderArgumentsNative.JumpBranchUncached
