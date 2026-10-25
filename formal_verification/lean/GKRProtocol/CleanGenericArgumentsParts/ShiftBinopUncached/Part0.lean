import GKRProtocol.CleanGenericArgumentsImport
import GKRProtocol.CleanArithmeticNative.ShiftBinopUncached
import GKRProtocol.FunctionalLinksNative.ShiftBinopUncached

namespace Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_clean_generic_arguments part0 from "artifacts/compiler/shift-binop-uncached.json"
  certificate "artifacts/compiler/lookup/shift-binop-uncached.json"
  clean_model Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native
  base_model Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native
  lookup_model Airbender.Compiler.LookupNative.ShiftBinopUncached.native
  query_model Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native
  links_model Airbender.Compiler.FunctionalLinksNative.ShiftBinopUncached.native
  start 0 stop 5

end Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native
