import Airbender.Proofs.GKRProtocol.CleanArgumentChecks.ShiftBinopUncached.Certificate

namespace Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

import_clean_generic_arguments native from "artifacts/compiler/shift-binop-uncached.json"
  certificate "artifacts/compiler/lookup/shift-binop-uncached.json"
  clean_model Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native
  base_model Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native
  lookup_model Airbender.Compiler.LookupNative.ShiftBinopUncached.native
  query_model Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native
  links_model Airbender.Compiler.FunctionalLinksNative.ShiftBinopUncached.native
  start 0 stop 5 part_size 8 phase 1 using_checks Airbender.Compiler.CleanArgumentChecks.ShiftBinopUncached

end Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached
