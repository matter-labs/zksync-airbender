import Airbender.Proofs.GKRProtocol.CleanArgumentChecks.ShiftBinopCached.Certificate

namespace Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

import_clean_generic_arguments native from "artifacts/compiler/shift-binop-cached.json"
  certificate "artifacts/compiler/lookup/shift-binop-cached.json"
  clean_model Airbender.Compiler.CleanArithmeticNative.ShiftBinopCached.native
  base_model Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native
  lookup_model Airbender.Compiler.LookupNative.ShiftBinopCached.native
  query_model Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native
  links_model Airbender.Compiler.FunctionalLinksNative.ShiftBinopCached.native
  start 0 stop 5 part_size 8 phase 1 using_checks Airbender.Compiler.CleanArgumentChecks.ShiftBinopCached

end Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopCached
