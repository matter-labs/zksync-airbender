import Airbender.Import.GKRProtocol.TableImport
import Airbender.Proofs.GKRProtocol.SourceFreshnessChecks.MulDivUncached.Certificate

namespace Airbender.Compiler.TableNative.MulDivUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

import_source_table_layout native from "artifacts/compiler/mul-div-uncached.json"
  source "artifacts/compiler/mul-div-uncached-source.json"
  source_lookups Airbender.Compiler.LookupSourceNative.MulDivUncached.native
  native_model Airbender.Compiler.LookupNative.MulDivUncached.native
  roles Airbender.Compiler.ConsumerNative.MulDivUncached.native.typing
  using_freshness Airbender.Compiler.SourceFreshnessChecks.MulDivUncached

end Airbender.Compiler.TableNative.MulDivUncached
