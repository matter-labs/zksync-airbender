import Airbender.Import.GKRProtocol.TableImport
import Airbender.Proofs.GKRProtocol.SourceFreshnessChecks.MulDivCached.Certificate

namespace Airbender.Compiler.TableNative.MulDivCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

import_source_table_layout native from "artifacts/compiler/mul-div-cached.json"
  source "artifacts/compiler/mul-div-cached-source.json"
  source_lookups Airbender.Compiler.LookupSourceNative.MulDivCached.native
  native_model Airbender.Compiler.LookupNative.MulDivCached.native
  roles Airbender.Compiler.ConsumerNative.MulDivCached.native.typing
  using_freshness Airbender.Compiler.SourceFreshnessChecks.MulDivCached

end Airbender.Compiler.TableNative.MulDivCached
