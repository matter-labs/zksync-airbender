import Airbender.Import.GKRProtocol.TableImport
import Airbender.Proofs.GKRProtocol.SourceFreshnessChecks.AddSubUncached.Certificate

namespace Airbender.Compiler.TableNative.AddSubUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

import_source_table_layout native from "artifacts/compiler/add-sub-uncached.json"
  source "artifacts/compiler/add-sub-uncached-source.json"
  source_lookups Airbender.Compiler.LookupSourceNative.AddSubUncached.native
  native_model Airbender.Compiler.LookupNative.AddSubUncached.native
  roles Airbender.Compiler.ConsumerNative.AddSubUncached.native.typing
  using_freshness Airbender.Compiler.SourceFreshnessChecks.AddSubUncached

end Airbender.Compiler.TableNative.AddSubUncached
