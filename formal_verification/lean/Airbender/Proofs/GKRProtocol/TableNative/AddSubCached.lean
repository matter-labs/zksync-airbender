import Airbender.Import.GKRProtocol.TableImport
import Airbender.Proofs.GKRProtocol.SourceFreshnessChecks.AddSubCached.Certificate

namespace Airbender.Compiler.TableNative.AddSubCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

import_source_table_layout native from "artifacts/compiler/add-sub-cached.json"
  source "artifacts/compiler/add-sub-cached-source.json"
  source_lookups Airbender.Compiler.LookupSourceNative.AddSubCached.native
  native_model Airbender.Compiler.LookupNative.AddSubCached.native
  roles Airbender.Compiler.ConsumerNative.AddSubCached.native.typing
  using_freshness Airbender.Compiler.SourceFreshnessChecks.AddSubCached

end Airbender.Compiler.TableNative.AddSubCached
