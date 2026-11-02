import Airbender.Import.GKRProtocol.TableImport
import Airbender.Proofs.GKRProtocol.SourceFreshnessChecks.UnifiedCached.Certificate

namespace Airbender.Compiler.TableNative.UnifiedCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

import_source_table_layout native from "artifacts/compiler/unified-cached.json"
  source "artifacts/compiler/unified-cached-source.json"
  source_lookups Airbender.Compiler.LookupSourceNative.UnifiedCached.native
  native_model Airbender.Compiler.LookupNative.UnifiedCached.native
  roles Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing
  using_freshness Airbender.Compiler.SourceFreshnessChecks.UnifiedCached

end Airbender.Compiler.TableNative.UnifiedCached
