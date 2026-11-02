import Airbender.Import.GKRProtocol.TableImport
import Airbender.Proofs.GKRProtocol.SourceFreshnessChecks.BlakeGUncached.Certificate

namespace Airbender.Compiler.TableNative.BlakeGUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

import_source_table_layout native from "artifacts/compiler/blake-g-uncached.json"
  source "artifacts/compiler/blake-g-uncached-source.json"
  source_lookups Airbender.Compiler.LookupSourceNative.BlakeGUncached.native
  native_model Airbender.Compiler.LookupNative.BlakeGUncached.native
  roles Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing
  using_freshness Airbender.Compiler.SourceFreshnessChecks.BlakeGUncached

end Airbender.Compiler.TableNative.BlakeGUncached
