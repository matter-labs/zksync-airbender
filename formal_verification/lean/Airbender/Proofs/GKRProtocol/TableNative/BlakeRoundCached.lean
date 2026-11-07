import Airbender.Import.GKRProtocol.TableImport
import Airbender.Proofs.GKRProtocol.SourceFreshnessChecks.BlakeRoundCached.Certificate

namespace Airbender.Compiler.TableNative.BlakeRoundCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

import_source_table_layout native from "artifacts/compiler/blake-round-cached.json"
  source "artifacts/compiler/blake-round-cached-source.json"
  source_lookups Airbender.Compiler.LookupSourceNative.BlakeRoundCached.native
  native_model Airbender.Compiler.LookupNative.BlakeRoundCached.native
  roles Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing
  using_freshness Airbender.Compiler.SourceFreshnessChecks.BlakeRoundCached

end Airbender.Compiler.TableNative.BlakeRoundCached
