import Airbender.Import.GKRProtocol.TableImport
import Airbender.Proofs.GKRProtocol.SourceFreshnessChecks.BigintCached.Certificate

namespace Airbender.Compiler.TableNative.BigintCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

import_source_table_layout native from "artifacts/compiler/bigint-cached.json"
  source "artifacts/compiler/bigint-cached-source.json"
  source_lookups Airbender.Compiler.LookupSourceNative.BigintCached.native
  native_model Airbender.Compiler.LookupNative.BigintCached.native
  roles Airbender.Compiler.ConsumerNative.BigintCached.native.typing
  using_freshness Airbender.Compiler.SourceFreshnessChecks.BigintCached

end Airbender.Compiler.TableNative.BigintCached
