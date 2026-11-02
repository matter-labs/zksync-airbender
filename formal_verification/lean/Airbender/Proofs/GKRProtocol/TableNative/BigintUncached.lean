import Airbender.Import.GKRProtocol.TableImport
import Airbender.Proofs.GKRProtocol.SourceFreshnessChecks.BigintUncached.Certificate

namespace Airbender.Compiler.TableNative.BigintUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

import_source_table_layout native from "artifacts/compiler/bigint-uncached.json"
  source "artifacts/compiler/bigint-uncached-source.json"
  source_lookups Airbender.Compiler.LookupSourceNative.BigintUncached.native
  native_model Airbender.Compiler.LookupNative.BigintUncached.native
  roles Airbender.Compiler.ConsumerNative.BigintUncached.native.typing
  using_freshness Airbender.Compiler.SourceFreshnessChecks.BigintUncached

end Airbender.Compiler.TableNative.BigintUncached
