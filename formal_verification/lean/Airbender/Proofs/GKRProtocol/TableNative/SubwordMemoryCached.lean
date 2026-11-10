import Airbender.Import.GKRProtocol.TableImport
import Airbender.Proofs.GKRProtocol.SourceFreshnessChecks.SubwordMemoryCached.Certificate

namespace Airbender.Compiler.TableNative.SubwordMemoryCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

import_source_table_layout native from "artifacts/compiler/subword-memory-cached.json"
  source "artifacts/compiler/subword-memory-cached-source.json"
  source_lookups Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native
  native_model Airbender.Compiler.LookupNative.SubwordMemoryCached.native
  roles Airbender.Compiler.ConsumerNative.SubwordMemoryCached.native.typing
  using_freshness Airbender.Compiler.SourceFreshnessChecks.SubwordMemoryCached

end Airbender.Compiler.TableNative.SubwordMemoryCached
