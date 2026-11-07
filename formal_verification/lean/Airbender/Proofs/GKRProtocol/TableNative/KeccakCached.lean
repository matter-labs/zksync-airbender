import Airbender.Import.GKRProtocol.TableImport
import Airbender.Proofs.GKRProtocol.SourceFreshnessChecks.KeccakCached.Certificate

namespace Airbender.Compiler.TableNative.KeccakCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

import_source_table_layout native from "artifacts/compiler/keccak-cached.json"
  source "artifacts/compiler/keccak-cached-source.json"
  source_lookups Airbender.Compiler.LookupSourceNative.KeccakCached.native
  native_model Airbender.Compiler.LookupNative.KeccakCached.native
  roles Airbender.Compiler.ConsumerNative.KeccakCached.native.typing
  using_freshness Airbender.Compiler.SourceFreshnessChecks.KeccakCached

end Airbender.Compiler.TableNative.KeccakCached
