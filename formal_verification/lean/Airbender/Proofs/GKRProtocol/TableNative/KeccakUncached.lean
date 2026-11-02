import Airbender.Import.GKRProtocol.TableImport
import Airbender.Proofs.GKRProtocol.SourceFreshnessChecks.KeccakUncached.Certificate

namespace Airbender.Compiler.TableNative.KeccakUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

import_source_table_layout native from "artifacts/compiler/keccak-uncached.json"
  source "artifacts/compiler/keccak-uncached-source.json"
  source_lookups Airbender.Compiler.LookupSourceNative.KeccakUncached.native
  native_model Airbender.Compiler.LookupNative.KeccakUncached.native
  roles Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing
  using_freshness Airbender.Compiler.SourceFreshnessChecks.KeccakUncached

end Airbender.Compiler.TableNative.KeccakUncached
