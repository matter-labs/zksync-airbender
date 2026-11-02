import Airbender.Import.GKRProtocol.TableImport
import Airbender.Proofs.GKRProtocol.SourceFreshnessChecks.BlakeRoundUncached.Certificate

namespace Airbender.Compiler.TableNative.BlakeRoundUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

import_source_table_layout native from "artifacts/compiler/blake-round-uncached.json"
  source "artifacts/compiler/blake-round-uncached-source.json"
  source_lookups Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native
  native_model Airbender.Compiler.LookupNative.BlakeRoundUncached.native
  roles Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing
  using_freshness Airbender.Compiler.SourceFreshnessChecks.BlakeRoundUncached

end Airbender.Compiler.TableNative.BlakeRoundUncached
