import Airbender.Import.GKRProtocol.FunctionalImport
import Airbender.Proofs.GKRProtocol.FullArithmeticNative.UnifiedCached
import Airbender.Proofs.GKRProtocol.LookupNative.UnifiedCached
import Airbender.Proofs.GKRProtocol.ProductNative.UnifiedCached

namespace Airbender.Compiler.FunctionalNative.UnifiedCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_functional_graph native from "artifacts/compiler/unified-cached.json"
  typing Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing
  lookup Airbender.Compiler.LookupNative.UnifiedCached.native
  product Airbender.Compiler.ProductNative.UnifiedCached.native
  base Airbender.Compiler.FullArithmeticNative.UnifiedCached.native

noncomputable def native.canonical {R : Type} [CommRing R]
  (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
  (baseValue : GKRAddress → Source.BaseField) : GKRAddress → R :=
  Functional.read native.isBase (hom ∘ baseValue)
    (native.program.execute hom challenges gamma native.isBase (hom ∘ baseValue) (fun _ => 0))

end Airbender.Compiler.FunctionalNative.UnifiedCached
