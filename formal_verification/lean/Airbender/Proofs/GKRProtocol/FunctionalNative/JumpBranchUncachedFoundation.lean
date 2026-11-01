import Airbender.Import.GKRProtocol.FunctionalImport
import Airbender.Proofs.GKRProtocol.FullArithmeticNative.JumpBranchUncached
import Airbender.Proofs.GKRProtocol.LookupNative.JumpBranchUncached
import Airbender.Proofs.GKRProtocol.ProductNative.JumpBranchUncached

namespace Airbender.Compiler.FunctionalNative.JumpBranchUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_functional_graph native from "artifacts/compiler/jump-branch-uncached.json"
  typing Airbender.Compiler.ConsumerNative.JumpBranchUncached.native.typing
  lookup Airbender.Compiler.LookupNative.JumpBranchUncached.native
  product Airbender.Compiler.ProductNative.JumpBranchUncached.native
  base Airbender.Compiler.FullArithmeticNative.JumpBranchUncached.native

noncomputable def native.canonical {R : Type} [CommRing R]
  (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
  (baseValue : GKRAddress → Source.BaseField) : GKRAddress → R :=
  Functional.read native.isBase (hom ∘ baseValue)
    (native.program.execute hom challenges gamma native.isBase (hom ∘ baseValue) (fun _ => 0))

end Airbender.Compiler.FunctionalNative.JumpBranchUncached
