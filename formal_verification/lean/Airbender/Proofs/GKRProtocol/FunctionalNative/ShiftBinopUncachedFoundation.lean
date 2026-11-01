import Airbender.Import.GKRProtocol.FunctionalImport
import Airbender.Proofs.GKRProtocol.FullArithmeticNative.ShiftBinopUncached
import Airbender.Proofs.GKRProtocol.LookupNative.ShiftBinopUncached
import Airbender.Proofs.GKRProtocol.ProductNative.ShiftBinopUncached

namespace Airbender.Compiler.FunctionalNative.ShiftBinopUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_functional_graph native from "artifacts/compiler/shift-binop-uncached.json"
  typing Airbender.Compiler.ConsumerNative.ShiftBinopUncached.native.typing
  lookup Airbender.Compiler.LookupNative.ShiftBinopUncached.native
  product Airbender.Compiler.ProductNative.ShiftBinopUncached.native
  base Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native

noncomputable def native.canonical {R : Type} [CommRing R]
  (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
  (baseValue : GKRAddress → Source.BaseField) : GKRAddress → R :=
  Functional.read native.isBase (hom ∘ baseValue)
    (native.program.execute hom challenges gamma native.isBase (hom ∘ baseValue) (fun _ => 0))

end Airbender.Compiler.FunctionalNative.ShiftBinopUncached
