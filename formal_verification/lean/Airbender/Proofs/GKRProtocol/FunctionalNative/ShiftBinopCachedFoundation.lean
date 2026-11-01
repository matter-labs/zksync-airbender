import Airbender.Import.GKRProtocol.FunctionalImport
import Airbender.Proofs.GKRProtocol.FullArithmeticNative.ShiftBinopCached
import Airbender.Proofs.GKRProtocol.LookupNative.ShiftBinopCached
import Airbender.Proofs.GKRProtocol.ProductNative.ShiftBinopCached

namespace Airbender.Compiler.FunctionalNative.ShiftBinopCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_functional_graph native from "artifacts/compiler/shift-binop-cached.json"
  typing Airbender.Compiler.ConsumerNative.ShiftBinopCached.native.typing
  lookup Airbender.Compiler.LookupNative.ShiftBinopCached.native
  product Airbender.Compiler.ProductNative.ShiftBinopCached.native
  base Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native

noncomputable def native.canonical {R : Type} [CommRing R]
  (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
  (baseValue : GKRAddress → Source.BaseField) : GKRAddress → R :=
  Functional.read native.isBase (hom ∘ baseValue)
    (native.program.execute hom challenges gamma native.isBase (hom ∘ baseValue) (fun _ => 0))

end Airbender.Compiler.FunctionalNative.ShiftBinopCached
