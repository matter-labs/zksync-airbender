module
import all Mathlib.Data.List.Sort
public import Proven.Import.GKRProtocol.FunctionalImport
public import Proven.GKRProtocol.FullArithmeticNative.MulDivCached
public import Proven.GKRProtocol.LookupNative.MulDivCached
public import Proven.GKRProtocol.ProductNative.MulDivCached

@[expose] public section
set_option warningAsError true

namespace Airbender.Compiler.FunctionalNative.MulDivCached
open Airbender Airbender.Compiler
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_functional_graph native from "artifacts/compiler/mul-div-cached.json"
  typing Airbender.Compiler.ConsumerNative.MulDivCached.native.typing
  lookup Airbender.Compiler.LookupNative.MulDivCached.native
  product Airbender.Compiler.ProductNative.MulDivCached.native
  base Airbender.Compiler.FullArithmeticNative.MulDivCached.native

noncomputable def native.canonical {R : Type} [CommRing R]
  (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
  (baseValue : GKRAddress → Source.BaseField) : GKRAddress → R :=
  Functional.read native.isBase (hom ∘ baseValue)
    (native.program.execute hom challenges gamma native.isBase (hom ∘ baseValue) (fun _ => 0))

end Airbender.Compiler.FunctionalNative.MulDivCached
