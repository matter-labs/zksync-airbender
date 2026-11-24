module
import all Mathlib.Data.List.Sort
public import Proven.Import.GKRProtocol.FunctionalImport
public import Proven.GKRProtocol.FullArithmeticNative.SubwordMemoryCached
public import Proven.GKRProtocol.LookupNative.SubwordMemoryCached
public import Proven.GKRProtocol.ProductNative.SubwordMemoryCached

@[expose] public section
set_option warningAsError true

namespace Airbender.Compiler.FunctionalNative.SubwordMemoryCached
open Airbender Airbender.Compiler
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_functional_graph native from "artifacts/compiler/subword-memory-cached.json"
  typing Airbender.Compiler.ConsumerNative.SubwordMemoryCached.native.typing
  lookup Airbender.Compiler.LookupNative.SubwordMemoryCached.native
  product Airbender.Compiler.ProductNative.SubwordMemoryCached.native
  base Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native

noncomputable def native.canonical {R : Type} [CommRing R]
  (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
  (baseValue : GKRAddress → Source.BaseField) : GKRAddress → R :=
  Functional.read native.isBase (hom ∘ baseValue)
    (native.program.execute hom challenges gamma native.isBase (hom ∘ baseValue) (fun _ => 0))

end Airbender.Compiler.FunctionalNative.SubwordMemoryCached
