module
import all Mathlib.Data.List.Sort
public import Proven.Import.GKRProtocol.FunctionalImport
public import Proven.GKRProtocol.FullArithmeticNative.ShiftBinopCached
public import Proven.GKRProtocol.LookupNative.ShiftBinopCached
public import Proven.GKRProtocol.ProductNative.ShiftBinopCached

@[expose] public section
set_option warningAsError true

namespace Airbender.Compiler.FunctionalNative.ShiftBinopCached
open Airbender Airbender.Compiler
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
