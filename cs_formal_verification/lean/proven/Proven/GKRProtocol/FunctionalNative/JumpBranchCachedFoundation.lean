module
import all Mathlib.Data.List.Sort
public import Proven.Import.GKRProtocol.FunctionalImport
public import Proven.GKRProtocol.FullArithmeticNative.JumpBranchCached
public import Proven.GKRProtocol.LookupNative.JumpBranchCached
public import Proven.GKRProtocol.ProductNative.JumpBranchCached

@[expose] public section
set_option warningAsError true

namespace Airbender.Compiler.FunctionalNative.JumpBranchCached
open Airbender Airbender.Compiler
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_functional_graph native from "artifacts/compiler/jump-branch-cached.json"
  typing Airbender.Compiler.ConsumerNative.JumpBranchCached.native.typing
  lookup Airbender.Compiler.LookupNative.JumpBranchCached.native
  product Airbender.Compiler.ProductNative.JumpBranchCached.native
  base Airbender.Compiler.FullArithmeticNative.JumpBranchCached.native

noncomputable def native.canonical {R : Type} [CommRing R]
  (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
  (baseValue : GKRAddress → Source.BaseField) : GKRAddress → R :=
  Functional.read native.isBase (hom ∘ baseValue)
    (native.program.execute hom challenges gamma native.isBase (hom ∘ baseValue) (fun _ => 0))

end Airbender.Compiler.FunctionalNative.JumpBranchCached
