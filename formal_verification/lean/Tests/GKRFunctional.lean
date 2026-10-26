import Airbender.Proofs.GKRProtocol.FunctionalNative.AddSubCached

namespace Tests.GKRFunctional
open Airbender Airbender.Compiler
open Airbender.Compiler.FunctionalNative.AddSubCached
set_option warningAsError true
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

theorem rejects_duplicate_extension_writes :
    FunctionalProgram.check native.isBase [] [native.step0, native.step0] = false := by decide +kernel

theorem rejects_missing_extension_dependency :
    native.step46.check native.isBase [] = false := by decide +kernel

theorem rejects_base_overwrite :
    FunctionalStep.check native.isBase []
      [(GKRAddress.BaseLayerWitness 0, RExpression.coefficient (.natural 0))] = false := by decide +kernel

theorem rejects_changed_base_recipe :
    equal (NativeBaseRecipe.relation (AffineProgram.constant (Address := GKRAddress) (R := Nat) 0)
        FullArithmeticNative.AddSubCached.native.bank native.baseOutput0)
      FullArithmeticNative.AddSubCached.native.gate0.inputResidual = false := by decide +kernel

/-- Canonical construction uses no inverse or nonzero-challenge hypothesis. -/
theorem constructs_lookup_graph_at_zero_challenges (baseValue : GKRAddress → Source.BaseField) :
    ∀ gate ∈ LookupNative.AddSubCached.native.gates,
      gate.Holds (RingHom.id Source.BaseField) ⟨0, 0, fun _ => 0⟩ 0
        (native.canonical (RingHom.id Source.BaseField) ⟨0, 0, fun _ => 0⟩ 0 baseValue) :=
  native.canonical_lookups _ _ _ _

end Tests.GKRFunctional
