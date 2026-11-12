module
public import Human.Import.NativeRamProducts
public import Human.Circuits.InitsTeardowns.UnifiedArtifact
public import Human.Circuits.InitsTeardowns.Native.Products

@[expose] public section

namespace Airbender.InitsTeardowns.Native

import_ram_products unifiedArtifact from "../../cs/compiled_circuits/unified_reduced_machine_layout_no_caches_gkr.json" unified_inline

/-- The memory-product graph is extracted from the existing typed circuit artifact. -/
def UnifiedBindingClaim : Prop :=
  Extract.extract .unified unifiedLayoutCircuit = .ok unifiedArtifact

/-- Every accepted native gate computes the exact initialization and teardown token products.
    Acceptance binds every native row, the raw memory columns, extension wires and public product challenges.
    Product equality does not assert a token permutation. -/
def UnifiedSoundnessClaim : Prop :=
  ∀ {E : Type} [CommRing E] (parameters : Parameters babyBearModulus E) (raw : Raw babyBearModulus)
    (wires : Wires E), Accepted unifiedArtifact parameters raw wires →
    rootProduct unifiedArtifact unifiedArtifact.terminal wires =
      ((ramTokens unifiedArtifact.layout parameters raw .terminal).map parameters.encode).prod ∧
    rootProduct unifiedArtifact unifiedArtifact.initial wires =
      ((ramTokens unifiedArtifact.layout parameters raw .initial).map parameters.encode).prod

/-- The native memory-product gate premises admit an assignment over BabyBear. -/
def UnifiedSatisfiableClaim : Prop :=
  ∃ (parameters : Parameters babyBearModulus (ZMod babyBearModulus))
    (raw : Raw babyBearModulus) (wires : Wires (ZMod babyBearModulus)),
    Accepted unifiedArtifact parameters raw wires

end Airbender.InitsTeardowns.Native
