module
public import Human.Import.NativeRamProducts
public import Human.Circuits.InitsTeardowns.Artifact
public import Human.Circuits.InitsTeardowns.Native.Products

@[expose] public section

namespace Airbender.InitsTeardowns.Native

import_ram_products standaloneArtifact from "../../cs/compiled_circuits/inits_and_teardowns_layout_no_caches_gkr.json"

/-- The memory-product graph is extracted from the existing typed circuit artifact. -/
def StandaloneBindingClaim : Prop :=
  Extract.extract .standalone importedLayoutCircuit = .ok standaloneArtifact

/-- Every accepted native gate computes the exact initialization and teardown token products.
    Acceptance binds every native row, the raw memory columns, extension wires and public product challenges.
    Product equality does not assert a token permutation. -/
def StandaloneSoundnessClaim : Prop :=
  ∀ {E : Type} [CommRing E] (parameters : Parameters babyBearModulus E) (raw : Raw babyBearModulus)
    (wires : Wires E), Accepted standaloneArtifact parameters raw wires →
    rootProduct standaloneArtifact standaloneArtifact.terminal wires =
      ((ramTokens standaloneArtifact.layout parameters raw .terminal).map parameters.encode).prod ∧
    rootProduct standaloneArtifact standaloneArtifact.initial wires =
      ((ramTokens standaloneArtifact.layout parameters raw .initial).map parameters.encode).prod

/-- The native memory-product gate premises admit an assignment over BabyBear. -/
def StandaloneSatisfiableClaim : Prop :=
  ∃ (parameters : Parameters babyBearModulus (ZMod babyBearModulus))
    (raw : Raw babyBearModulus) (wires : Wires (ZMod babyBearModulus)),
    Accepted standaloneArtifact parameters raw wires

end Airbender.InitsTeardowns.Native
