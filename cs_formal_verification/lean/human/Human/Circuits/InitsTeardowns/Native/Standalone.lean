module
public import Human.Import.NativeRamProducts
public import Human.Circuits.InitsTeardowns.Artifact
public import Human.Circuits.InitsTeardowns.Native.Products
public import Human.Circuits.InitsTeardowns.Theorems

@[expose] public section

namespace Airbender.InitsTeardowns.Native

import_ram_products standaloneArtifact from "../../cs/compiled_circuits/inits_and_teardowns_layout_no_caches_gkr.json"

/-- The memory-product graph is extracted from the existing typed circuit artifact. -/
def StandaloneBindingClaim : Prop :=
  Extract.extract .standalone importedLayoutCircuit = .ok standaloneArtifact

/-- Every accepted native gate computes the products of the boot interface initialization and teardown tokens
    (`Witness.initTokens` and `Witness.teardownTokens`).
    The public product windows are the instance top bits, below the verifier ceiling.
    The native memory bank reads the instance assignment. The kernel checks its column offset against the
    imported teardown placements. Acceptance binds every native row, extension wire and public product challenge.
    Product equality does not assert a token permutation. -/
def StandaloneSoundnessClaim : Prop :=
  ∀ {E : Type} [CommRing E] (parameters : Parameters babyBearModulus E)
    (witness : InitsTeardowns.Witness babyBearModulus InitsTeardowns.importedLayout) (wires : Wires E),
    (∀ set : Fin InitsTeardowns.importedLayout.sets.size, parameters.windows set.val = witness.topBits[set]) →
    (∀ top ∈ witness.topBits.toList, top < InitsTeardowns.maxTopBit) →
    Accepted standaloneArtifact parameters (memoryBank 0 witness) wires →
    rootProduct standaloneArtifact standaloneArtifact.terminal wires = (witness.teardownTokens.map parameters.encode).prod ∧
    rootProduct standaloneArtifact standaloneArtifact.initial wires = (witness.initTokens.map parameters.encode).prod

/-- An initialization instance with checked public windows meets every native memory-product gate premise. -/
def StandaloneSatisfiableClaim : Prop :=
  ∃ (parameters : Parameters babyBearModulus (ZMod babyBearModulus))
    (witness : InitsTeardowns.Witness babyBearModulus InitsTeardowns.importedLayout)
    (wires : Wires (ZMod babyBearModulus)),
    (∀ set : Fin InitsTeardowns.importedLayout.sets.size, parameters.windows set.val = witness.topBits[set]) ∧
    (∀ top ∈ witness.topBits.toList, top < InitsTeardowns.maxTopBit) ∧
    Accepted standaloneArtifact parameters (memoryBank 0 witness) wires

end Airbender.InitsTeardowns.Native
