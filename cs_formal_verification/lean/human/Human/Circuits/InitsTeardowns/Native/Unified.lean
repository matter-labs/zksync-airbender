module
public import Human.Import.NativeRamProducts
public import Human.Circuits.InitsTeardowns.UnifiedArtifact
public import Human.Circuits.InitsTeardowns.Native.Products
public import Human.Circuits.InitsTeardowns.Theorems

@[expose] public section

namespace Airbender.InitsTeardowns.Native

import_ram_products unifiedArtifact from "../../cs/compiled_circuits/unified_reduced_machine_layout_no_caches_gkr.json" unified_inline

/-- The memory-product graph is extracted from the existing typed circuit artifact. -/
def UnifiedBindingClaim : Prop :=
  Extract.extract .unified unifiedLayoutCircuit = .ok unifiedArtifact

/-- Every accepted native gate computes the products of the boot interface initialization and teardown tokens
    (`Witness.initTokens` and `Witness.teardownTokens`).
    The public product windows are the instance top bits, below the verifier ceiling.
    The native memory bank reads the instance assignment. The kernel checks its column offset against the
    imported teardown placements. Acceptance binds every native row, extension wire and public product challenge.
    Product equality does not assert a token permutation. -/
def UnifiedSoundnessClaim : Prop :=
  ∀ {E : Type} [CommRing E] (parameters : Parameters babyBearModulus E)
    (witness : InitsTeardowns.Witness babyBearModulus InitsTeardowns.unifiedLayout) (wires : Wires E),
    (∀ set : Fin InitsTeardowns.unifiedLayout.sets.size, parameters.windows set.val = witness.topBits[set]) →
    (∀ top ∈ witness.topBits.toList, top < InitsTeardowns.maxTopBit) →
    Accepted unifiedArtifact parameters (memoryBank 96 witness) wires →
    rootProduct unifiedArtifact unifiedArtifact.terminal wires = (witness.teardownTokens.map parameters.encode).prod ∧
    rootProduct unifiedArtifact unifiedArtifact.initial wires = (witness.initTokens.map parameters.encode).prod

/-- An initialization instance with checked public windows meets every native memory-product gate premise. -/
def UnifiedSatisfiableClaim : Prop :=
  ∃ (parameters : Parameters babyBearModulus (ZMod babyBearModulus))
    (witness : InitsTeardowns.Witness babyBearModulus InitsTeardowns.unifiedLayout)
    (wires : Wires (ZMod babyBearModulus)),
    (∀ set : Fin InitsTeardowns.unifiedLayout.sets.size, parameters.windows set.val = witness.topBits[set]) ∧
    (∀ top ∈ witness.topBits.toList, top < InitsTeardowns.maxTopBit) ∧
    Accepted unifiedArtifact parameters (memoryBank 96 witness) wires

end Airbender.InitsTeardowns.Native
