module
public import Human.Import.NativeRamProducts
public import Human.Circuits.InitsTeardowns.Artifact
public import Human.Circuits.InitsTeardowns.Native.Products
public import Human.Compiler.NativeMemory
public import Human.Circuits.InitsTeardowns.Theorems

@[expose] public section

namespace Airbender.InitsTeardowns.Native

import_ram_products standaloneArtifact from "../../cs/compiled_circuits/inits_and_teardowns_layout_no_caches_gkr.json"

/-- The memory-product graph is extracted from the existing typed circuit artifact. -/
def StandaloneBindingClaim : Prop :=
  Extract.extract .standalone importedLayoutCircuit = .ok standaloneArtifact

/-- Compiled acceptance of the standalone capture gives the products of the boot interface initialization and
    teardown tokens (`Witness.initTokens` and `Witness.teardownTokens`) on its two output wires.
    On every row the compiled initialization pairs, extension copies and extension products hold
    (`NativeMemory.InitializationHolds`), with the window shift of the bound layout. The virtual setup wires hold
    the setup address limbs of the row (`withSetupAddresses`). The memory bank reads the instance assignment.
    The public windows of the compiled tuples are the instance top bits, below the verifier ceiling.
    Product equality does not assert a token permutation. -/
def StandaloneSoundnessClaim : Prop :=
  ∀ {E : Type} [CommRing E] (challenges : Compiler.NativeMemory.Challenges E)
    (witness : InitsTeardowns.Witness babyBearModulus InitsTeardowns.importedLayout)
    (physical : Nat → GKRAddress → ZMod babyBearModulus) (values : Nat → GKRAddress → E),
    (∀ set : Fin InitsTeardowns.importedLayout.sets.size, challenges.memory.windows set.val = witness.topBits[set]) →
    (∀ top ∈ witness.topBits.toList, top < InitsTeardowns.maxTopBit) →
    (∀ row column, physical row (.BaseLayerMemory column) = memoryBank 0 witness row column) →
    (∀ row < standaloneArtifact.layout.rows, Compiler.NativeMemory.InitializationHolds importedLayoutCircuit
      InitsTeardowns.importedLayout challenges (withSetupAddresses InitsTeardowns.importedLayout row (physical row))
      (values row)) →
    outputProduct standaloneArtifact standaloneArtifact.terminal values =
      (witness.teardownTokens.map challenges.memory.encode).prod ∧
    outputProduct standaloneArtifact standaloneArtifact.initial values =
      (witness.initTokens.map challenges.memory.encode).prod

/-- An initialization instance with checked public windows meets the compiled acceptance premises. -/
def StandaloneSatisfiableClaim : Prop :=
  ∃ (challenges : Compiler.NativeMemory.Challenges (ZMod babyBearModulus))
    (witness : InitsTeardowns.Witness babyBearModulus InitsTeardowns.importedLayout)
    (physical : Nat → GKRAddress → ZMod babyBearModulus) (values : Nat → GKRAddress → ZMod babyBearModulus),
    (∀ set : Fin InitsTeardowns.importedLayout.sets.size, challenges.memory.windows set.val = witness.topBits[set]) ∧
    (∀ top ∈ witness.topBits.toList, top < InitsTeardowns.maxTopBit) ∧
    (∀ row column, physical row (.BaseLayerMemory column) = memoryBank 0 witness row column) ∧
    (∀ row < standaloneArtifact.layout.rows, Compiler.NativeMemory.InitializationHolds importedLayoutCircuit
      InitsTeardowns.importedLayout challenges (withSetupAddresses InitsTeardowns.importedLayout row (physical row))
      (values row))

end Airbender.InitsTeardowns.Native
