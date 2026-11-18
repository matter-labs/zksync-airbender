module
public import Human.Import.NativeRamProducts
public import Human.Circuits.InitsTeardowns.UnifiedArtifact
public import Human.Compiler.Captures.Unified
public import Human.Circuits.InitsTeardowns.Native.Products
public import Human.Compiler.NativeMemory
public import Human.Circuits.InitsTeardowns.Theorems

@[expose] public section

namespace Airbender.InitsTeardowns.Native

import_ram_products unifiedArtifact from "../../cs/compiled_circuits/unified_reduced_machine_layout_gkr.json" unified_inline

/-- The cached unified capture is the circuit that production proves. Its initialization gates have the layout
    `InitsTeardowns.unifiedLayout`: the same sets and teardown columns, and each gate pairs the adjacent sets 2k and
    2k + 1. Its memory-product graph is the extracted graph. Extraction checks the virtual setup address inputs, the
    window geometry and the output map. -/
def UnifiedBindingClaim : Prop :=
  Compiler.Captures.Unified.imported.circuit.initsTeardownsLayout false = .ok InitsTeardowns.unifiedLayout ∧
    Extract.extract .unified Compiler.Captures.Unified.imported.circuit = .ok unifiedArtifact

/-- Compiled acceptance of the cached unified capture gives the products of the boot interface initialization and
    teardown tokens (`Witness.initTokens` and `Witness.teardownTokens`) on its two output wires.
    On every row the compiled initialization pairs, extension copies and extension products hold
    (`NativeMemory.InitializationHolds`), with the window shift of the bound layout. The virtual setup wires hold
    the setup address limbs of the row (`withSetupAddresses`). The memory bank reads the instance assignment.
    The public windows of the compiled tuples are the instance top bits, below the verifier ceiling.
    Product equality does not assert a token permutation. -/
def UnifiedSoundnessClaim : Prop :=
  ∀ {E : Type} [CommRing E] (challenges : Compiler.NativeMemory.Challenges E)
    (witness : InitsTeardowns.Witness babyBearModulus InitsTeardowns.unifiedLayout)
    (physical : Nat → GKRAddress → ZMod babyBearModulus) (values : Nat → GKRAddress → E),
    (∀ set : Fin InitsTeardowns.unifiedLayout.sets.size, challenges.memory.windows set.val = witness.topBits[set]) →
    (∀ top ∈ witness.topBits.toList, top < InitsTeardowns.maxTopBit) →
    (∀ row column, physical row (.BaseLayerMemory column) = memoryBank 96 witness row column) →
    (∀ row < unifiedArtifact.layout.rows, Compiler.NativeMemory.InitializationHolds
      Compiler.Captures.Unified.imported.circuit InitsTeardowns.unifiedLayout challenges
      (withSetupAddresses InitsTeardowns.unifiedLayout row (physical row)) (values row)) →
    outputProduct unifiedArtifact unifiedArtifact.terminal values =
      (witness.teardownTokens.map challenges.memory.encode).prod ∧
    outputProduct unifiedArtifact unifiedArtifact.initial values =
      (witness.initTokens.map challenges.memory.encode).prod

/-- An initialization instance with checked public windows meets the compiled acceptance premises. -/
def UnifiedSatisfiableClaim : Prop :=
  ∃ (challenges : Compiler.NativeMemory.Challenges (ZMod babyBearModulus))
    (witness : InitsTeardowns.Witness babyBearModulus InitsTeardowns.unifiedLayout)
    (physical : Nat → GKRAddress → ZMod babyBearModulus) (values : Nat → GKRAddress → ZMod babyBearModulus),
    (∀ set : Fin InitsTeardowns.unifiedLayout.sets.size, challenges.memory.windows set.val = witness.topBits[set]) ∧
    (∀ top ∈ witness.topBits.toList, top < InitsTeardowns.maxTopBit) ∧
    (∀ row column, physical row (.BaseLayerMemory column) = memoryBank 96 witness row column) ∧
    (∀ row < unifiedArtifact.layout.rows, Compiler.NativeMemory.InitializationHolds
      Compiler.Captures.Unified.imported.circuit InitsTeardowns.unifiedLayout challenges
      (withSetupAddresses InitsTeardowns.unifiedLayout row (physical row)) (values row))

end Airbender.InitsTeardowns.Native
