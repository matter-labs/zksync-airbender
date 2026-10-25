import GKRProtocol.WindowedNative.UnifiedCachedWitness
import GKRProtocol.VirtualInitialization

namespace Airbender.Compiler.WindowedNative.UnifiedCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

theorem public_boundary_outputs (publicTops : Nat → Nat) {R : Type} [CommRing R]
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (sourceValue : Fin 145 → Source.BaseField) (counts : Fin 3 → Source.BaseField)
    (row : Fin Airbender.Compiler.MaterializedNative.UnifiedCached.native.model.imported.data.length)
    (fallback baseValue : GKRAddress → Source.BaseField) (values : GKRAddress → R)
    (witness : CompleteActualRowWitness publicTops hom challenges gamma sourceValue counts row
      (initializationVirtualOracle row.val fallback) baseValue values)
    (parameters : Initialization.Parameters babyBearModulus Source.BaseField)
    (windows : ∀ set : Fin 2, parameters.windows set.val = publicTops set.val)
    (windowBound : ∀ set : Fin 2, publicTops set.val < 128) :
    values (.InnerLayer 4 8) = (((List.finRange 2).map (fun set : Fin 2 =>
      (Initialization.Leaf.mk .terminal set.val Initialization.unified.layout.columns[set]).token
        Initialization.unified.layout parameters (fun _ column => baseValue (.BaseLayerMemory column)) row.val)).map
          (memoryTokenFingerprint hom challenges)).prod ∧
    values (.InnerLayer 4 9) = (((List.finRange 2).map (fun set : Fin 2 =>
      (Initialization.Leaf.mk .initial set.val Initialization.unified.layout.columns[set]).token
        Initialization.unified.layout parameters (fun _ column => baseValue (.BaseLayerMemory column)) row.val)).map
          (memoryTokenFingerprint hom challenges)).prod := by
  have low := witness.2.1 (.VirtualSetup .InitsAndTeardownsLow) (by decide +kernel)
  have high := witness.2.1 (.VirtualSetup .InitsAndTeardownsHigh) (by decide +kernel)
  change baseValue (.VirtualSetup .InitsAndTeardownsLow) = (Initialization.addressLo row.val : Nat) at low
  change baseValue (.VirtualSetup .InitsAndTeardownsHigh) = (row.val / 16384 : Nat) at high
  have tokens (stageKind : Initialization.Phase) (set : Fin 2) :
      windowedBoundaryToken (Airbender.Compiler.MemoryNative.UnifiedCached.native.sourceValues baseValue)
        publicTops stageKind set.val 512 =
      (Initialization.Leaf.mk stageKind set.val Initialization.unified.layout.columns[set]).token
        Initialization.unified.layout parameters (fun _ column => baseValue (.BaseLayerMemory column)) row.val := by
    apply windowed_public_leaf parameters _ _ ⟨row.val, row.isLt⟩ publicTops windows windowBound low high set stageKind
    all_goals fin_cases set <;> rfl
  constructor
  · rw [witness.2.2.1]
    apply congrArg List.prod
    apply congrArg (List.map (memoryTokenFingerprint hom challenges))
    apply List.map_congr_left
    intro set _
    exact tokens .terminal set
  · rw [witness.2.2.2.1]
    apply congrArg List.prod
    apply congrArg (List.map (memoryTokenFingerprint hom challenges))
    apply List.map_congr_left
    intro set _
    exact tokens .initial set

end Airbender.Compiler.WindowedNative.UnifiedCached
