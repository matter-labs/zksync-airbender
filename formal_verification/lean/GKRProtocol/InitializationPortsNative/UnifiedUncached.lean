import GKRProtocol.InitializationPublic
import GKRProtocol.MemoryNative.UnifiedUncached
import GKRProtocol.FunctionalLinksNative.UnifiedUncached
import GKRProtocol.NativeWitness
import Airbender.Review.Circuits.Initialization.Artifact

namespace Airbender.Compiler.InitializationPortsNative.UnifiedUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

theorem geometry : Initialization.unified.layout.rows = 8388608 ∧
    Initialization.unified.layout.stride = 512 ∧ Initialization.unified.layout.columns.size = 2 := by decide +kernel

theorem source_read_tokens (physical : GKRAddress → Source.BaseField) :
    Airbender.Compiler.MemoryNative.UnifiedUncached.native.initializationReadRows.map (fun row => row.token (Airbender.Compiler.MemoryNative.UnifiedUncached.native.sourceValues physical)) =
      (List.finRange 2).map (fun set => sourceBoundaryToken (Airbender.Compiler.MemoryNative.UnifiedUncached.native.sourceValues physical) .terminal set.val 512) := by rfl

theorem read_products_from_base {R : Type} [CommRing R]
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R)
    (physical : GKRAddress → Source.BaseField) :
    (Airbender.Compiler.MemoryNative.UnifiedUncached.native.initializationReadRows.map (fun row => row.fingerprint (Airbender.Compiler.MemoryNative.UnifiedUncached.native.sourceValues physical) hom challenges)).prod =
      (((List.finRange 2).map (fun set => sourceBoundaryToken (Airbender.Compiler.MemoryNative.UnifiedUncached.native.sourceValues physical) .terminal set.val 512)).map
        (memoryTokenFingerprint hom challenges)).prod := by
  rw [← Source.MemoryRow.token_products Airbender.Compiler.MemoryNative.UnifiedUncached.native.initializationReadRows (Airbender.Compiler.MemoryNative.UnifiedUncached.native.sourceValues physical) hom challenges, source_read_tokens physical]

theorem source_write_tokens (physical : GKRAddress → Source.BaseField) :
    Airbender.Compiler.MemoryNative.UnifiedUncached.native.initializationWriteRows.map (fun row => row.token (Airbender.Compiler.MemoryNative.UnifiedUncached.native.sourceValues physical)) =
      (List.finRange 2).map (fun set => sourceBoundaryToken (Airbender.Compiler.MemoryNative.UnifiedUncached.native.sourceValues physical) .initial set.val 512) := by rfl

theorem write_products_from_base {R : Type} [CommRing R]
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R)
    (physical : GKRAddress → Source.BaseField) :
    (Airbender.Compiler.MemoryNative.UnifiedUncached.native.initializationWriteRows.map (fun row => row.fingerprint (Airbender.Compiler.MemoryNative.UnifiedUncached.native.sourceValues physical) hom challenges)).prod =
      (((List.finRange 2).map (fun set => sourceBoundaryToken (Airbender.Compiler.MemoryNative.UnifiedUncached.native.sourceValues physical) .initial set.val 512)).map
        (memoryTokenFingerprint hom challenges)).prod := by
  rw [← Source.MemoryRow.token_products Airbender.Compiler.MemoryNative.UnifiedUncached.native.initializationWriteRows (Airbender.Compiler.MemoryNative.UnifiedUncached.native.sourceValues physical) hom challenges, source_write_tokens physical]

theorem raw_columns (physical : GKRAddress → Source.BaseField)
    (set : Fin Initialization.unified.layout.columns.size) :
    (Airbender.Compiler.MemoryNative.UnifiedUncached.native.sourceValues physical).teardownTimestamp set.val 0 = physical (.BaseLayerMemory Initialization.unified.layout.columns[set].timeLo) ∧
    (Airbender.Compiler.MemoryNative.UnifiedUncached.native.sourceValues physical).teardownTimestamp set.val 1 = physical (.BaseLayerMemory Initialization.unified.layout.columns[set].timeHi) ∧
    (Airbender.Compiler.MemoryNative.UnifiedUncached.native.sourceValues physical).teardownValue set.val 0 = physical (.BaseLayerMemory Initialization.unified.layout.columns[set].valueLo) ∧
    (Airbender.Compiler.MemoryNative.UnifiedUncached.native.sourceValues physical).teardownValue set.val 1 = physical (.BaseLayerMemory Initialization.unified.layout.columns[set].valueHi) := by
  fin_cases set <;> exact ⟨rfl, rfl, rfl, rfl⟩

theorem public_leaf (physical : GKRAddress → Source.BaseField)
    (parameters : Initialization.Parameters babyBearModulus Source.BaseField)
    (row : Fin 8388608) (window : Nat) (windowBound : window + 1 < 128)
    (windows : ∀ set : Fin 2, parameters.windows set.val = window + set.val)
    (low : (Airbender.Compiler.MemoryNative.UnifiedUncached.native.sourceValues physical).initializationAddress 0 = (Initialization.addressLo row.val : Source.BaseField))
    (high : (Airbender.Compiler.MemoryNative.UnifiedUncached.native.sourceValues physical).initializationAddress 1 = (row.val / 16384 + window * 512 : Nat))
    (stageKind : Initialization.Phase) (set : Fin 2) :
    sourceBoundaryToken (Airbender.Compiler.MemoryNative.UnifiedUncached.native.sourceValues physical) stageKind set.val 512 =
      (Initialization.Leaf.mk stageKind set.val Initialization.unified.layout.columns[set]).token
        Initialization.unified.layout parameters (fun _ column => physical (.BaseLayerMemory column)) row.val := by
  have addresses := inline_public_addresses parameters (Airbender.Compiler.MemoryNative.UnifiedUncached.native.sourceValues physical) row window windows low high set
  have bounds := inline_public_bounds parameters row window windowBound windows set
  have raw := raw_columns physical set
  exact source_boundary_leaf Initialization.unified.layout parameters (Airbender.Compiler.MemoryNative.UnifiedUncached.native.sourceValues physical)
    (fun _ column => physical (.BaseLayerMemory column)) stageKind set row addresses.1 addresses.2 bounds.1 bounds.2
      raw.1 raw.2.1 raw.2.2.1 raw.2.2.2

theorem read_output_tokens {R : Type} [CommRing R]
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R)
    (physical : GKRAddress → Source.BaseField) (values : GKRAddress → R)
    (baseLaw : ∀ address, Airbender.Compiler.FunctionalNative.UnifiedUncached.native.isBase address = true → values address = hom (physical address))
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.bank.address) = 0)
    (affine : ∀ definition ∈ Airbender.Compiler.FunctionalNative.UnifiedUncached.native.definitions, definition.Holds hom challenges values)
    (products : ∀ gate ∈ Airbender.Compiler.ProductNative.UnifiedUncached.native.gates, gate.Holds hom challenges values) :
    values Airbender.Compiler.MemoryNative.UnifiedUncached.native.initializationReadOutput =
      (((List.finRange 2).map (fun set => sourceBoundaryToken (Airbender.Compiler.MemoryNative.UnifiedUncached.native.sourceValues physical) .terminal set.val 512)).map
        (memoryTokenFingerprint hom challenges)).prod := by
  let assignment : TypedAssignment R := ⟨physical, values⟩
  have typedEq : assignment.value Airbender.Compiler.ConsumerNative.UnifiedUncached.native.typing hom = values := TypedAssignment.value_eq assignment Airbender.Compiler.ConsumerNative.UnifiedUncached.native.typing hom baseLaw
  have defined : ∀ definition ∈ Airbender.Compiler.MemoryNative.UnifiedUncached.native.definitions, definition.Holds hom challenges (assignment.value Airbender.Compiler.ConsumerNative.UnifiedUncached.native.typing hom) := by
    rw [typedEq, ← Airbender.Compiler.FunctionalLinksNative.UnifiedUncached.native.memoryDefinitionsAgree]
    exact affine
  have holds := products
  rw [← typedEq] at holds
  have reduced := Airbender.Compiler.MemoryNative.UnifiedUncached.native.initializationReadSourceReduction hom challenges assignment defined (Airbender.Compiler.FunctionalLinksNative.UnifiedUncached.native.memoryCopies physical arithmetic) holds
  rw [typedEq] at reduced
  change values Airbender.Compiler.MemoryNative.UnifiedUncached.native.initializationReadOutput =
    (Airbender.Compiler.MemoryNative.UnifiedUncached.native.initializationReadRows.map (fun row => row.fingerprint (Airbender.Compiler.MemoryNative.UnifiedUncached.native.sourceValues physical) hom challenges)).prod at reduced
  rw [read_products_from_base hom challenges physical] at reduced
  exact reduced

theorem write_output_tokens {R : Type} [CommRing R]
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R)
    (physical : GKRAddress → Source.BaseField) (values : GKRAddress → R)
    (baseLaw : ∀ address, Airbender.Compiler.FunctionalNative.UnifiedUncached.native.isBase address = true → values address = hom (physical address))
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.bank.address) = 0)
    (affine : ∀ definition ∈ Airbender.Compiler.FunctionalNative.UnifiedUncached.native.definitions, definition.Holds hom challenges values)
    (products : ∀ gate ∈ Airbender.Compiler.ProductNative.UnifiedUncached.native.gates, gate.Holds hom challenges values) :
    values Airbender.Compiler.MemoryNative.UnifiedUncached.native.initializationWriteOutput =
      (((List.finRange 2).map (fun set => sourceBoundaryToken (Airbender.Compiler.MemoryNative.UnifiedUncached.native.sourceValues physical) .initial set.val 512)).map
        (memoryTokenFingerprint hom challenges)).prod := by
  let assignment : TypedAssignment R := ⟨physical, values⟩
  have typedEq : assignment.value Airbender.Compiler.ConsumerNative.UnifiedUncached.native.typing hom = values := TypedAssignment.value_eq assignment Airbender.Compiler.ConsumerNative.UnifiedUncached.native.typing hom baseLaw
  have defined : ∀ definition ∈ Airbender.Compiler.MemoryNative.UnifiedUncached.native.definitions, definition.Holds hom challenges (assignment.value Airbender.Compiler.ConsumerNative.UnifiedUncached.native.typing hom) := by
    rw [typedEq, ← Airbender.Compiler.FunctionalLinksNative.UnifiedUncached.native.memoryDefinitionsAgree]
    exact affine
  have holds := products
  rw [← typedEq] at holds
  have reduced := Airbender.Compiler.MemoryNative.UnifiedUncached.native.initializationWriteSourceReduction hom challenges assignment defined (Airbender.Compiler.FunctionalLinksNative.UnifiedUncached.native.memoryCopies physical arithmetic) holds
  rw [typedEq] at reduced
  change values Airbender.Compiler.MemoryNative.UnifiedUncached.native.initializationWriteOutput =
    (Airbender.Compiler.MemoryNative.UnifiedUncached.native.initializationWriteRows.map (fun row => row.fingerprint (Airbender.Compiler.MemoryNative.UnifiedUncached.native.sourceValues physical) hom challenges)).prod at reduced
  rw [write_products_from_base hom challenges physical] at reduced
  exact reduced

theorem read_output_public {R : Type} [CommRing R]
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R)
    (physical : GKRAddress → Source.BaseField) (values : GKRAddress → R)
    (parameters : Initialization.Parameters babyBearModulus Source.BaseField)
    (row : Fin 8388608) (window : Nat) (windowBound : window + 1 < 128)
    (windows : ∀ set : Fin 2, parameters.windows set.val = window + set.val)
    (low : (Airbender.Compiler.MemoryNative.UnifiedUncached.native.sourceValues physical).initializationAddress 0 = (Initialization.addressLo row.val : Source.BaseField))
    (high : (Airbender.Compiler.MemoryNative.UnifiedUncached.native.sourceValues physical).initializationAddress 1 = (row.val / 16384 + window * 512 : Nat))
    (baseLaw : ∀ address, Airbender.Compiler.FunctionalNative.UnifiedUncached.native.isBase address = true → values address = hom (physical address))
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.bank.address) = 0)
    (affine : ∀ definition ∈ Airbender.Compiler.FunctionalNative.UnifiedUncached.native.definitions, definition.Holds hom challenges values)
    (products : ∀ gate ∈ Airbender.Compiler.ProductNative.UnifiedUncached.native.gates, gate.Holds hom challenges values) :
    values Airbender.Compiler.MemoryNative.UnifiedUncached.native.initializationReadOutput =
      ((Initialization.unified.layout.leaves .terminal).map (fun leaf =>
        memoryTokenFingerprint hom challenges (leaf.token Initialization.unified.layout parameters
          (fun _ column => physical (.BaseLayerMemory column)) row.val))).prod := by
  rw [read_output_tokens hom challenges physical values baseLaw arithmetic affine products]
  have identity : (List.finRange 2).map (fun set => sourceBoundaryToken (Airbender.Compiler.MemoryNative.UnifiedUncached.native.sourceValues physical) .terminal set.val 512) =
      (Initialization.unified.layout.leaves .terminal).map (fun leaf => leaf.token Initialization.unified.layout parameters
        (fun _ column => physical (.BaseLayerMemory column)) row.val) := by
    simp only [Initialization.Layout.leaves, List.map_map]
    change _ = (List.finRange 2).map _
    apply List.map_congr_left
    intro set member
    exact public_leaf physical parameters row window windowBound windows low high .terminal set
  rw [identity]
  simp only [List.map_map, Function.comp_def]

theorem write_output_public {R : Type} [CommRing R]
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R)
    (physical : GKRAddress → Source.BaseField) (values : GKRAddress → R)
    (parameters : Initialization.Parameters babyBearModulus Source.BaseField)
    (row : Fin 8388608) (window : Nat) (windowBound : window + 1 < 128)
    (windows : ∀ set : Fin 2, parameters.windows set.val = window + set.val)
    (low : (Airbender.Compiler.MemoryNative.UnifiedUncached.native.sourceValues physical).initializationAddress 0 = (Initialization.addressLo row.val : Source.BaseField))
    (high : (Airbender.Compiler.MemoryNative.UnifiedUncached.native.sourceValues physical).initializationAddress 1 = (row.val / 16384 + window * 512 : Nat))
    (baseLaw : ∀ address, Airbender.Compiler.FunctionalNative.UnifiedUncached.native.isBase address = true → values address = hom (physical address))
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.bank.address) = 0)
    (affine : ∀ definition ∈ Airbender.Compiler.FunctionalNative.UnifiedUncached.native.definitions, definition.Holds hom challenges values)
    (products : ∀ gate ∈ Airbender.Compiler.ProductNative.UnifiedUncached.native.gates, gate.Holds hom challenges values) :
    values Airbender.Compiler.MemoryNative.UnifiedUncached.native.initializationWriteOutput =
      ((Initialization.unified.layout.leaves .initial).map (fun leaf =>
        memoryTokenFingerprint hom challenges (leaf.token Initialization.unified.layout parameters
          (fun _ column => physical (.BaseLayerMemory column)) row.val))).prod := by
  rw [write_output_tokens hom challenges physical values baseLaw arithmetic affine products]
  have identity : (List.finRange 2).map (fun set => sourceBoundaryToken (Airbender.Compiler.MemoryNative.UnifiedUncached.native.sourceValues physical) .initial set.val 512) =
      (Initialization.unified.layout.leaves .initial).map (fun leaf => leaf.token Initialization.unified.layout parameters
        (fun _ column => physical (.BaseLayerMemory column)) row.val) := by
    simp only [Initialization.Layout.leaves, List.map_map]
    change _ = (List.finRange 2).map _
    apply List.map_congr_left
    intro set member
    exact public_leaf physical parameters row window windowBound windows low high .initial set
  rw [identity]
  simp only [List.map_map, Function.comp_def]

end Airbender.Compiler.InitializationPortsNative.UnifiedUncached
