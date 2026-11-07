import Airbender.Proofs.GKRCompiler.WiringNative.AddSubCached

namespace Tests.GKRCompilerWiring
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

private noncomputable def original : Wiring :=
  Airbender.Compiler.WiringNative.AddSubCached.native.graph

private noncomputable def wrongLayer : GatePorts :=
  { Airbender.Compiler.WiringNative.AddSubCached.native.gate0 with layer := 99 }

theorem rejects_wrong_layer : original.gateValid wrongLayer = false := by decide +kernel

theorem rejects_out_of_bounds_memory :
    original.inputValid 0 (.BaseLayerMemory original.memoryWidth) = false := by decide +kernel

private noncomputable def wrongCache : CachePorts :=
  { Airbender.Compiler.WiringNative.AddSubCached.native.cache0 with layer := 1 }

theorem rejects_wrong_cache_layer : original.cacheValid wrongCache = false := by decide +kernel

private noncomputable def duplicateProducer : Wiring :=
  { original with producerPorts := original.produced.get ⟨0, by decide⟩ :: original.produced }

theorem rejects_duplicate_producer : duplicateProducer.uniqueValid = false := by decide +kernel

private noncomputable def duplicatePlacement : Wiring :=
  { original with placement := original.placement.get ⟨0, by decide⟩ :: original.placement }

theorem rejects_duplicate_source_placement :
    duplicatePlacement.placementCase ⟨0, by decide⟩ = false := by decide +kernel

private noncomputable def danglingOutput : Wiring :=
  { original with globalOutputs := .InnerLayer 99 0 :: original.globalOutputs }

theorem rejects_dangling_output : danglingOutput.outputsValid = false := by decide +kernel

private noncomputable def staleProducerTable : Wiring :=
  { original with producerPorts := original.produced.tail }

theorem rejects_stale_producer_table :
    decide (staleProducerTable.produced = staleProducerTable.computedProduced) = false := by decide +kernel

end Tests.GKRCompilerWiring
