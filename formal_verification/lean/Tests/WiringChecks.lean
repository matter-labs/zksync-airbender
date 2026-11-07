import Airbender.Proofs.GKRCompiler.WiringChecks

namespace Tests.WiringChecks
open Airbender.Compiler
open Airbender.Compiler.WiringChecks
set_option warningAsError true

def graph : Wiring := ⟨1, 1, 1, [1, 1],
  [⟨1, [.BaseLayerMemory 0], [.InnerLayer 1 0]⟩,
   ⟨2, [.InnerLayer 1 0], [.InnerLayer 2 0]⟩], [],
  [.InnerLayer 1 0, .InnerLayer 2 0],
  [(.BaseLayerMemory 0, 0), (.InnerLayer 1 0, 1)], 0, [], [], [.InnerLayer 2 0], false⟩

def capture : Capture := ⟨.node (.node .empty 8 .empty) 38 .empty,
  .node (.node .empty 2 .empty) 8 .empty⟩
theorem bindings : Bindings graph capture := ⟨rfl, rfl⟩
theorem checked : check graph capture = true := by decide +kernel
theorem original_checked : graph.check = true := check_sound graph capture bindings checked

def emptyProducers : Capture := {capture with producers := .empty}
def wrongKey : Capture := {capture with producers := .node (.node .empty 9 .empty) 38 .empty}
def duplicateKey : Capture := {capture with producers := .node (.node .empty 8 .empty) 8 .empty}
def duplicatePlacementKey : Capture := {capture with placements := .node (.node .empty 2 .empty) 2 .empty}
def wrongLayer : Wiring := {graph with gates := [⟨3, [.BaseLayerMemory 0], [.InnerLayer 1 0]⟩,
  ⟨2, [.InnerLayer 1 0], [.InnerLayer 2 0]⟩]}
def missingOutput : Wiring := {graph with globalOutputs := [.InnerLayer 2 1]}
def staleProducerTable : Wiring := {graph with producerPorts := [.InnerLayer 1 0]}

theorem empty_producers_rejected : check graph emptyProducers = false := by decide +kernel
theorem wrong_key_rejected : check graph wrongKey = false := by decide +kernel
theorem duplicate_key_rejected : check graph duplicateKey = false := by decide +kernel
theorem duplicate_placement_key_rejected : check graph duplicatePlacementKey = false := by decide +kernel
theorem wrong_layer_rejected : check wrongLayer capture = false := by decide +kernel
theorem missing_output_rejected : check missingOutput capture = false := by decide +kernel
theorem stale_producer_table_rejected : check staleProducerTable capture = false := by decide +kernel

def cachedGraph : Wiring := {graph with
  cached := true
  gates := [⟨1, [.Cached 0 0], [.InnerLayer 1 0]⟩, ⟨2, [.InnerLayer 1 0], [.InnerLayer 2 0]⟩]
  caches := [⟨0, [.BaseLayerMemory 0], .Cached 0 0⟩]
  producerPorts := [.InnerLayer 1 0, .InnerLayer 2 0, .Cached 0 0]}
def cachedCapture : Capture := {capture with producers := .node (.node .empty 8 .empty) 38 (.node .empty 42 .empty)}
theorem cached_bindings : Bindings cachedGraph cachedCapture := ⟨rfl, rfl⟩
theorem cached_checked : check cachedGraph cachedCapture = true := by decide +kernel
theorem cached_original : cachedGraph.check = true := check_sound cachedGraph cachedCapture cached_bindings cached_checked

def badCache : Wiring := {cachedGraph with caches := [⟨0, [.Cached 0 0], .Cached 0 0⟩]}
theorem cache_dependency_rejected : check badCache cachedCapture = false := by decide +kernel

end Tests.WiringChecks
