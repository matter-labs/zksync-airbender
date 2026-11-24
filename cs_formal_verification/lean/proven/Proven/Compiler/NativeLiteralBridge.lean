module
public import Proven.Compiler.NativeBridge

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.NativeBridge
open NativeArithmetic

/-- Transport a native cache equation through its literal entry certificate. -/
theorem cache_at_literal {circuit : Circuit} {physical : GKRAddress → F}
    (accepted : Holds circuit physical) (layer : Fin circuit.layers.size)
    (index : Fin circuit.layers[layer].cached_relations.size)
    (entry : GKRAddress × GKRCacheRelation)
    (selected : circuit.layers[layer].cached_relations[index.val]'index.isLt = entry) :
    (Clause.cache entry.1 entry.2).residual physical = 0 := by
  have result := cache_at accepted layer index
  change (Clause.cache (circuit.layers[layer].cached_relations[index.val]'index.isLt).1
    (circuit.layers[layer].cached_relations[index.val]'index.isLt).2).residual physical = 0 at result
  rw [selected] at result
  exact result

/-- Transport a native gate equation through its literal entry certificate. -/
theorem gate_at_literal {circuit : Circuit} {physical : GKRAddress → F}
    (accepted : Holds circuit physical) (layer : Fin circuit.layers.size)
    (index : Fin (circuit.layers[layer].gates ++ circuit.layers[layer].gates_with_external_connections).size)
    (entry : GateArtifacts)
    (selected : (circuit.layers[layer].gates ++
      circuit.layers[layer].gates_with_external_connections)[index.val]'index.isLt = entry) :
    (Clause.gate entry.enforced_relation).residual physical = 0 := by
  have result := gate_at accepted layer index
  change (Clause.gate ((circuit.layers[layer].gates ++
    circuit.layers[layer].gates_with_external_connections)[index.val]'index.isLt).enforced_relation).residual
      physical = 0 at result
  rw [selected] at result
  exact result

end Airbender.Compiler.NativeBridge
