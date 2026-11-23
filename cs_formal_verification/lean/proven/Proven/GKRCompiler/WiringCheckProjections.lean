module
import all Mathlib.Data.List.Sort
public import Proven.GKRCompiler.WiringChecks

@[expose] public section
set_option warningAsError true

namespace Airbender.Compiler.WiringChecks

structure Facts (graph : Wiring) : Prop where
  nonempty : decide (graph.widths ≠ []) = true
  producerTable : decide (graph.produced = graph.computedProduced) = true
  unique : graph.uniqueValid = true
  gates : graph.gates.all graph.gateValid = true
  caches : graph.caches.all graph.cacheValid = true
  placement : graph.placementValid = true
  scratch : graph.scratchValid = true
  outputs : graph.outputsValid = true

theorem facts (graph : Wiring) (checked : graph.check = true) : Facts graph := by
  simp only [Wiring.check, Bool.and_eq_true] at checked
  rcases checked with ⟨⟨⟨⟨⟨⟨⟨nonempty, table⟩, unique⟩, gates⟩, caches⟩, placement⟩, scratch⟩, outputs⟩
  exact ⟨nonempty, table, unique, gates, caches, placement, scratch, outputs⟩

theorem unique_at (graph : Wiring) (checked : graph.check = true) (index : Fin graph.produced.length) :
    distinctAt graph.produced index = true :=
  List.all_eq_true.mp (facts graph checked).unique index (List.mem_finRange index)

theorem placement_at (graph : Wiring) (checked : graph.check = true) (index : Fin graph.placement.length) :
    graph.placementCase index = true :=
  List.all_eq_true.mp (facts graph checked).placement index (List.mem_finRange index)

theorem gate_at (graph : Wiring) (checked : graph.check = true) (index : Fin graph.gates.length) :
    graph.gateValid (graph.gates.get index) = true :=
  List.all_eq_true.mp (facts graph checked).gates _ (List.get_mem _ _)

theorem cache_at (graph : Wiring) (checked : graph.check = true) (index : Fin graph.caches.length) :
    graph.cacheValid (graph.caches.get index) = true :=
  List.all_eq_true.mp (facts graph checked).caches _ (List.get_mem _ _)

end Airbender.Compiler.WiringChecks
