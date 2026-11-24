module
import all Mathlib.Data.List.Sort
public import Proven.GKRProtocol.CleanPlacementChecks
public import Proven.GKRCompiler.WiringKeySort

@[expose] public section
set_option warningAsError true

namespace Airbender.Compiler.WiringChecks

inductive KeyTree where
  | empty
  | node (left : KeyTree) (key : Nat) (right : KeyTree)

def KeyTree.toList : KeyTree → List Nat
  | .empty => []
  | .node left key right => left.toList ++ key :: right.toList

def KeyTree.contains : KeyTree → Nat → Bool
  | .empty, _ => false
  | .node left key right, query =>
      if query == key then true else if query < key then left.contains query else right.contains query

theorem KeyTree.contains_sound (tree : KeyTree) (query : Nat)
    (checked : tree.contains query = true) : query ∈ tree.toList := by
  induction tree with
  | empty => simp [contains] at checked
  | node left key right leftIH rightIH =>
      simp only [contains] at checked
      split at checked
      · rename_i same
        have same : query = key := by simpa using same
        subst query
        simp [toList]
      · split at checked
        · exact List.mem_append_left _ (leftIH checked)
        · exact List.mem_append_right _ (List.mem_cons_of_mem _ (rightIH checked))

structure Capture where
  producers : KeyTree
  placements : KeyTree

structure Bindings (graph : Wiring) (data : Capture) : Prop where
  producers : data.producers.toList =
    KeySort.sort (graph.produced.map AddressUniqueChecks.addressCode)
  placements : data.placements.toList =
    KeySort.sort (graph.placement.map (fun entry => AddressUniqueChecks.addressCode entry.1))

def inputCheck (graph : Wiring) (data : Capture) (layer : Nat) (address : GKRAddress) : Bool :=
  graph.addressBound address && decide (addressLayer address = layer) &&
    match address with
    | .InnerLayer _ _ | .Cached _ _ => data.producers.contains (AddressUniqueChecks.addressCode address)
    | .ScratchSpace _ => false
    | _ => true

def gateCheck (graph : Wiring) (data : Capture) (gate : GatePorts) : Bool :=
  decide (0 < gate.layer ∧ gate.layer ≤ graph.widths.length) &&
    gate.inputs.all (inputCheck graph data (gate.layer - 1)) &&
    gate.outputs.all (fun address =>
      match address with
      | .InnerLayer layer _ => decide (layer = gate.layer) && graph.addressBound address &&
          (if gate.layer == graph.widths.length then graph.globalOutputs.contains address else true)
      | _ => false)

def cacheCheck (graph : Wiring) (data : Capture) (cache : CachePorts) : Bool :=
  cache.inputs.all (fun address =>
    match address with
    | .Cached _ _ => false
    | _ => inputCheck graph data cache.layer address) &&
    match cache.output with
    | .Cached layer _ => decide (layer = cache.layer) && graph.addressBound cache.output
    | _ => false

def placementCheck (graph : Wiring) (data : Capture) (entry : GKRAddress × Nat) : Bool :=
  match entry.1 with
  | .BaseLayerMemory _ | .BaseLayerWitness _ | .InnerLayer _ _ => inputCheck graph data entry.2 entry.1
  | _ => false

def check (graph : Wiring) (data : Capture) : Bool :=
  decide (graph.widths ≠ []) && (graph.produced == graph.computedProduced) &&
    AddressUniqueChecks.ascending data.producers.toList &&
    AddressUniqueChecks.ascending data.placements.toList &&
    graph.gates.all (gateCheck graph data) && graph.caches.all (cacheCheck graph data) &&
    graph.placement.all (placementCheck graph data) && graph.scratchValid && graph.outputsValid

theorem producers_unique (graph : Wiring) (data : Capture) (binding : Bindings graph data)
    (checked : AddressUniqueChecks.ascending data.producers.toList = true) : graph.produced.Nodup := by
  have unique := AddressUniqueChecks.ascending_sound _ checked
  rw [binding.producers] at unique
  exact List.Nodup.of_map AddressUniqueChecks.addressCode ((KeySort.sort_perm _).nodup_iff.mp unique)

theorem producer_mem (graph : Wiring) (data : Capture) (binding : Bindings graph data)
    (address : GKRAddress) (checked : data.producers.contains (AddressUniqueChecks.addressCode address) = true) :
    address ∈ graph.produced := by
  have member := KeyTree.contains_sound _ _ checked
  rw [binding.producers] at member
  have original := (KeySort.sort_perm _).mem_iff.mp member
  rcases List.mem_map.mp original with ⟨actual, included, same⟩
  exact CleanPlacementChecks.addressCode_injective same ▸ included

theorem inputCheck_sound (graph : Wiring) (data : Capture) (binding : Bindings graph data)
    (unique : graph.produced.Nodup) (layer : Nat) (address : GKRAddress)
    (checked : inputCheck graph data layer address = true) : graph.inputValid layer address = true := by
  cases address <;> simp only [inputCheck, Wiring.inputValid, Bool.and_eq_true] at checked ⊢
  all_goals try exact checked
  all_goals
    refine ⟨checked.1, ?_⟩
    exact decide_eq_true (List.count_eq_one_of_mem unique (producer_mem graph data binding _ checked.2))

theorem all_imp (items : List α) (left right : α → Bool)
    (implication : ∀ item, left item = true → right item = true)
    (checked : items.all left = true) : items.all right = true := by
  exact List.all_eq_true.mpr fun item member => implication item (List.all_eq_true.mp checked item member)

theorem gateCheck_sound (graph : Wiring) (data : Capture) (binding : Bindings graph data)
    (unique : graph.produced.Nodup) (gate : GatePorts) (checked : gateCheck graph data gate = true) :
    graph.gateValid gate = true := by
  simp only [gateCheck, Wiring.gateValid, Bool.and_eq_true] at checked ⊢
  exact ⟨⟨checked.1.1, all_imp _ _ _ (inputCheck_sound graph data binding unique _) checked.1.2⟩, checked.2⟩

theorem cacheCheck_sound (graph : Wiring) (data : Capture) (binding : Bindings graph data)
    (unique : graph.produced.Nodup) (cache : CachePorts) (checked : cacheCheck graph data cache = true) :
    graph.cacheValid cache = true := by
  simp only [cacheCheck, Wiring.cacheValid, Bool.and_eq_true] at checked ⊢
  refine ⟨all_imp _ _ _ ?_ checked.1, checked.2⟩
  intro address checked
  cases address <;> simp only at checked ⊢
  all_goals try exact checked
  all_goals exact inputCheck_sound graph data binding unique _ _ checked

theorem placements_unique (graph : Wiring) (data : Capture) (binding : Bindings graph data)
    (checked : AddressUniqueChecks.ascending data.placements.toList = true) : (graph.placement.map Prod.fst).Nodup := by
  have unique := AddressUniqueChecks.ascending_sound _ checked
  rw [binding.placements] at unique
  have original := (KeySort.sort_perm _).nodup_iff.mp unique
  apply List.Nodup.of_map AddressUniqueChecks.addressCode
  simpa only [List.map_map, Function.comp_def] using original

theorem placementCheck_sound (graph : Wiring) (data : Capture) (binding : Bindings graph data)
    (unique : graph.produced.Nodup) (placements : (graph.placement.map Prod.fst).Nodup)
    (checked : graph.placement.all (placementCheck graph data) = true) : graph.placementValid = true := by
  apply List.all_eq_true.mpr
  intro index _
  have row := List.all_eq_true.mp checked _ (List.get_mem graph.placement index)
  have distinct := AddressUniqueChecks.distinctAt_complete _ placements
    (⟨index.val, by simp⟩ : Fin (graph.placement.map Prod.fst).length)
  simp only [Wiring.placementCase, Bool.and_eq_true]
  refine ⟨distinct, ?_⟩
  cases entry : graph.placement.get index with
  | mk address layer =>
      rw [entry] at row
      cases address <;> simp only [placementCheck] at row ⊢
      all_goals try exact row
      all_goals exact inputCheck_sound graph data binding unique _ _ row

theorem check_sound (graph : Wiring) (data : Capture) (binding : Bindings graph data)
    (checked : check graph data = true) : graph.check = true := by
  simp only [check, Bool.and_eq_true] at checked
  rcases checked with ⟨⟨⟨⟨⟨⟨⟨⟨nonempty, table⟩, producers⟩, placements⟩, gates⟩, caches⟩, placement⟩, scratch⟩, outputs⟩
  have unique := producers_unique graph data binding producers
  apply Wiring.assemble nonempty (by simpa only [beq_iff_eq, decide_eq_true_eq] using table)
  · exact List.all_eq_true.mpr fun index _ => AddressUniqueChecks.distinctAt_complete _ unique index
  · exact all_imp _ _ _ (gateCheck_sound graph data binding unique) gates
  · exact all_imp _ _ _ (cacheCheck_sound graph data binding unique) caches
  · exact placementCheck_sound graph data binding unique (placements_unique graph data binding placements) placement
  · exact scratch
  · exact outputs

end Airbender.Compiler.WiringChecks
