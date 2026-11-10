import Airbender.Import.Schema
import Mathlib.Data.List.Count

namespace Airbender.Compiler
set_option warningAsError true

/-- Structural Boolean equality keeps large port-bank checks from constructing
the proof objects carried by the generic DecidableEq-based BEq instance. -/
def addressEqual : GKRAddress → GKRAddress → Bool
  | .BaseLayerWitness a, .BaseLayerWitness b
  | .BaseLayerMemory a, .BaseLayerMemory b
  | .Setup a, .Setup b
  | .ScratchSpace a, .ScratchSpace b => a == b
  | .InnerLayer a b, .InnerLayer c d
  | .Cached a b, .Cached c d => a == c && b == d
  | .VirtualSetup a, .VirtualSetup b => decide (a = b)
  | _, _ => false

theorem addressEqual_iff (left right : GKRAddress) :
    addressEqual left right = true ↔ left = right := by
  cases left <;> cases right <;> simp [addressEqual, Bool.and_eq_true]

instance gkrAddressBEq : BEq GKRAddress := ⟨addressEqual⟩

instance gkrAddressLawfulBEq : LawfulBEq GKRAddress where
  eq_of_beq := by
    intro left right checked
    exact (addressEqual_iff left right).mp checked
  rfl := by
    intro address
    exact (addressEqual_iff address address).mpr rfl

/-- Boolean duplicate checking avoids constructing discarded decidability
proofs for every suffix of a large native address table. -/
def distinct [BEq α] : List α → Bool
  | [] => true
  | first :: rest => !rest.contains first && distinct rest

theorem distinct_iff [BEq α] [LawfulBEq α] (items : List α) :
    distinct items = true ↔ items.Nodup := by
  induction items with
  | nil => simp [distinct]
  | cons first rest ih => simp [distinct, List.nodup_cons, ih]

def distinctAt [BEq α] (items : List α) (index : Fin items.length) : Bool :=
  !(items.drop (index.val + 1)).contains (items.get index)

theorem distinctAt_sound [BEq α] [LawfulBEq α] {items : List α}
    (checks : ∀ index, distinctAt items index = true) : items.Nodup := by
  induction items with
  | nil => simp
  | cons first rest ih =>
    have absent : first ∉ rest := by
      simpa [distinctAt] using checks ⟨0, by simp⟩
    apply List.nodup_cons.mpr
    refine ⟨absent, ih ?_⟩
    intro index
    have checked := checks ⟨index.val + 1, by simp⟩
    simpa [distinctAt, Nat.add_assoc] using checked

/-- Ports extracted from every actual relation, including cache-only inputs. -/
structure GatePorts where
  layer : Nat
  inputs : List GKRAddress
  outputs : List GKRAddress
  deriving Repr, DecidableEq

structure CachePorts where
  layer : Nat
  inputs : List GKRAddress
  output : GKRAddress
  deriving Repr, DecidableEq

structure Wiring where
  memoryWidth : Nat
  witnessWidth : Nat
  setupWidth : Nat
  /-- Widths of layers 1 through the final output layer. -/
  widths : List Nat
  gates : List GatePorts
  caches : List CachePorts
  /-- A separately shared address table; its equality to actual producer ports
  is checked before it can be used by the per-input checks. -/
  producerPorts : List GKRAddress
  /-- The actual address and original requested layer of every source variable. -/
  placement : List (GKRAddress × Nat)
  scratchSize : Nat
  scratch : List (GKRAddress × Nat)
  scratchReverse : List (Nat × GKRAddress)
  globalOutputs : List GKRAddress
  cached : Bool
  deriving Repr, DecidableEq

def addressLayer : GKRAddress → Nat
  | .InnerLayer layer _ | .Cached layer _ => layer
  | _ => 0

def Wiring.addressBound (graph : Wiring) : GKRAddress → Bool
  | .BaseLayerMemory offset => decide (offset < graph.memoryWidth)
  | .BaseLayerWitness offset => decide (offset < graph.witnessWidth)
  | .Setup offset => decide (offset < graph.setupWidth)
  | .VirtualSetup _ => true
  | .InnerLayer layer offset =>
      decide (0 < layer) && decide (offset < (graph.widths[layer - 1]?).getD 0)
  | .Cached layer offset => graph.cached && decide (layer < graph.widths.length) &&
      decide (offset < (graph.caches.filter (fun cache => cache.layer == layer)).length)
  | .ScratchSpace _ => false

def Wiring.computedProduced (graph : Wiring) : List GKRAddress :=
  graph.gates.flatMap GatePorts.outputs ++ graph.caches.map CachePorts.output

def Wiring.produced (graph : Wiring) : List GKRAddress := graph.producerPorts

def Wiring.uniqueValid (graph : Wiring) : Bool :=
  (List.finRange graph.produced.length).all (distinctAt graph.produced)

theorem Wiring.unique_sound {graph : Wiring} (checked : graph.uniqueValid = true) :
    graph.produced.Nodup :=
  distinctAt_sound (fun index => List.all_eq_true.mp checked index (List.mem_finRange index))

def Wiring.inputValid (graph : Wiring) (layer : Nat) (address : GKRAddress) : Bool :=
  graph.addressBound address && decide (addressLayer address = layer) &&
    match address with
    | .InnerLayer _ _ | .Cached _ _ => decide (graph.produced.count address = 1)
    | .ScratchSpace _ => false
    | _ => true

def Wiring.gateValid (graph : Wiring) (gate : GatePorts) : Bool :=
  decide (0 < gate.layer ∧ gate.layer ≤ graph.widths.length) &&
    gate.inputs.all (graph.inputValid (gate.layer - 1)) &&
    gate.outputs.all (fun address =>
      match address with
      | .InnerLayer layer _ => decide (layer = gate.layer) && graph.addressBound address &&
          (if gate.layer == graph.widths.length then graph.globalOutputs.contains address else true)
      | _ => false)

def Wiring.cacheValid (graph : Wiring) (cache : CachePorts) : Bool :=
  cache.inputs.all (fun address =>
    match address with
    | .Cached _ _ => false
    | _ => graph.inputValid cache.layer address) &&
    match cache.output with
    | .Cached layer _ => decide (layer = cache.layer) && graph.addressBound cache.output
    | _ => false

def Wiring.placementCase (graph : Wiring) (index : Fin graph.placement.length) : Bool :=
  distinctAt (graph.placement.map Prod.fst) ⟨index.val, by simp⟩ &&
    (let (address, layer) := graph.placement.get index
      match address with
      | .BaseLayerMemory _ | .BaseLayerWitness _ | .InnerLayer _ _ =>
          graph.inputValid layer address
      | _ => false)

def Wiring.placementValid (graph : Wiring) : Bool :=
  (List.finRange graph.placement.length).all graph.placementCase

def Wiring.scratchValid (graph : Wiring) : Bool :=
  decide (graph.scratch.length = graph.scratchSize) &&
    distinct (graph.scratch.map Prod.fst) &&
    distinct (graph.scratch.map Prod.snd) &&
    decide (graph.scratchReverse.length = graph.scratchSize) &&
    graph.scratch.all (fun (address, index) =>
      decide (index < graph.scratchSize) &&
      decide ((index, address) ∈ graph.scratchReverse) &&
      match address with
      | .InnerLayer layer _ => graph.inputValid layer address
      | _ => false)

def Wiring.outputsValid (graph : Wiring) : Bool :=
  decide (graph.globalOutputs ≠ []) && distinct graph.globalOutputs &&
    graph.globalOutputs.all (graph.inputValid graph.widths.length)

def Wiring.check (graph : Wiring) : Bool :=
  decide (graph.widths ≠ []) && decide (graph.produced = graph.computedProduced) && graph.uniqueValid &&
    graph.gates.all graph.gateValid && graph.caches.all graph.cacheValid &&
    graph.placementValid && graph.scratchValid && graph.outputsValid

theorem Wiring.assemble {graph : Wiring}
    (nonempty : decide (graph.widths ≠ []) = true)
    (producerTable : decide (graph.produced = graph.computedProduced) = true)
    (unique : graph.uniqueValid = true)
    (gates : graph.gates.all graph.gateValid = true)
    (caches : graph.caches.all graph.cacheValid = true)
    (placement : graph.placementValid = true)
    (scratch : graph.scratchValid = true)
    (outputs : graph.outputsValid = true) : graph.check = true := by
  simp only [check, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨nonempty, producerTable⟩, unique⟩, gates⟩, caches⟩, placement⟩, scratch⟩, outputs⟩

def Wiring.Valid (graph : Wiring) : Prop :=
    graph.widths ≠ [] ∧ graph.produced = graph.computedProduced ∧ graph.produced.Nodup ∧
    (∀ gate ∈ graph.gates, graph.gateValid gate = true) ∧
    (∀ cache ∈ graph.caches, graph.cacheValid cache = true) ∧
    graph.placementValid = true ∧ graph.scratchValid = true ∧ graph.outputsValid = true

/-- The extracted graph has unique producers, bounded adjacent-layer inputs,
bounded outputs, checked cache dependencies, injective original placements,
a complete scratch bijection, and exactly its declared final output ports. -/
theorem Wiring.sound {graph : Wiring} (checked : graph.check = true) : graph.Valid := by
  have components : graph.widths ≠ [] ∧ graph.produced = graph.computedProduced ∧
      graph.uniqueValid = true ∧
      (∀ gate ∈ graph.gates, graph.gateValid gate = true) ∧
      (∀ cache ∈ graph.caches, graph.cacheValid cache = true) ∧
      graph.placementValid = true ∧ graph.scratchValid = true ∧ graph.outputsValid = true := by
    simpa only [check, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
      and_assoc] using checked
  exact ⟨components.1, components.2.1, unique_sound components.2.2.1, components.2.2.2⟩

/-- A read from an intermediate or cached address identifies exactly one
producer. This is checked independently of any arithmetic identity. -/
theorem Wiring.unique_input {graph : Wiring} {layer : Nat} {address : GKRAddress}
    (checked : graph.inputValid layer address = true)
    (intermediate : (∃ l o, address = .InnerLayer l o) ∨ (∃ l o, address = .Cached l o)) :
    graph.produced.count address = 1 := by
  rcases intermediate with ⟨l, o, rfl⟩ | ⟨l, o, rfl⟩ <;>
    simp only [inputValid, Bool.and_eq_true, decide_eq_true_eq, and_assoc] at checked <;>
    exact checked.2.2

end Airbender.Compiler
