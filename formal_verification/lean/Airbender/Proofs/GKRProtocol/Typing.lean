import Airbender.Proofs.GKRCompiler.Wiring
import Airbender.Proofs.GKRCompiler.Certificate

namespace Airbender.Compiler
set_option warningAsError true

inductive WireKind where
  | base
  | extension
  deriving Repr, DecidableEq, BEq

instance : LawfulBEq WireKind where
  eq_of_beq := by
    intro left right checked
    cases left <;> cases right <;> first | rfl | cases checked
  rfl := by intro kind; cases kind <;> rfl

abbrev TypedPort := GKRAddress × WireKind

/-- The field roles consumed by the native helper for one actual gate/cache.
The untyped port lists refer to the separately checked actual wiring data. -/
structure ConsumerNode where
  rawInputs : List GKRAddress
  rawOutputs : List GKRAddress
  inputs : List TypedPort
  outputs : List TypedPort
  /-- Inputs flattened by native helpers that assert unique addresses. -/
  distinctGroups : List (List GKRAddress)

structure ConsumerTyping where
  graph : Wiring
  declarations : List TypedPort
  nodes : List ConsumerNode

def ConsumerTyping.consumersValid (typing : ConsumerTyping) : Bool :=
  decide (typing.nodes.map (fun node => (node.rawInputs, node.rawOutputs)) =
    typing.graph.gates.map (fun gate => (gate.inputs, gate.outputs)) ++
      typing.graph.caches.map (fun cache => (cache.inputs, [cache.output])))

def ConsumerTyping.compatible (typing : ConsumerTyping) (port : TypedPort) : Bool :=
  match port.1 with
  | .BaseLayerWitness _ | .BaseLayerMemory _ | .Setup _ | .VirtualSetup _ => port.2 == .base
  | .InnerLayer _ _ | .Cached _ _ => typing.declarations.contains port
  | .ScratchSpace _ => false

def ConsumerTyping.nodeValid (typing : ConsumerTyping) (node : ConsumerNode) : Bool :=
  decide (node.inputs.map Prod.fst = node.rawInputs) &&
    decide (node.outputs.map Prod.fst = node.rawOutputs) &&
    node.inputs.all typing.compatible && node.outputs.all typing.compatible &&
    node.distinctGroups.all distinct

def ConsumerTyping.sourceValid (typing : ConsumerTyping) : Bool :=
  typing.graph.placement.all (fun slot => typing.compatible (slot.1, .base)) &&
    typing.graph.scratch.all (fun slot => typing.compatible (slot.1, .base))

def ConsumerTyping.outputsValid (typing : ConsumerTyping) : Bool :=
  typing.graph.globalOutputs.all (fun address => typing.compatible (address, .extension))

def ConsumerTyping.check (typing : ConsumerTyping) : Bool :=
  decide (typing.declarations.map Prod.fst = typing.graph.produced) &&
    decide (typing.nodes.flatMap ConsumerNode.outputs = typing.declarations) &&
    typing.consumersValid && typing.nodes.all typing.nodeValid && typing.sourceValid && typing.outputsValid

def ConsumerTyping.Valid (typing : ConsumerTyping) : Prop :=
  typing.graph.Valid ∧
    typing.declarations.map Prod.fst = typing.graph.produced ∧
    typing.nodes.flatMap ConsumerNode.outputs = typing.declarations ∧
    typing.consumersValid = true ∧
    (∀ node ∈ typing.nodes, typing.nodeValid node = true) ∧
    typing.sourceValid = true ∧ typing.outputsValid = true

theorem ConsumerTyping.assemble {typing : ConsumerTyping}
    (ports : decide (typing.declarations.map Prod.fst = typing.graph.produced) = true)
    (declarations : decide (typing.nodes.flatMap ConsumerNode.outputs = typing.declarations) = true)
    (consumers : typing.consumersValid = true)
    (nodes : typing.nodes.all typing.nodeValid = true)
    (sources : typing.sourceValid = true) (outputs : typing.outputsValid = true) :
    typing.check = true := by
  simp only [check, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨ports, declarations⟩, consumers⟩, nodes⟩, sources⟩, outputs⟩

theorem ConsumerTyping.sound {typing : ConsumerTyping}
    (wiring : typing.graph.Valid) (checked : typing.check = true) : typing.Valid := by
  refine ⟨wiring, ?_⟩
  simpa only [check, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, and_assoc] using checked

/-- Every actual intermediate/cache address has one declared field role;
changing base/extension helper selection cannot be hidden by port aliasing. -/
theorem ConsumerTyping.unique_roles {typing : ConsumerTyping} (valid : typing.Valid) :
    (typing.declarations.map Prod.fst).Nodup := by
  rw [valid.2.1]
  exact valid.1.2.2.1

end Airbender.Compiler
