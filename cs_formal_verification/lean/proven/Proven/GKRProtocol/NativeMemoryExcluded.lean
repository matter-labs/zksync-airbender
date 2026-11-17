module
import all Mathlib.Data.List.Sort
public import Proven.GKRProtocol.NativeMemoryBridge

@[expose] public section
set_option warningAsError true

/-! The initialization pair of the unified capture has its own interface. Its extension wires and their
copies form a closed subgraph. The RAM bridge reads them from the canonical evaluation and every other
extension wire from the supplied values. -/

namespace Airbender.Compiler.NativeMemoryBridge
open NativeArithmetic NativeMemory

/-- The output and the input wires of an affine definition. -/
def definitionAddresses (definition : AffineDefinition) : List GKRAddress :=
  definition.output :: definition.program.inputs

/-- The output wire of a product gate. -/
def productOutput : NativeProductGate → GKRAddress
  | .single output _ | .pair output _ _ | .mul output _ _ | .mask output _ _ | .copy output _ => output

/-- The output and the input wires of a product gate. -/
def productAddresses : NativeProductGate → List GKRAddress
  | .single output input => output :: input.inputs
  | .pair output left right => output :: (left.inputs ++ right.inputs)
  | .mul output left right => [output, left, right]
  | .mask output input predicate => [output, input, predicate]
  | .copy output input => [output, input]

/-- The initialization pair outputs and their extension copies, in native gate order. -/
def initializationWires (circuit : Circuit) : List GKRAddress :=
  (layerGates circuit).foldl (fun wires gate => match gate.enforced_relation with
    | .InitsOrTeardownsInitialPair _ _ output _ => output :: wires
    | .CopyInExtensionField input output => if wires.contains input then output :: wires else wires
    | _ => wires) []

/-- An excluded element reads only excluded or base wires. Any other element reads no excluded wire. -/
def separated (typing : ConsumerTyping) (excluded : List GKRAddress) (output : GKRAddress)
    (addresses : List GKRAddress) : Bool :=
  if excluded.contains output then addresses.all fun address => excluded.contains address || isBase typing address
  else addresses.all fun address => !excluded.contains address

/-- Excluded wires take the canonical values. Other wires take the supplied values. -/
def spliced (excluded : List GKRAddress) (canonical values : GKRAddress → R) (address : GKRAddress) : R :=
  if excluded.contains address then canonical address else values address

variable {R : Type} [CommRing R]

theorem interpret_congr (payload : LookupPayload) (hom : Source.BaseField →+* R) (cache : CacheChallenges R)
    (left right : GKRAddress → R) (same : ∀ address ∈ payload.inputs, left address = right address) :
    payload.interpret hom cache left = payload.interpret hom cache right := by
  unfold LookupPayload.interpret
  apply AffineProgram.value_congr
  simpa only [AffineProgram.mapCoefficients_inputs] using same

theorem definition_holds_congr (definition : AffineDefinition) (hom : Source.BaseField →+* R)
    (cache : CacheChallenges R) (left right : GKRAddress → R)
    (same : ∀ address ∈ definitionAddresses definition, left address = right address)
    (holds : definition.Holds hom cache left) : definition.Holds hom cache right := by
  unfold AffineDefinition.Holds at *
  rw [← same _ List.mem_cons_self, holds]
  exact interpret_congr _ _ _ _ _ fun address member => same address (List.mem_cons_of_mem _ member)

theorem product_holds_congr (gate : NativeProductGate) (hom : Source.BaseField →+* R)
    (cache : CacheChallenges R) (left right : GKRAddress → R)
    (same : ∀ address ∈ productAddresses gate, left address = right address)
    (holds : gate.Holds hom cache left) : gate.Holds hom cache right := by
  cases gate with
  | single output input =>
    simp only [NativeProductGate.Holds, productAddresses] at *
    rw [← same _ List.mem_cons_self, holds]
    exact interpret_congr _ _ _ _ _ fun address member => same address (List.mem_cons_of_mem _ member)
  | pair output first second =>
    simp only [NativeProductGate.Holds, productAddresses] at *
    rw [← same _ List.mem_cons_self, holds,
      interpret_congr first _ _ _ right fun address member =>
        same address (List.mem_cons_of_mem _ (List.mem_append_left _ member)),
      interpret_congr second _ _ _ right fun address member =>
        same address (List.mem_cons_of_mem _ (List.mem_append_right _ member))]
  | mul output first second =>
    simp only [NativeProductGate.Holds, productAddresses, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq] at *
    rw [← same.1, holds, same.2.1, same.2.2]
  | mask output input predicate =>
    simp only [NativeProductGate.Holds, productAddresses, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq] at *
    rw [← same.1, holds, same.2.1, same.2.2]
  | copy output input =>
    simp only [NativeProductGate.Holds, productAddresses, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq] at *
    rw [← same.1, holds, same.2]

section Excluded
variable (challenges : NativeMemory.Challenges R) (typing : ConsumerTyping) (physical : GKRAddress → F)
  (values canonical : GKRAddress → R) (excluded : List GKRAddress) {circuit : Circuit}

/-- The spliced wires agree with the canonical wires on excluded and base wires. -/
theorem spliced_canonical (canonicalBase : ∀ address, isBase typing address = true →
      canonical address = challenges.embed (physical address))
    (address : GKRAddress) (inside : excluded.contains address = true ∨ isBase typing address = true) :
    wires challenges typing physical (spliced excluded canonical values) address = canonical address := by
  cases base : isBase typing address with
  | true => rw [wires_base challenges typing physical _ base, canonicalBase address base]
  | false =>
    rw [wires_extension challenges typing physical _ base]
    simp only [base, Bool.false_eq_true, or_false] at inside
    simp only [spliced, inside, ↓reduceIte]

/-- The spliced wires agree with the supplied wires off the excluded wires. -/
theorem spliced_values (address : GKRAddress) (outside : excluded.contains address = false) :
    wires challenges typing physical (spliced excluded canonical values) address =
      wires challenges typing physical values address := by
  cases base : isBase typing address with
  | true => rw [wires_base challenges typing physical _ base, wires_base challenges typing physical _ base]
  | false =>
    rw [wires_extension challenges typing physical _ base, wires_extension challenges typing physical _ base]
    simp only [spliced, outside, Bool.false_eq_true, ↓reduceIte]

theorem gate_definition_excluded {relation : GKRRelation} {definition : AffineDefinition}
    (found : gateDefinition relation = some definition) (excludedGate : excludedRelation excluded relation = true) :
    excluded.contains definition.output = true := by
  cases relation <;> simp only [excludedRelation, Bool.false_eq_true] at excludedGate <;>
    simp only [gateDefinition, reduceCtorEq, Option.some.injEq] at found
  case CopyInExtensionField input output =>
    subst found
    exact excludedGate

theorem product_gate_excluded {caches : List GKRAddress} {relation : GKRRelation} {gate : NativeProductGate}
    (found : productGate circuit caches relation = some gate) (excludedGate : excludedRelation excluded relation = true) :
    excluded.contains (productOutput gate) = true := by
  cases relation <;> simp only [excludedRelation, Bool.false_eq_true] at excludedGate
  case CopyInExtensionField input output =>
    simp only [productGate] at found
    split at found <;> simp only [Option.some.injEq] at found <;> subst found <;> exact excludedGate
  case InitsOrTeardownsInitialPair state setup output sets =>
    obtain ⟨left, right, pair⟩ := fixed_two sets
    simp only [productGate, pair] at found
    cases leftPayload : initPayload circuit state setup left 0 <;>
      cases rightPayload : initPayload circuit state setup right 1 <;>
      simp only [leftPayload, rightPayload, Option.bind_eq_bind, Option.bind_none, Option.bind_some,
        reduceCtorEq, Option.some.injEq] at found
    subst found
    exact excludedGate

/-- Native base gates, the extension semantics and the canonical evaluation give every affine definition
    on the spliced wires. -/
theorem definitions_hold_spliced (typed : typingCheckedExcept typing circuit excluded = true)
    (partitioned : (definitionPrograms circuit).all
      (fun definition => separated typing excluded definition.output (definitionAddresses definition)) = true)
    (accepted : NativeArithmetic.Holds circuit physical)
    (extension : NativeMemory.Holds circuit challenges physical values)
    (canonicalBase : ∀ address, isBase typing address = true → canonical address = challenges.embed (physical address))
    (canonicalHolds : ∀ definition ∈ definitionPrograms circuit,
      definition.Holds challenges.memory.embed (cacheChallenges challenges) canonical) :
    ∀ definition ∈ definitionPrograms circuit, definition.Holds challenges.memory.embed
      (cacheChallenges challenges) (wires challenges typing physical (spliced excluded canonical values)) := by
  intro definition member
  have split := List.all_eq_true.mp partitioned definition member
  cases inside : excluded.contains definition.output with
  | true =>
    simp only [separated, inside, ↓reduceIte, List.all_eq_true, Bool.or_eq_true] at split
    exact definition_holds_congr definition _ _ canonical _
      (fun address used => (spliced_canonical challenges typing physical values canonical excluded canonicalBase
        address (split address used)).symm) (canonicalHolds definition member)
  | false =>
    simp only [separated, inside, Bool.false_eq_true, ↓reduceIte, List.all_eq_true, Bool.not_eq_true'] at split
    apply definition_holds_congr definition _ _ (wires challenges typing physical values)
    · intro address used
      exact (spliced_values challenges typing physical values canonical excluded address (split address used)).symm
    rcases List.mem_append.mp member with cache | gate
    · obtain ⟨entry, entryMember, found⟩ := List.mem_filterMap.mp cache
      obtain ⟨program, programFound, rfl⟩ := Option.map_eq_some_iff.mp found
      obtain ⟨layer, layerMember, entryInside⟩ := cache_member entryMember
      exact cache_definition_holds challenges typing physical values entry.1 entry.2 program programFound
        (typed_caches typing typed entry entryMember) ((accepted layer layerMember).1 entry entryInside)
        ((extension layer layerMember).1 entry entryInside)
    · obtain ⟨artifact, artifactMember, found⟩ := List.mem_filterMap.mp gate
      obtain ⟨layer, layerMember, artifactInside⟩ := gate_member artifactMember
      cases excludedGate : excludedRelation excluded artifact.enforced_relation with
      | true =>
        have contradiction := gate_definition_excluded excluded found excludedGate
        rw [inside] at contradiction
        cases contradiction
      | false =>
        have checked := typed_gates_except typing typed artifact artifactMember excludedGate
        exact gate_definition_holds challenges typing physical values artifact.enforced_relation definition found
          checked ((accepted layer layerMember).2 artifact artifactInside)
          ((extension layer layerMember).2 artifact artifactInside)

/-- The extension semantics and the canonical evaluation give every product gate on the spliced wires. -/
theorem products_hold_spliced (typed : typingCheckedExcept typing circuit excluded = true)
    (partitioned : (productGates circuit).all
      (fun gate => separated typing excluded (productOutput gate) (productAddresses gate)) = true)
    (extension : NativeMemory.Holds circuit challenges physical values)
    (canonicalBase : ∀ address, isBase typing address = true → canonical address = challenges.embed (physical address))
    (canonicalHolds : ∀ gate ∈ productGates circuit,
      gate.Holds challenges.memory.embed (cacheChallenges challenges) canonical) :
    ∀ gate ∈ productGates circuit, gate.Holds challenges.memory.embed
      (cacheChallenges challenges) (wires challenges typing physical (spliced excluded canonical values)) := by
  intro gate member
  have split := List.all_eq_true.mp partitioned gate member
  cases inside : excluded.contains (productOutput gate) with
  | true =>
    simp only [separated, inside, ↓reduceIte, List.all_eq_true, Bool.or_eq_true] at split
    exact product_holds_congr gate _ _ canonical _
      (fun address used => (spliced_canonical challenges typing physical values canonical excluded canonicalBase
        address (split address used)).symm) (canonicalHolds gate member)
  | false =>
    simp only [separated, inside, Bool.false_eq_true, ↓reduceIte, List.all_eq_true, Bool.not_eq_true'] at split
    apply product_holds_congr gate _ _ (wires challenges typing physical values)
    · intro address used
      exact (spliced_values challenges typing physical values canonical excluded address (split address used)).symm
    obtain ⟨artifact, artifactMember, found⟩ := List.mem_filterMap.mp member
    obtain ⟨layer, layerMember, artifactInside⟩ := gate_member artifactMember
    cases excludedGate : excludedRelation excluded artifact.enforced_relation with
    | true =>
      have contradiction := product_gate_excluded excluded found excludedGate
      rw [inside] at contradiction
      cases contradiction
    | false =>
      have checked := typed_gates_except typing typed artifact artifactMember excludedGate
      exact product_gate_holds challenges typing physical values circuit _ artifact.enforced_relation gate found
        checked ((extension layer layerMember).2 artifact artifactInside)

end Excluded

end Airbender.Compiler.NativeMemoryBridge
