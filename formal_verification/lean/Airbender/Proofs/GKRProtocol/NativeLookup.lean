import Airbender.Proofs.GKRProtocol.LookupReduction
import Airbender.Proofs.GKRProtocol.CacheBindings

namespace Airbender.Compiler
set_option warningAsError true

inductive LookupWeight where
  | one
  | column : GKRAddress → LookupWeight
  | negativeMultiplicity : GKRAddress → LookupWeight

def LookupWeight.value [CommRing R] (values : GKRAddress → R) : LookupWeight → R
  | .one => 1
  | .column address => values address
  | .negativeMultiplicity address => -values address

abbrev LookupPayload := AffineProgram GKRAddress CacheCoefficient

def LookupPayload.interpret [CommRing R] (payload : LookupPayload)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (values : GKRAddress → R) : R :=
  (payload.mapCoefficients (CacheCoefficient.value hom challenges)).value values

structure NativeLookupLeaf where
  weight : LookupWeight
  payload : LookupPayload

def NativeLookupLeaf.isSetup (leaf : NativeLookupLeaf) : Bool :=
  match leaf.weight with
  | .negativeMultiplicity _ => true
  | .one | .column _ => false

def NativeLookupLeaf.value [CommRing R] (leaf : NativeLookupLeaf)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (values : GKRAddress → R) : RationalPair R :=
  RationalPair.leaf (leaf.weight.value values) (leaf.payload.interpret hom challenges values + gamma)

def NativeLookupLeaf.registryValue [CommRing R] (registry : List NativeLookupLeaf)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (values : GKRAddress → R) (index : Nat) : RationalPair R :=
  match registry[index]? with
  | none => 0
  | some leaf => leaf.value hom challenges gamma values

theorem NativeLookupLeaf.registryValue_at [CommRing R] {registry : List NativeLookupLeaf}
    {index : Nat} {leaf : NativeLookupLeaf} (found : registry[index]? = some leaf)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (values : GKRAddress → R) :
    registryValue registry hom challenges gamma values index = leaf.value hom challenges gamma values := by
  simp only [registryValue, found]

/-- Actual helper formulas, before converting them into abstract tree addition.
The payloads are read from the native graph's actual operands and columns. -/
inductive NativeLookupGate where
  | pair (output : RationalPorts) (left right : LookupPayload)
  | setup (output : RationalPorts) (mask : LookupWeight) (input : LookupPayload)
      (multiplicity : GKRAddress) (table : LookupPayload)
  | add (output left right : RationalPorts)
  | extend (output input : RationalPorts) (remainder : LookupPayload)
  | copy (output input : GKRAddress)

def NativeLookupGate.Holds [CommRing R] (hom : Source.BaseField →+* R)
    (challenges : CacheChallenges R) (gamma : R) (values : GKRAddress → R) : NativeLookupGate → Prop
  | .pair output left right => output.value values =
      lookupPair gamma (left.interpret hom challenges values) (right.interpret hom challenges values)
  | .setup output mask input multiplicity table => output.value values =
      lookupMinusSetup gamma (mask.value values) (input.interpret hom challenges values)
        (values multiplicity) (table.interpret hom challenges values)
  | .add output left right => output.value values = (left.value values).add (right.value values)
  | .extend output input remainder => output.value values =
      lookupRemainder gamma (input.value values) (remainder.interpret hom challenges values)
  | .copy output input => values output = values input

def NativeLookupGate.Normalizes (registry : List NativeLookupLeaf) : NativeLookupGate → LookupStep → Prop
  | .pair output left right, .seed actual l r =>
      output = actual ∧ registry[l]? = some ⟨.one, left⟩ ∧ registry[r]? = some ⟨.one, right⟩
  | .setup output mask input multiplicity table, .seed actual l r =>
      output = actual ∧ registry[l]? = some ⟨mask, input⟩ ∧
        registry[r]? = some ⟨.negativeMultiplicity multiplicity, table⟩
  | .add output left right, .add actual l r => output = actual ∧ left = l ∧ right = r
  | .extend output input remainder, .extend actual parent index =>
      output = actual ∧ input = parent ∧ registry[index]? = some ⟨.one, remainder⟩
  | .copy output input, .copy actual parent => output = actual ∧ input = parent
  | _, _ => False

theorem NativeLookupGate.normalization_sound [CommRing R] {registry : List NativeLookupLeaf}
    {native : NativeLookupGate} {step : LookupStep} (valid : Normalizes registry native step)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (values : GKRAddress → R) (holds : native.Holds hom challenges gamma values) :
    step.Holds values (NativeLookupLeaf.registryValue registry hom challenges gamma values) := by
  cases native <;> cases step <;> try exact False.elim valid
  case pair.seed output left right actual l r =>
    rcases valid with ⟨rfl, leftFound, rightFound⟩
    change output.value values = _
    rw [NativeLookupLeaf.registryValue_at leftFound, NativeLookupLeaf.registryValue_at rightFound]
    exact holds.trans (lookupPair_is_add _ _ _)
  case setup.seed output mask input multiplicity table actual l r =>
    rcases valid with ⟨rfl, leftFound, rightFound⟩
    change output.value values = _
    rw [NativeLookupLeaf.registryValue_at leftFound, NativeLookupLeaf.registryValue_at rightFound]
    exact holds.trans (lookupMinusSetup_is_add _ _ _ _ _)
  case add.add output left right actual l r =>
    rcases valid with ⟨rfl, rfl, rfl⟩
    exact holds
  case extend.extend output input remainder actual parent index =>
    rcases valid with ⟨rfl, rfl, found⟩
    change output.value values = _
    rw [NativeLookupLeaf.registryValue_at found]
    exact holds.trans (lookupRemainder_is_add _ _ _)
  case copy.copy output input actual parent =>
    rcases valid with ⟨rfl, rfl⟩
    exact holds

/-- A certificate selects an actual native gate; it cannot replace the native
equation or its operands with a more convenient expression. -/
structure NativeLookupBinding where
  nativeIndex : Nat
  step : LookupStep

def NativeLookupBinding.Valid (registry : List NativeLookupLeaf) (native : List NativeLookupGate)
    (binding : NativeLookupBinding) : Prop :=
  match native[binding.nativeIndex]? with
  | none => False
  | some actual => actual.Normalizes registry binding.step

theorem NativeLookupBinding.sound [CommRing R] {registry : List NativeLookupLeaf}
    {native : List NativeLookupGate} {binding : NativeLookupBinding}
    (valid : binding.Valid registry native) (hom : Source.BaseField →+* R)
    (challenges : CacheChallenges R) (gamma : R) (values : GKRAddress → R)
    (holds : ∀ actual ∈ native, actual.Holds hom challenges gamma values) :
    binding.step.Holds values (NativeLookupLeaf.registryValue registry hom challenges gamma values) := by
  cases found : native[binding.nativeIndex]? with
  | none => simp only [Valid, found] at valid
  | some actual =>
    have legal : actual.Normalizes registry binding.step := by simpa only [Valid, found] using valid
    exact actual.normalization_sound legal hom challenges gamma values (holds actual (List.mem_of_getElem? found))

inductive PredicateChecks (predicate : α → Prop) : List α → Prop where
  | nil : PredicateChecks predicate []
  | cons {head tail} : predicate head → PredicateChecks predicate tail → PredicateChecks predicate (head :: tail)

theorem PredicateChecks.all {predicate : α → Prop} {items : List α}
    (checks : PredicateChecks predicate items) : ∀ item ∈ items, predicate item := by
  induction checks with
  | nil => intro item member; cases member
  | cons head tail proof =>
      intro item member
      rcases List.mem_cons.mp member with rfl | member
      · exact head
      · exact proof item member

theorem NativeLookupBinding.replay_sound [CommRing R]
    {registry : List NativeLookupLeaf} {native : List NativeLookupGate}
    {bindings : List NativeLookupBinding}
    (valid : ∀ binding ∈ bindings, binding.Valid registry native)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (values : GKRAddress → R) (holds : ∀ actual ∈ native, actual.Holds hom challenges gamma values)
    {environment result : LookupEnvironment}
    (sound : environment.Sound values (NativeLookupLeaf.registryValue registry hom challenges gamma values))
    (replayed : LookupStep.run (bindings.map (·.step)) environment = some result) :
    result.Sound values (NativeLookupLeaf.registryValue registry hom challenges gamma values) := by
  apply LookupStep.run_sound (sound := sound) (replayed := replayed)
  intro step member
  obtain ⟨binding, bindingMember, rfl⟩ := List.mem_map.mp member
  exact binding.sound (valid binding bindingMember) hom challenges gamma values holds

/-- Concrete native formulas imply source reduction once the finite port trace,
primitive fields and exact source-label multiset have all been checked. -/
theorem NativeLookupBinding.source_translation [CommRing R]
    {registry : List NativeLookupLeaf} {native : List NativeLookupGate}
    {bindings : List NativeLookupBinding}
    (valid : ∀ binding ∈ bindings, binding.Valid registry native)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (values : GKRAddress → R) (holds : ∀ actual ∈ native, actual.Holds hom challenges gamma values)
    {result : LookupEnvironment} (replayed : LookupStep.run (bindings.map (·.step)) [] = some result)
    {output : RationalPorts} {tree : LookupTree Nat} (root : result.pair output = some tree)
    (sourcePrimitive : Nat → RationalPair R) (label : Nat → Nat)
    (fields : ∀ index ∈ tree.leaves,
      NativeLookupLeaf.registryValue registry hom challenges gamma values index = sourcePrimitive (label index))
    {source : List Nat} (coverage : (tree.leaves.map label).Perm source) :
    output.value values = (source.map sourcePrimitive).sum := by
  have normalized : ∀ step ∈ bindings.map (·.step),
      step.Holds values (NativeLookupLeaf.registryValue registry hom challenges gamma values) := by
    intro step member
    obtain ⟨binding, bindingMember, rfl⟩ := List.mem_map.mp member
    exact binding.sound (valid binding bindingMember) hom challenges gamma values holds
  exact LookupStep.source_translation normalized replayed root label fields coverage

theorem NativeLookupBinding.reduction [CommRing R]
    {registry : List NativeLookupLeaf} {native : List NativeLookupGate}
    {bindings : List NativeLookupBinding}
    (valid : ∀ binding ∈ bindings, binding.Valid registry native)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (values : GKRAddress → R) (holds : ∀ actual ∈ native, actual.Holds hom challenges gamma values)
    {result : LookupEnvironment} (replayed : LookupStep.run (bindings.map (·.step)) [] = some result)
    {output : RationalPorts} {tree : LookupTree Nat} (root : result.pair output = some tree) :
    output.value values =
      (tree.leaves.map (NativeLookupLeaf.registryValue registry hom challenges gamma values)).sum := by
  apply source_translation valid hom challenges gamma values holds replayed root
    (NativeLookupLeaf.registryValue registry hom challenges gamma values) id
  · intro index member
    rfl
  · simpa only [List.map_id] using List.Perm.refl tree.leaves

end Airbender.Compiler
