import GKRProtocol.ProductReduction

namespace Airbender.Compiler
set_option warningAsError true

def productRegistryValue [CommRing R] (registry : List LookupPayload)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R)
    (values : GKRAddress → R) (index : Nat) : R :=
  match registry[index]? with
  | some payload => payload.interpret hom challenges values
  | none => 0

theorem productRegistryValue_at [CommRing R] {registry : List LookupPayload} {index : Nat}
    {payload : LookupPayload} (found : registry[index]? = some payload)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (values : GKRAddress → R) :
    productRegistryValue registry hom challenges values index = payload.interpret hom challenges values := by
  simp only [productRegistryValue, found]

/-- The actual native product formulas precede their indexed reduction trace.
Memory and initialization tuples retain their actual affine payloads. -/
inductive NativeProductGate where
  | single (output : GKRAddress) (input : LookupPayload)
  | pair (output : GKRAddress) (left right : LookupPayload)
  | mul (output left right : GKRAddress)
  | mask (output input predicate : GKRAddress)
  | copy (output input : GKRAddress)

def NativeProductGate.Holds [CommRing R] (hom : Source.BaseField →+* R)
    (challenges : CacheChallenges R) (values : GKRAddress → R) : NativeProductGate → Prop
  | .single output input => values output = input.interpret hom challenges values
  | .pair output left right => values output =
      left.interpret hom challenges values * right.interpret hom challenges values
  | .mul output left right => values output = values left * values right
  | .mask output input predicate => values output = maskProduct (values predicate) (values input)
  | .copy output input => values output = values input

def NativeProductGate.Normalizes (registry : List LookupPayload) : NativeProductGate → ProductStep → Prop
  | .single output input, .single actual index => output = actual ∧ registry[index]? = some input
  | .pair output left right, .pair actual l r =>
      output = actual ∧ registry[l]? = some left ∧ registry[r]? = some right
  | .mul output left right, .mul actual l r => output = actual ∧ left = l ∧ right = r
  | .mask output input predicate, .mask actual source predicateAddress =>
      output = actual ∧ input = source ∧ predicate = predicateAddress
  | .copy output input, .copy actual source => output = actual ∧ input = source
  | _, _ => False

theorem NativeProductGate.normalization_sound [CommRing R] {registry : List LookupPayload}
    {native : NativeProductGate} {step : ProductStep} (valid : native.Normalizes registry step)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (values : GKRAddress → R)
    (holds : native.Holds hom challenges values) :
    step.Holds values (productRegistryValue registry hom challenges values) := by
  cases native <;> cases step <;> try exact False.elim valid
  case single.single output input actual index =>
    rcases valid with ⟨rfl, found⟩
    exact holds.trans (productRegistryValue_at found hom challenges values).symm
  case pair.pair output left right actual l r =>
    rcases valid with ⟨rfl, leftFound, rightFound⟩
    exact holds.trans (congrArg₂ (· * ·)
      (productRegistryValue_at leftFound hom challenges values).symm
      (productRegistryValue_at rightFound hom challenges values).symm)
  case mul.mul output left right actual l r =>
    rcases valid with ⟨rfl, rfl, rfl⟩
    exact holds
  case mask.mask output input predicate actual source predicateAddress =>
    rcases valid with ⟨rfl, rfl, rfl⟩
    exact holds
  case copy.copy output input actual source =>
    rcases valid with ⟨rfl, rfl⟩
    exact holds

structure NativeProductBinding where
  nativeIndex : Nat
  step : ProductStep

def NativeProductBinding.Valid (registry : List LookupPayload) (native : List NativeProductGate)
    (binding : NativeProductBinding) : Prop :=
  match native[binding.nativeIndex]? with
  | some gate => gate.Normalizes registry binding.step
  | none => False

theorem NativeProductBinding.sound [CommRing R] {registry : List LookupPayload}
    {native : List NativeProductGate} {binding : NativeProductBinding}
    (valid : binding.Valid registry native) (hom : Source.BaseField →+* R)
    (challenges : CacheChallenges R) (values : GKRAddress → R)
    (holds : ∀ gate ∈ native, gate.Holds hom challenges values) :
    binding.step.Holds values (productRegistryValue registry hom challenges values) := by
  cases found : native[binding.nativeIndex]? with
  | none => simp [Valid, found] at valid
  | some actual =>
      have legal : actual.Normalizes registry binding.step := by simpa only [Valid, found] using valid
      exact actual.normalization_sound legal hom challenges values
        (holds actual (List.mem_of_getElem? found))

theorem NativeProductBinding.replay_sound [CommRing R]
    {registry : List LookupPayload} {native : List NativeProductGate}
    {bindings : List NativeProductBinding}
    (valid : ∀ binding ∈ bindings, binding.Valid registry native)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (values : GKRAddress → R)
    (holds : ∀ gate ∈ native, gate.Holds hom challenges values)
    {environment result : ProductEnvironment}
    (sound : environment.Sound values (productRegistryValue registry hom challenges values))
    (replayed : ProductStep.run (bindings.map (·.step)) environment = some result) :
    result.Sound values (productRegistryValue registry hom challenges values) := by
  apply ProductStep.run_sound (fun step member => ?_) sound replayed
  obtain ⟨binding, bindingMember, rfl⟩ := List.mem_map.mp member
  exact NativeProductBinding.sound (valid binding bindingMember) hom challenges values holds

end Airbender.Compiler
