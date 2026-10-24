import GKRCompiler.HomPolynomial
import GKRProtocol.MemoryFields

namespace Airbender.Compiler
set_option warningAsError true

theorem Agreement.sound_hom [CommRing F] [DecidableEq F] [CommRing R]
    {relations : List (Polynomial n F)} {agreement : Agreement relations}
    (checked : agreement.check = true) (hom : F →+* R) (values : Fin n → R)
    (holds : ∀ relation ∈ relations, evaluateHom hom values relation = 0) :
    evaluateHom hom values agreement.source = evaluateHom hom values agreement.lowered := by
  have result := equal_hom_sound checked hom values
  rw [evaluateHom_add, combination_hom_zero hom holds, add_zero] at result
  exact result

structure MemorySymbolPlacement (n : Nat) where
  address : GKRAddress → Fin n
  power : Fin 6 → Fin n
  gamma : Fin n

/-- Seven extra coordinates keep every native input symbol distinct from every
challenge coordinate. A table of source-selected aliases cannot merge them. -/
def MemorySymbolPlacement.forBank (bank : WireBank n) : MemorySymbolPlacement (n + 7) where
  address address := (bank.placement address).castAdd 7
  power index := ⟨n + index.val, by omega⟩
  gamma := ⟨n + 6, by omega⟩

def memorySymbolValues [CommRing R] (bank : WireBank n) (base : GKRAddress → Source.BaseField)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (index : Fin (n + 7)) : R :=
  if bound : index.val < n then hom (base (bank.address ⟨index.val, bound⟩))
  else if powerBound : index.val - n < 6 then challenges.memoryPowers ⟨index.val - n, powerBound⟩
  else challenges.memoryGamma

theorem memorySymbolValues_base [CommRing R] (bank : WireBank n) (base : GKRAddress → Source.BaseField)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (index : Fin n) :
    memorySymbolValues bank base hom challenges (index.castAdd 7) = hom (base (bank.address index)) := by
  simp [memorySymbolValues, index.isLt]

theorem memorySymbolValues_power [CommRing R] (bank : WireBank n) (base : GKRAddress → Source.BaseField)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (index : Fin 6) :
    memorySymbolValues bank base hom challenges ((MemorySymbolPlacement.forBank bank).power index) =
      challenges.memoryPowers index := by
  have outside : ¬n + index.val < n := by omega
  simp [memorySymbolValues, MemorySymbolPlacement.forBank, outside, index.isLt]

theorem memorySymbolValues_gamma [CommRing R] (bank : WireBank n) (base : GKRAddress → Source.BaseField)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) :
    memorySymbolValues bank base hom challenges (MemorySymbolPlacement.forBank bank).gamma = challenges.memoryGamma := by
  have outside : ¬n + 6 < n := by omega
  simp [memorySymbolValues, MemorySymbolPlacement.forBank, outside]

def WireBank.inputCheck (bank : WireBank n) (inputs : List GKRAddress) : Bool :=
  inputs.all (fun address => addressEqual (bank.address (bank.placement address)) address)

theorem memorySymbolValues_inputs [CommRing R] (bank : WireBank n) (typing : ConsumerTyping)
    (assignment : TypedAssignment R) (hom : Source.BaseField →+* R) (challenges : CacheChallenges R)
    (inputs : List GKRAddress) (inBank : bank.inputCheck inputs = true)
    (roles : inputs.all (fun address => typing.compatible (address, .base)) = true) :
    ∀ address ∈ inputs, memorySymbolValues bank assignment.base hom challenges
      ((MemorySymbolPlacement.forBank bank).address address) = assignment.value typing hom address := by
  intro address member
  have same := (addressEqual_iff _ _).mp (List.all_eq_true.mp inBank address member)
  have role := List.all_eq_true.mp roles address member
  change memorySymbolValues bank assignment.base hom challenges ((bank.placement address).castAdd 7) = _
  rw [memorySymbolValues_base, same, assignment.value_base typing hom role]

/-- Memory powers and gamma are formal variables, not sampled base-field
constants. Unsupported lookup-alpha coefficients fail closed. -/
def CacheCoefficient.memoryExpression (placement : MemorySymbolPlacement n) :
    CacheCoefficient → Option (Expression n Source.BaseField)
  | .base raw => some (.constant ((raw : Source.BaseField) * montgomeryInverse))
  | .natural scalar => some (.constant scalar)
  | .negativeOne => some (.constant (-1))
  | .memoryPower index => some (.atom (placement.power index))
  | .memoryGamma => some (.atom placement.gamma)
  | .lookupPower _ => none

theorem CacheCoefficient.memoryExpression_sound [CommRing R] (coefficient : CacheCoefficient)
    (placement : MemorySymbolPlacement n) {expression : Expression n Source.BaseField}
    (reflected : coefficient.memoryExpression placement = some expression)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (symbols : Fin n → R)
    (powers : ∀ index, symbols (placement.power index) = challenges.memoryPowers index)
    (gamma : symbols placement.gamma = challenges.memoryGamma) :
    expression.valueHom hom symbols = coefficient.value hom challenges := by
  cases coefficient with
  | base raw => cases Option.some.inj reflected; rfl
  | natural scalar => cases Option.some.inj reflected; rfl
  | negativeOne => cases Option.some.inj reflected; simp [Expression.valueHom, value]
  | memoryPower index => cases Option.some.inj reflected; exact powers index
  | memoryGamma => cases Option.some.inj reflected; exact gamma
  | lookupPower index => cases reflected

def LookupPayload.memoryExpression (placement : MemorySymbolPlacement n) :
    LookupPayload → Option (Expression n Source.BaseField)
  | .constant coefficient => coefficient.memoryExpression placement
  | .input address => some (.atom (placement.address address))
  | .add left right => do return .add (← LookupPayload.memoryExpression placement left) (← LookupPayload.memoryExpression placement right)
  | .scale coefficient inner => do
      return .mul (← coefficient.memoryExpression placement) (← LookupPayload.memoryExpression placement inner)

theorem LookupPayload.memoryExpression_sound [CommRing R] (payload : LookupPayload)
    (placement : MemorySymbolPlacement n) {expression : Expression n Source.BaseField}
    (reflected : payload.memoryExpression placement = some expression)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R)
    (symbols : Fin n → R) (values : GKRAddress → R)
    (powers : ∀ index, symbols (placement.power index) = challenges.memoryPowers index)
    (gamma : symbols placement.gamma = challenges.memoryGamma)
    (inputs : ∀ address ∈ payload.inputs, symbols (placement.address address) = values address) :
    expression.valueHom hom symbols = payload.interpret hom challenges values := by
  induction payload generalizing expression with
  | constant coefficient => exact coefficient.memoryExpression_sound placement reflected hom challenges symbols powers gamma
  | input address =>
      cases Option.some.inj reflected
      exact inputs address List.mem_cons_self
  | add left right leftProof rightProof =>
      cases leftReflected : LookupPayload.memoryExpression placement left with
      | none => simp [memoryExpression, leftReflected] at reflected
      | some leftExpression =>
          cases rightReflected : LookupPayload.memoryExpression placement right with
          | none => simp [memoryExpression, leftReflected, rightReflected] at reflected
          | some rightExpression =>
              simp only [memoryExpression, leftReflected, rightReflected, Option.bind_eq_bind, Option.bind_some,
                Option.pure_def, Option.some.injEq] at reflected
              cases reflected
              exact congrArg₂ (· + ·)
                (leftProof leftReflected (fun address member => inputs address (List.mem_append_left _ member)))
                (rightProof rightReflected (fun address member => inputs address (List.mem_append_right _ member)))
  | scale coefficient inner proof =>
      cases scalarReflected : coefficient.memoryExpression placement with
      | none => simp [memoryExpression, scalarReflected] at reflected
      | some scalarExpression =>
          cases innerReflected : LookupPayload.memoryExpression placement inner with
          | none => simp [memoryExpression, scalarReflected, innerReflected] at reflected
          | some innerExpression =>
              simp only [memoryExpression, scalarReflected, innerReflected, Option.bind_eq_bind, Option.bind_some,
                Option.pure_def, Option.some.injEq] at reflected
              cases reflected
              exact congrArg₂ (· * ·)
                (coefficient.memoryExpression_sound placement scalarReflected hom challenges symbols powers gamma)
                (proof innerReflected inputs)

end Airbender.Compiler
