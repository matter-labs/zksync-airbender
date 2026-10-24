import GKRProtocol.AffineExpansion
import GKRProtocol.LookupFields
import GKRProtocol.Typing

namespace Airbender.Compiler
set_option warningAsError true

theorem AffineProgram.mapCoefficients_comp (program : AffineProgram Address C)
    (first : C → D) (second : D → E) :
    (program.mapCoefficients first).mapCoefficients second = program.mapCoefficients (second ∘ first) := by
  induction program with
  | constant scalar => rfl
  | input address => rfl
  | add left right leftProof rightProof => exact congrArg₂ AffineProgram.add leftProof rightProof
  | scale coefficient inner proof => exact congrArg (AffineProgram.scale (second (first coefficient))) proof

theorem AffineProgram.value_congr [CommRing R] (program : AffineProgram Address R)
    (left right : Address → R) (same : ∀ address ∈ program.inputs, left address = right address) :
    program.value left = program.value right := by
  induction program with
  | constant scalar => rfl
  | input address => exact same address (List.mem_cons_self)
  | add first second firstProof secondProof =>
    exact congrArg₂ (· + ·)
      (firstProof (fun address member => same address (List.mem_append_left _ member)))
      (secondProof (fun address member => same address (List.mem_append_right _ member)))
  | scale coefficient inner proof => exact congrArg (coefficient * ·) (proof same)

theorem AffineProgram.value_map_hom [CommRing F] [CommRing R]
    (program : AffineProgram Address F) (hom : F →+* R) (values : Address → F) :
    (program.mapCoefficients hom).value (hom ∘ values) = hom (program.value values) := by
  induction program with
  | constant scalar => rfl
  | input address => rfl
  | add left right leftProof rightProof =>
    change _ + _ = hom (_ + _)
    rw [map_add, leftProof, rightProof]
  | scale coefficient inner proof =>
    change hom coefficient * _ = hom (coefficient * _)
    rw [map_mul, proof]

/-- Base-column expressions retain raw Montgomery coefficients and actual native
addresses. Alpha powers occur only outside these base expressions. -/
abbrev NativeBaseRecipe := AffineProgram GKRAddress Nat

def NativeBaseRecipe.decode (raw : Nat) : Source.BaseField := (raw : Source.BaseField) * montgomeryInverse

def NativeBaseRecipe.toPayload (recipe : NativeBaseRecipe) : LookupPayload :=
  recipe.mapCoefficients CacheCoefficient.base

def NativeBaseRecipe.value (recipe : NativeBaseRecipe) (values : GKRAddress → Source.BaseField) : Source.BaseField :=
  (recipe.mapCoefficients decode).value values

def NativeBaseRecipe.expression (placement : GKRAddress → Fin n) : NativeBaseRecipe → Expression n Source.BaseField
  | .constant scalar => .constant (decode scalar)
  | .input address => .atom (placement address)
  | .add left right => .add (expression placement left) (expression placement right)
  | .scale coefficient inner => .mul (.constant (decode coefficient)) (expression placement inner)

theorem NativeBaseRecipe.expression_value (recipe : NativeBaseRecipe) (placement : GKRAddress → Fin n)
    (values : Fin n → Source.BaseField) :
    (recipe.expression placement).value values = recipe.value (values ∘ placement) := by
  induction recipe with
  | constant scalar => rfl
  | input address => rfl
  | add left right leftProof rightProof => exact congrArg₂ (· + ·) leftProof rightProof
  | scale coefficient inner proof => exact congrArg (decode coefficient * ·) proof

theorem NativeBaseRecipe.interpret [CommRing R] (recipe : NativeBaseRecipe)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R)
    (base : GKRAddress → Source.BaseField) (values : GKRAddress → R)
    (inputs : ∀ address ∈ recipe.inputs, values address = hom (base address)) :
    recipe.toPayload.interpret hom challenges values = hom (recipe.value base) := by
  have mapped : (recipe.toPayload).mapCoefficients (CacheCoefficient.value hom challenges) =
      (recipe.mapCoefficients decode).mapCoefficients hom := by
    simp only [toPayload, AffineProgram.mapCoefficients_comp]
    rfl
  unfold LookupPayload.interpret
  rw [mapped]
  have same : ∀ address ∈ ((recipe.mapCoefficients decode).mapCoefficients hom).inputs,
      values address = (hom ∘ base) address := by
    simpa only [AffineProgram.mapCoefficients_inputs, Function.comp_apply] using inputs
  exact (AffineProgram.value_congr _ _ _ same).trans
    (AffineProgram.value_map_hom (recipe.mapCoefficients decode) hom base)

inductive NativeLookupEncoding where
  | scalar : NativeBaseRecipe → NativeLookupEncoding
  | vector : List NativeBaseRecipe → NativeLookupEncoding

def NativeLookupEncoding.columns : NativeLookupEncoding → List NativeBaseRecipe
  | .scalar recipe => [recipe]
  | .vector recipes => recipes

def NativeLookupEncoding.fields (encoding : NativeLookupEncoding) (base : GKRAddress → Source.BaseField) :
    List Source.BaseField := encoding.columns.map (fun recipe => recipe.value base)

def NativeLookupEncoding.vectorProgram : List NativeBaseRecipe → Nat → LookupPayload → LookupPayload
  | [], _, result => result
  | recipe :: rest, index, result =>
      vectorProgram rest (index + 1) (.add result (.scale (.lookupPower index) recipe.toPayload))

def NativeLookupEncoding.program : NativeLookupEncoding → LookupPayload
  | .scalar recipe => recipe.toPayload
  | .vector recipes => vectorProgram recipes 0 (.constant (.natural 0))

def NativeLookupEncoding.linearize [CommRing R] (hom : Source.BaseField →+* R) (alpha : R) :
    List Source.BaseField → Nat → R → R
  | [], _, result => result
  | field :: rest, index, result => linearize hom alpha rest (index + 1) (result + alpha ^ index * hom field)

theorem NativeLookupEncoding.vectorProgram_value [CommRing R]
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R)
    (base : GKRAddress → Source.BaseField) (values : GKRAddress → R)
    (recipes : List NativeBaseRecipe)
    (inputs : ∀ recipe ∈ recipes, ∀ address ∈ recipe.inputs, values address = hom (base address))
    (index : Nat) (initial : LookupPayload) :
    (vectorProgram recipes index initial).interpret hom challenges values =
      linearize hom challenges.lookupAlpha (recipes.map (fun recipe => recipe.value base)) index
        (initial.interpret hom challenges values) := by
  induction recipes generalizing index initial with
  | nil => rfl
  | cons recipe rest proof =>
    rw [vectorProgram, List.map_cons, linearize]
    rw [proof (fun actual member => inputs actual (List.mem_cons_of_mem _ member))]
    congr 1
    change initial.interpret hom challenges values +
      challenges.lookupAlpha ^ index * recipe.toPayload.interpret hom challenges values = _
    rw [recipe.interpret hom challenges base values (inputs recipe List.mem_cons_self)]

theorem NativeLookupEncoding.interpret [CommRing R] (encoding : NativeLookupEncoding)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R)
    (base : GKRAddress → Source.BaseField) (values : GKRAddress → R)
    (inputs : ∀ recipe ∈ encoding.columns, ∀ address ∈ recipe.inputs, values address = hom (base address)) :
    encoding.program.interpret hom challenges values =
      linearize hom challenges.lookupAlpha (encoding.fields base) 0 0 := by
  cases encoding with
  | scalar recipe =>
    simpa [program, fields, columns, linearize] using
      recipe.interpret hom challenges base values (inputs recipe List.mem_cons_self)
  | vector recipes =>
    simpa [program, fields, columns, LookupPayload.interpret, AffineProgram.mapCoefficients,
      AffineProgram.value, CacheCoefficient.value] using
      vectorProgram_value hom challenges base values recipes inputs 0 (.constant (.natural 0))

structure TypedAssignment (R : Type) where
  base : GKRAddress → Source.BaseField
  extension : GKRAddress → R

def TypedAssignment.value [CommRing R] (assignment : TypedAssignment R) (typing : ConsumerTyping)
    (hom : Source.BaseField →+* R) (address : GKRAddress) : R :=
  if typing.compatible (address, .base) then hom (assignment.base address) else assignment.extension address

theorem TypedAssignment.value_base [CommRing R] (assignment : TypedAssignment R) (typing : ConsumerTyping)
    (hom : Source.BaseField →+* R) {address : GKRAddress}
    (checked : typing.compatible (address, .base) = true) :
    assignment.value typing hom address = hom (assignment.base address) := by
  simp only [value, checked, ↓reduceIte]

def NativeLookupEncoding.baseCheck (encoding : NativeLookupEncoding) (typing : ConsumerTyping) : Bool :=
  encoding.columns.all (fun recipe => recipe.inputs.all (fun address => typing.compatible (address, .base)))

theorem NativeLookupEncoding.interpret_typed [CommRing R] (encoding : NativeLookupEncoding)
    (typing : ConsumerTyping) (checked : encoding.baseCheck typing = true)
    (assignment : TypedAssignment R) (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) :
    encoding.program.interpret hom challenges (assignment.value typing hom) =
      linearize hom challenges.lookupAlpha (encoding.fields assignment.base) 0 0 := by
  have inputs : ∀ recipe ∈ encoding.columns, ∀ address ∈ recipe.inputs,
      typing.compatible (address, .base) = true := by
    simpa only [baseCheck, List.all_eq_true] using checked
  exact encoding.interpret hom challenges assignment.base (assignment.value typing hom)
    (fun recipe member address addressMember => assignment.value_base typing hom (inputs recipe member address addressMember))

/-- Neither side of a source-column identity is supplied as a replacement
polynomial: the source is an authored encoded field and the target is the
actual native base recipe's expression. -/
structure BaseRecipeAgreement (relations : List (Polynomial n Source.BaseField))
    (recipe : NativeBaseRecipe) where
  source : Source.EncodedField
  witness : Combination relations

def BaseRecipeAgreement.field {relations : List (Polynomial n Source.BaseField)}
    {recipe : NativeBaseRecipe} (agreement : BaseRecipeAgreement relations recipe)
    (placement : GKRAddress → Fin n) : LookupFieldAgreement relations :=
  ⟨agreement.source, recipe.expression placement, agreement.witness⟩

def BaseRecipeAgreement.check {relations : List (Polynomial n Source.BaseField)}
    {recipe : NativeBaseRecipe} (agreement : BaseRecipeAgreement relations recipe)
    (sourcePlacement : Nat → Fin n) (wirePlacement : GKRAddress → Fin n) : Bool :=
  (agreement.field wirePlacement).check sourcePlacement

theorem BaseRecipeAgreement.sound {relations : List (Polynomial n Source.BaseField)}
    {recipe : NativeBaseRecipe} {agreement : BaseRecipeAgreement relations recipe}
    (sourcePlacement : Nat → Fin n) (wirePlacement : GKRAddress → Fin n)
    (checked : agreement.check sourcePlacement wirePlacement = true)
    {values : Fin n → Source.BaseField} (holds : Satisfies relations values)
    (base : GKRAddress → Source.BaseField)
    (wires : ∀ address ∈ recipe.inputs, base address = values (wirePlacement address)) :
    agreement.source.value (values ∘ sourcePlacement) = recipe.value base := by
  have same := LookupFieldAgreement.sound (field := agreement.field wirePlacement)
    sourcePlacement checked holds
  change agreement.source.value (values ∘ sourcePlacement) =
    (recipe.expression wirePlacement).value values at same
  rw [recipe.expression_value] at same
  apply same.trans
  apply Eq.symm
  apply AffineProgram.value_congr
  simpa only [AffineProgram.mapCoefficients_inputs, Function.comp_apply] using wires

end Airbender.Compiler
