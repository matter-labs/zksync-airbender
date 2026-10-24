import GKRProtocol.NativeLookup

namespace Airbender.Compiler
set_option warningAsError true

def AffineProgram.replace [BEq Address] (program : AffineProgram Address C) (address : Address)
    (replacement : AffineProgram Address C) : AffineProgram Address C := match program with
  | .constant scalar => .constant scalar
  | .input actual => if actual == address then replacement else .input actual
  | .add left right => .add (left.replace address replacement) (right.replace address replacement)
  | .scale coefficient inner => .scale coefficient (inner.replace address replacement)

theorem AffineProgram.replace_value [BEq Address] [LawfulBEq Address] [CommRing R]
    (program replacement : AffineProgram Address R) (address : Address) (values : Address → R)
    (definitionValue : values address = replacement.value values) :
    (program.replace address replacement).value values = program.value values := by
  induction program with
  | constant scalar => rfl
  | input actual =>
    simp only [replace]
    split
    next checked =>
      have same : actual = address := LawfulBEq.eq_of_beq checked
      subst actual
      exact definitionValue.symm
    next different => rfl
  | add left right leftProof rightProof =>
    change (left.replace address replacement).value values + (right.replace address replacement).value values = _
    rw [leftProof, rightProof]
    rfl
  | scale coefficient inner proof =>
    change coefficient * (inner.replace address replacement).value values = _
    rw [proof]
    rfl

theorem AffineProgram.mapCoefficients_replace [BEq Address]
    (program replacement : AffineProgram Address C) (address : Address) (map : C → D) :
    (program.replace address replacement).mapCoefficients map =
      (program.mapCoefficients map).replace address (replacement.mapCoefficients map) := by
  induction program with
  | constant scalar => rfl
  | input actual =>
    simp only [replace, mapCoefficients]
    split <;> rfl
  | add left right leftProof rightProof =>
    exact congrArg₂ AffineProgram.add leftProof rightProof
  | scale coefficient inner proof =>
    exact congrArg (AffineProgram.scale (map coefficient)) proof

structure AffineDefinition where
  output : GKRAddress
  program : LookupPayload

def AffineDefinition.Holds [CommRing R] (definition : AffineDefinition)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (values : GKRAddress → R) : Prop :=
  values definition.output = definition.program.interpret hom challenges values

theorem AffineDefinition.expand_value [CommRing R] (definition : AffineDefinition)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (values : GKRAddress → R)
    (holds : definition.Holds hom challenges values) (payload : LookupPayload) :
    LookupPayload.interpret (payload.replace definition.output definition.program) hom challenges values =
      payload.interpret hom challenges values := by
  unfold LookupPayload.interpret
  rw [AffineProgram.mapCoefficients_replace]
  exact AffineProgram.replace_value _ _ _ _ holds

/-- Expansion witnesses select actual definitions. Replacement expressions are
reconstructed from the native cache/materialization/copy relation list. -/
def LookupPayload.expand (definitions : List AffineDefinition) : List Nat → LookupPayload → Option LookupPayload
  | [], payload => some payload
  | index :: rest, payload =>
      match definitions[index]? with
      | none => none
      | some definition => expand definitions rest (payload.replace definition.output definition.program)

theorem LookupPayload.expand_sound [CommRing R] {definitions : List AffineDefinition}
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (values : GKRAddress → R)
    (holds : ∀ definition ∈ definitions, definition.Holds hom challenges values)
    {indices : List Nat} {payload result : LookupPayload}
    (checked : LookupPayload.expand definitions indices payload = some result) :
    result.interpret hom challenges values = payload.interpret hom challenges values := by
  induction indices generalizing payload with
  | nil =>
    simp only [expand, Option.some.injEq] at checked
    cases checked
    rfl
  | cons index rest proof =>
    cases found : definitions[index]? with
    | none => simp [expand, found] at checked
    | some definition =>
      have tail : LookupPayload.expand definitions rest
          (payload.replace definition.output definition.program) = some result := by
        simpa only [expand, found] using checked
      exact (proof tail).trans
        (definition.expand_value hom challenges values (holds definition (List.mem_of_getElem? found)) payload)

end Airbender.Compiler
