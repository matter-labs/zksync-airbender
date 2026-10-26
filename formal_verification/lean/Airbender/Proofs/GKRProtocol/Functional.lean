import Airbender.Proofs.GKRProtocol.BaseEncoding

namespace Airbender.Compiler
set_option warningAsError true

/-- Functional extension-field operations retain the actual native affine
payloads. Lookup gamma is separate from the memory/cache challenges. -/
inductive RExpression where
  | input : GKRAddress → RExpression
  | coefficient : CacheCoefficient → RExpression
  | lookupGamma
  | affine : LookupPayload → RExpression
  | add : RExpression → RExpression → RExpression
  | mul : RExpression → RExpression → RExpression
  | neg : RExpression → RExpression

def RExpression.inputs : RExpression → List GKRAddress
  | .input address => [address]
  | .coefficient _ | .lookupGamma => []
  | .affine payload => payload.inputs
  | .add left right | .mul left right => left.inputs ++ right.inputs
  | .neg expression => expression.inputs

def RExpression.value [CommRing R] (hom : Source.BaseField →+* R) (challenges : CacheChallenges R)
    (gamma : R) (values : GKRAddress → R) : RExpression → R
  | .input address => values address
  | .coefficient scalar => scalar.value hom challenges
  | .lookupGamma => gamma
  | .affine payload => payload.interpret hom challenges values
  | .add left right => left.value hom challenges gamma values + right.value hom challenges gamma values
  | .mul left right => left.value hom challenges gamma values * right.value hom challenges gamma values
  | .neg expression => -expression.value hom challenges gamma values

theorem RExpression.value_congr [CommRing R] (expression : RExpression)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (left right : GKRAddress → R) (same : ∀ address ∈ expression.inputs, left address = right address) :
    expression.value hom challenges gamma left = expression.value hom challenges gamma right := by
  induction expression with
  | input address => exact same address List.mem_cons_self
  | coefficient _ | lookupGamma => rfl
  | affine payload =>
      apply AffineProgram.value_congr
      simpa only [RExpression.inputs, AffineProgram.mapCoefficients_inputs] using same
  | add first second firstProof secondProof =>
      exact congrArg₂ (· + ·)
        (firstProof (fun address member => same address (List.mem_append_left _ member)))
        (secondProof (fun address member => same address (List.mem_append_right _ member)))
  | mul first second firstProof secondProof =>
      exact congrArg₂ (· * ·)
        (firstProof (fun address member => same address (List.mem_append_left _ member)))
        (secondProof (fun address member => same address (List.mem_append_right _ member)))
  | neg expression proof => exact congrArg Neg.neg (proof same)

abbrev FunctionalStep := List (GKRAddress × RExpression)

def FunctionalStep.outputs (step : FunctionalStep) : List GKRAddress := step.map Prod.fst
def FunctionalStep.inputs (step : FunctionalStep) : List GKRAddress := step.flatMap (fun entry => entry.2.inputs)

def FunctionalStep.Holds [CommRing R] (step : FunctionalStep) (hom : Source.BaseField →+* R)
    (challenges : CacheChallenges R) (gamma : R) (values : GKRAddress → R) : Prop :=
  ∀ entry ∈ step, values entry.1 = entry.2.value hom challenges gamma values

theorem FunctionalStep.holds_congr [CommRing R] (step : FunctionalStep)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (left right : GKRAddress → R)
    (same : ∀ address ∈ step.outputs ++ step.inputs, left address = right address)
    (holds : step.Holds hom challenges gamma left) : step.Holds hom challenges gamma right := by
  intro entry member
  have output := same entry.1 (List.mem_append_left _ (List.mem_map.mpr ⟨entry, member, rfl⟩))
  have inputs : ∀ address ∈ entry.2.inputs, left address = right address := by
    intro address inside
    exact same address (List.mem_append_right _ (List.mem_flatMap.mpr ⟨entry, member, inside⟩))
  exact output.symm.trans ((holds entry member).trans (entry.2.value_congr hom challenges gamma left right inputs))

namespace Functional

def read (isBase : GKRAddress → Bool) (base extension : GKRAddress → R) (address : GKRAddress) : R :=
  if isBase address then base address else extension address

def write : List (GKRAddress × R) → (GKRAddress → R) → GKRAddress → R
  | [], original => original
  | (output, value) :: rest, original => fun address =>
      if addressEqual address output then value else write rest original address

theorem write_frame (updates : List (GKRAddress × R)) (original : GKRAddress → R)
    (address : GKRAddress) (outside : address ∉ updates.map Prod.fst) :
    write updates original address = original address := by
  induction updates with
  | nil => rfl
  | cons first rest proof =>
      have different : addressEqual address first.1 = false := by
        apply Bool.eq_false_iff.mpr
        intro same
        apply outside
        exact List.mem_cons.mpr (.inl ((addressEqual_iff _ _).mp same))
      simp only [write, different, Bool.false_eq_true, ↓reduceIte]
      exact proof (fun member => outside (List.mem_cons_of_mem _ member))

theorem write_member (updates : List (GKRAddress × R)) (original : GKRAddress → R)
    (unique : (updates.map Prod.fst).Nodup) (entry : GKRAddress × R) (member : entry ∈ updates) :
    write updates original entry.1 = entry.2 := by
  induction updates with
  | nil => simp at member
  | cons first rest proof =>
      rcases List.mem_cons.mp member with same | inside
      · subst entry
        simp only [write, (addressEqual_iff _ _).mpr rfl, ↓reduceIte]
      · have distinct := List.nodup_cons.mp unique
        have different : addressEqual entry.1 first.1 = false := by
          apply Bool.eq_false_iff.mpr
          intro same
          apply distinct.1
          exact (addressEqual_iff _ _).mp same ▸ List.mem_map.mpr ⟨entry, inside, rfl⟩
        simp only [write, different, Bool.false_eq_true, ↓reduceIte]
        exact proof distinct.2 inside

end Functional

def FunctionalStep.execute [CommRing R] (step : FunctionalStep) (hom : Source.BaseField →+* R)
    (challenges : CacheChallenges R) (gamma : R) (isBase : GKRAddress → Bool)
    (base extension : GKRAddress → R) : GKRAddress → R :=
  Functional.write (step.map (fun entry =>
    (entry.1, entry.2.value hom challenges gamma (Functional.read isBase base extension)))) extension

structure FunctionalStep.Valid (isBase : GKRAddress → Bool) (known : List GKRAddress) (step : FunctionalStep) : Prop where
  unique : step.outputs.Nodup
  fresh : ∀ output ∈ step.outputs, isBase output = false ∧ output ∉ known
  inputs : ∀ address ∈ step.inputs, isBase address = true ∨ address ∈ known

def FunctionalStep.check (isBase : GKRAddress → Bool) (known : List GKRAddress) (step : FunctionalStep) : Bool :=
  distinct step.outputs &&
    step.outputs.all (fun output => !isBase output && !known.contains output) &&
    step.inputs.all (fun address => isBase address || known.contains address)

theorem FunctionalStep.check_sound {isBase : GKRAddress → Bool} {known : List GKRAddress} {step : FunctionalStep}
    (checked : step.check isBase known = true) : step.Valid isBase known := by
  simp only [check, Bool.and_eq_true, List.all_eq_true] at checked
  refine ⟨(distinct_iff _).mp checked.1.1, ?_, ?_⟩
  · intro output member
    simpa using checked.1.2 output member
  · intro address member
    simpa using checked.2 address member

theorem FunctionalStep.execute_frame [CommRing R] (step : FunctionalStep)
    {isBase : GKRAddress → Bool} {known : List GKRAddress} (valid : step.Valid isBase known)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (base extension : GKRAddress → R) (address : GKRAddress)
    (prior : isBase address = true ∨ address ∈ known) :
    Functional.read isBase base (step.execute hom challenges gamma isBase base extension) address =
      Functional.read isBase base extension address := by
  cases role : isBase address with
  | true => simp only [Functional.read, role, ↓reduceIte]
  | false =>
      have previous : address ∈ known := prior.resolve_left (by simp only [role, Bool.false_eq_true, not_false_eq_true])
      have absent : address ∉ step.outputs := fun member => (valid.fresh address member).2 previous
      unfold execute
      simp only [Functional.read, role, Bool.false_eq_true, ↓reduceIte]
      apply Functional.write_frame
      simpa only [List.map_map, Function.comp_def, outputs] using absent

theorem FunctionalStep.execute_sound [CommRing R] (step : FunctionalStep)
    {isBase : GKRAddress → Bool} {known : List GKRAddress} (valid : step.Valid isBase known)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (base extension : GKRAddress → R) :
    step.Holds hom challenges gamma
      (Functional.read isBase base (step.execute hom challenges gamma isBase base extension)) := by
  intro entry member
  let before := Functional.read isBase base extension
  let after := Functional.read isBase base (step.execute hom challenges gamma isBase base extension)
  let updates := step.map (fun row => (row.1, row.2.value hom challenges gamma before))
  have sameOutputs : updates.map Prod.fst = step.outputs := by
    simp only [updates, outputs, List.map_map]
    rfl
  have present : (entry.1, entry.2.value hom challenges gamma before) ∈ updates :=
    List.mem_map.mpr ⟨entry, member, rfl⟩
  have output := Functional.write_member updates extension (sameOutputs.symm ▸ valid.unique) _ present
  have baseRole : isBase entry.1 = false :=
    (valid.fresh entry.1 (List.mem_map.mpr ⟨entry, member, rfl⟩)).1
  have assigned : after entry.1 = entry.2.value hom challenges gamma before := by
    simpa only [after, execute, Functional.read, baseRole, Bool.false_eq_true, ↓reduceIte, before, updates] using output
  apply assigned.trans
  apply entry.2.value_congr hom challenges gamma before after
  intro address inside
  exact (step.execute_frame valid hom challenges gamma base extension address
    (valid.inputs address (List.mem_flatMap.mpr ⟨entry, member, inside⟩))).symm

abbrev FunctionalProgram := List FunctionalStep

inductive FunctionalProgram.Valid (isBase : GKRAddress → Bool) : List GKRAddress → FunctionalProgram → Prop
  | nil {known} : Valid isBase known []
  | cons {known step rest} : step.Valid isBase known → Valid isBase (step.outputs ++ known) rest →
      Valid isBase known (step :: rest)

def FunctionalProgram.check (isBase : GKRAddress → Bool) (known : List GKRAddress) : FunctionalProgram → Bool
  | [] => true
  | step :: rest => step.check isBase known && check isBase (step.outputs ++ known) rest

def FunctionalProgram.outputs (program : FunctionalProgram) : List GKRAddress :=
  program.flatMap FunctionalStep.outputs

def FunctionalProgram.finalKnown (known : List GKRAddress) : FunctionalProgram → List GKRAddress
  | [] => known
  | step :: rest => FunctionalProgram.finalKnown (step.outputs ++ known) rest

theorem FunctionalProgram.valid_append {isBase : GKRAddress → Bool} {known : List GKRAddress}
    {first second : FunctionalProgram} (left : first.Valid isBase known)
    (right : second.Valid isBase (first.finalKnown known)) :
    (first ++ second).Valid isBase known := by
  induction left with
  | nil => exact right
  | @cons known step rest stepValid restValid proof =>
      apply Valid.cons stepValid
      apply proof
      exact right

theorem FunctionalProgram.check_sound {isBase : GKRAddress → Bool} {known : List GKRAddress}
    {program : FunctionalProgram} (checked : program.check isBase known = true) : program.Valid isBase known := by
  induction program generalizing known with
  | nil => exact .nil
  | cons step rest proof =>
      have parts : step.check isBase known = true ∧ FunctionalProgram.check isBase (step.outputs ++ known) rest = true := by
        simpa only [check, Bool.and_eq_true] using checked
      exact .cons (FunctionalStep.check_sound parts.1) (proof parts.2)

def FunctionalProgram.execute [CommRing R] (hom : Source.BaseField →+* R) (challenges : CacheChallenges R)
    (gamma : R) (isBase : GKRAddress → Bool) (base : GKRAddress → R) : FunctionalProgram →
    (GKRAddress → R) → GKRAddress → R
  | [], extension => extension
  | step :: rest, extension => execute hom challenges gamma isBase base rest
      (step.execute hom challenges gamma isBase base extension)

/-- Evaluate the whole functional graph and preserve every prior/base input.
Fresh outputs and checked dependencies make every earlier relation stable under
later writes. No field division or sampled-challenge assumption is needed. -/
theorem FunctionalProgram.execute_sound [CommRing R] {isBase : GKRAddress → Bool} {known : List GKRAddress}
    {program : FunctionalProgram} (valid : program.Valid isBase known)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (base extension : GKRAddress → R) :
    (∀ step ∈ program, step.Holds hom challenges gamma
      (Functional.read isBase base (program.execute hom challenges gamma isBase base extension))) ∧
    (∀ address, isBase address = true ∨ address ∈ known →
      Functional.read isBase base (program.execute hom challenges gamma isBase base extension) address =
        Functional.read isBase base extension address) := by
  induction valid generalizing extension with
  | nil => exact ⟨by simp, fun _ _ => rfl⟩
  | @cons known step rest stepValid restValid proof =>
      let next := step.execute hom challenges gamma isBase base extension
      have tail := proof next
      have current := step.execute_sound stepValid hom challenges gamma base extension
      have unchanged (address : GKRAddress) (prior : isBase address = true ∨ address ∈ known) :
          Functional.read isBase base (rest.execute hom challenges gamma isBase base next) address =
            Functional.read isBase base extension address :=
        (tail.2 address (prior.imp_right (List.mem_append_right _))).trans
          (step.execute_frame stepValid hom challenges gamma base extension address prior)
      refine ⟨?_, unchanged⟩
      intro actual member
      rcases List.mem_cons.mp member with same | inside
      · subst actual
        apply step.holds_congr hom challenges gamma
          (Functional.read isBase base next) _ _ current
        intro address used
        apply Eq.symm
        apply tail.2
        rcases List.mem_append.mp used with output | input
        · exact .inr (List.mem_append_left _ output)
        · exact (stepValid.inputs address input).imp_right (List.mem_append_right _)
      · exact tail.1 actual inside

end Airbender.Compiler
