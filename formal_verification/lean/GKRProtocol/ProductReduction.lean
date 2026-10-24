import GKRProtocol.NativeLookup

namespace Airbender.Compiler
set_option warningAsError true

/-- Masks retain their actual input addresses. They are not silently replaced
by Boolean constants or distributed over products. -/
inductive ProductFormula where
  | leaf : Nat → ProductFormula
  | mul : ProductFormula → ProductFormula → ProductFormula
  | mask : GKRAddress → ProductFormula → ProductFormula
  deriving Repr

def ProductFormula.value [CommRing R] (values : GKRAddress → R) (primitive : Nat → R) : ProductFormula → R
  | .leaf index => primitive index
  | .mul left right => left.value values primitive * right.value values primitive
  | .mask address input => maskProduct (values address) (input.value values primitive)

def ProductFormula.leaves : ProductFormula → List Nat
  | .leaf index => [index]
  | .mul left right => left.leaves ++ right.leaves
  | .mask _ input => input.leaves

def ProductFormula.ofTree : ProductTree Nat → ProductFormula
  | .leaf index => .leaf index
  | .mul left right => .mul (ofTree left) (ofTree right)

theorem ProductFormula.ofTree_value [CommRing R] (tree : ProductTree Nat)
    (values : GKRAddress → R) (primitive : Nat → R) :
    (ofTree tree).value values primitive = tree.evaluate primitive := by
  induction tree with
  | leaf index => rfl
  | mul left right leftProof rightProof => exact congrArg₂ (· * ·) leftProof rightProof

theorem maskProduct_mul [CommRing R] (mask left right : R) (boolean : mask * mask = mask) :
    maskProduct mask (left * right) = maskProduct mask left * maskProduct mask right := by
  dsimp [maskProduct]
  apply sub_eq_zero.mp
  calc
    ((left * right - 1) * mask + 1) -
        (((left - 1) * mask + 1) * ((right - 1) * mask + 1)) =
        -(left - 1) * (right - 1) * (mask * mask - mask) := by ring
    _ = 0 := by rw [boolean, sub_self, mul_zero]

abbrev ProductEnvironment := List (GKRAddress × ProductFormula)

def ProductEnvironment.find (address : GKRAddress) : ProductEnvironment → Option ProductFormula
  | [] => none
  | (candidate, formula) :: rest =>
      if addressEqual address candidate then some formula else ProductEnvironment.find address rest

theorem ProductEnvironment.find_member {environment : ProductEnvironment} {address : GKRAddress}
    {formula : ProductFormula} (found : environment.find address = some formula) :
    (address, formula) ∈ environment := by
  induction environment with
  | nil => cases found
  | cons entry rest proof =>
      rcases entry with ⟨candidate, actual⟩
      simp only [find] at found
      split at found
      next same =>
        have equal := (addressEqual_iff _ _).mp same
        cases Option.some.inj found
        subst candidate
        exact List.mem_cons_self
      next different => exact List.mem_cons_of_mem _ (proof found)

def ProductEnvironment.Sound [CommRing R] (environment : ProductEnvironment)
    (values : GKRAddress → R) (primitive : Nat → R) : Prop :=
  ∀ address formula, (address, formula) ∈ environment → values address = formula.value values primitive

theorem ProductEnvironment.insert_sound [CommRing R] {environment : ProductEnvironment}
    {values : GKRAddress → R} {primitive : Nat → R} (sound : environment.Sound values primitive)
    {address : GKRAddress} {formula : ProductFormula} (value : values address = formula.value values primitive) :
    ProductEnvironment.Sound ((address, formula) :: environment) values primitive := by
  intro actual meaning member
  rcases List.mem_cons.mp member with same | member
  · cases same
    exact value
  · exact sound _ _ member

inductive ProductStep where
  | single (output : GKRAddress) (index : Nat)
  | pair (output : GKRAddress) (left right : Nat)
  | mul (output left right : GKRAddress)
  | mask (output input predicate : GKRAddress)
  | copy (output input : GKRAddress)

def ProductStep.Holds [CommRing R] (values : GKRAddress → R) (primitive : Nat → R) : ProductStep → Prop
  | .single output index => values output = primitive index
  | .pair output left right => values output = primitive left * primitive right
  | .mul output left right => values output = values left * values right
  | .mask output input predicate => values output = maskProduct (values predicate) (values input)
  | .copy output input => values output = values input

def ProductStep.advance (environment : ProductEnvironment) : ProductStep → Option ProductEnvironment
  | .single output index => some ((output, .leaf index) :: environment)
  | .pair output left right => some ((output, .mul (.leaf left) (.leaf right)) :: environment)
  | .mul output left right =>
      match environment.find left, environment.find right with
      | some leftTree, some rightTree => some ((output, .mul leftTree rightTree) :: environment)
      | _, _ => none
  | .mask output input predicate =>
      match environment.find input with
      | some tree => some ((output, .mask predicate tree) :: environment)
      | none => none
  | .copy output input =>
      match environment.find input with
      | some tree => some ((output, tree) :: environment)
      | none => some environment

theorem ProductStep.advance_sound [CommRing R] {environment result : ProductEnvironment}
    {values : GKRAddress → R} {primitive : Nat → R} (sound : environment.Sound values primitive)
    {step : ProductStep} (holds : step.Holds values primitive)
    (progressed : step.advance environment = some result) : result.Sound values primitive := by
  cases step with
  | single output index =>
      cases Option.some.inj progressed
      exact ProductEnvironment.insert_sound sound holds
  | pair output left right =>
      cases Option.some.inj progressed
      exact ProductEnvironment.insert_sound sound holds
  | mul output left right =>
      cases leftFound : environment.find left with
      | none => simp [advance, leftFound] at progressed
      | some leftTree =>
          cases rightFound : environment.find right with
          | none => simp [advance, leftFound, rightFound] at progressed
          | some rightTree =>
              simp only [advance, leftFound, rightFound, Option.some.injEq] at progressed
              cases progressed
              apply ProductEnvironment.insert_sound sound
              exact holds.trans (congrArg₂ (· * ·)
                (sound _ _ (ProductEnvironment.find_member leftFound))
                (sound _ _ (ProductEnvironment.find_member rightFound)))
  | mask output input predicate =>
      cases found : environment.find input with
      | none => simp [advance, found] at progressed
      | some tree =>
          simp only [advance, found, Option.some.injEq] at progressed
          cases progressed
          apply ProductEnvironment.insert_sound sound
          exact holds.trans (congrArg (maskProduct (values predicate))
            (sound _ _ (ProductEnvironment.find_member found)))
  | copy output input =>
      cases found : environment.find input with
      | none =>
          simp only [advance, found, Option.some.injEq] at progressed
          cases progressed
          exact sound
      | some tree =>
          simp only [advance, found, Option.some.injEq] at progressed
          cases progressed
          exact ProductEnvironment.insert_sound sound
            (holds.trans (sound _ _ (ProductEnvironment.find_member found)))

def ProductStep.run : List ProductStep → ProductEnvironment → Option ProductEnvironment
  | [], environment => some environment
  | step :: rest, environment =>
      match step.advance environment with
      | none => none
      | some next => ProductStep.run rest next

theorem ProductStep.run_sound [CommRing R] {steps : List ProductStep}
    {values : GKRAddress → R} {primitive : Nat → R}
    (holds : ∀ step ∈ steps, step.Holds values primitive)
    {environment result : ProductEnvironment} (sound : environment.Sound values primitive)
    (replayed : ProductStep.run steps environment = some result) : result.Sound values primitive := by
  induction steps generalizing environment result with
  | nil =>
      cases Option.some.inj replayed
      exact sound
  | cons step rest proof =>
      cases progressed : step.advance environment with
      | none => simp [run, progressed] at replayed
      | some next =>
          apply proof (fun item member => holds item (List.mem_cons_of_mem _ member))
            (advance_sound sound (holds step List.mem_cons_self) progressed)
          simpa only [run, progressed] using replayed

theorem ProductStep.output_formula [CommRing R] {steps : List ProductStep}
    {values : GKRAddress → R} {primitive : Nat → R}
    (holds : ∀ step ∈ steps, step.Holds values primitive)
    {result : ProductEnvironment} (replayed : ProductStep.run steps [] = some result)
    {output : GKRAddress} {formula : ProductFormula} (found : result.find output = some formula) :
    values output = formula.value values primitive :=
  run_sound holds (by intro address meaning member; cases member) replayed _ _
    (ProductEnvironment.find_member found)

end Airbender.Compiler
