import Airbender.Proofs.GKRProtocol.RationalSemantics
import Airbender.Proofs.GKRCompiler.Wiring

namespace Airbender.Compiler
set_option warningAsError true

theorem option_eq_some_getD {value : Option α} (present : value.isSome = true) (fallback : α) :
    value = some (value.getD fallback) := by
  cases value with
  | none => cases present
  | some actual => rfl

structure RationalPorts where
  numerator : GKRAddress
  denominator : GKRAddress
  deriving Repr, DecidableEq

def RationalPorts.value (ports : RationalPorts) (values : GKRAddress → R) : RationalPair R :=
  ⟨values ports.numerator, values ports.denominator⟩

def LookupTree.same : LookupTree Nat → LookupTree Nat → Bool
  | .leaf left, .leaf right => left == right
  | .add left right, .add otherLeft otherRight => left.same otherLeft && right.same otherRight
  | _, _ => false

theorem LookupTree.same_sound {left right : LookupTree Nat} (checked : left.same right = true) :
    left = right := by
  induction left generalizing right with
  | leaf item =>
      cases right with
      | leaf other => simpa only [same, beq_iff_eq, leaf.injEq] using checked
      | add _ _ => cases checked
  | add leftChild rightChild leftProof rightProof =>
      cases right with
      | leaf _ => cases checked
      | add otherLeft otherRight =>
          have parts : leftChild.same otherLeft = true ∧ rightChild.same otherRight = true := by
            simpa only [same, Bool.and_eq_true] using checked
          exact congrArg₂ LookupTree.add (leftProof parts.1) (rightProof parts.2)

structure LookupMeaning where
  tree : LookupTree Nat
  denominator : Bool

def LookupMeaning.value [CommRing R] (meaning : LookupMeaning) (primitive : Nat → RationalPair R) : R :=
  if meaning.denominator then (meaning.tree.evaluate primitive).denominator
  else (meaning.tree.evaluate primitive).numerator

abbrev LookupEnvironment := List (GKRAddress × LookupMeaning)

def LookupEnvironment.same : LookupEnvironment → LookupEnvironment → Bool
  | [], [] => true
  | (leftAddress, left) :: leftRest, (rightAddress, right) :: rightRest =>
      addressEqual leftAddress rightAddress && (left.denominator == right.denominator) &&
        left.tree.same right.tree && LookupEnvironment.same leftRest rightRest
  | _, _ => false

theorem LookupEnvironment.same_sound {left right : LookupEnvironment} (checked : same left right = true) :
    left = right := by
  induction left generalizing right with
  | nil => cases right <;> first | rfl | cases checked
  | cons entry rest proof =>
    rcases entry with ⟨address, ⟨tree, flag⟩⟩
    cases right with
    | nil => cases checked
    | cons other otherRest =>
      rcases other with ⟨otherAddress, ⟨otherTree, otherFlag⟩⟩
      have parts : ((address = otherAddress ∧ flag = otherFlag) ∧ tree.same otherTree = true) ∧
          same rest otherRest = true := by
        simpa only [same, Bool.and_eq_true, addressEqual_iff, beq_iff_eq] using checked
      exact congrArg₂ List.cons
        (congrArg₂ Prod.mk parts.1.1.1 (congrArg₂ LookupMeaning.mk (LookupTree.same_sound parts.1.2) parts.1.1.2))
        (proof parts.2)

def LookupEnvironment.checkResult (actual : Option LookupEnvironment) (expected : LookupEnvironment) : Bool :=
  match actual with
  | none => false
  | some environment => same environment expected

theorem LookupEnvironment.checkResult_sound {actual : Option LookupEnvironment} {expected : LookupEnvironment}
    (checked : checkResult actual expected = true) : actual = some expected := by
  cases actual with
  | none => cases checked
  | some environment => exact congrArg some (same_sound checked)

def LookupEnvironment.find (address : GKRAddress) : LookupEnvironment → Option LookupMeaning
  | [] => none
  | (candidate, meaning) :: rest =>
      if addressEqual address candidate then some meaning else LookupEnvironment.find address rest

theorem LookupEnvironment.find_member {environment : LookupEnvironment} {address : GKRAddress}
    {meaning : LookupMeaning} (found : environment.find address = some meaning) :
    (address, meaning) ∈ environment := by
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

def LookupEnvironment.Sound [CommRing R] (environment : LookupEnvironment)
    (values : GKRAddress → R) (primitive : Nat → RationalPair R) : Prop :=
  ∀ address meaning, (address, meaning) ∈ environment → values address = meaning.value primitive

def LookupEnvironment.pair (environment : LookupEnvironment) (ports : RationalPorts) : Option (LookupTree Nat) := do
  let numerator ← environment.find ports.numerator
  let denominator ← environment.find ports.denominator
  if (numerator.denominator == false) && denominator.denominator && numerator.tree.same denominator.tree then
    some numerator.tree
  else none

theorem LookupEnvironment.pair_sound [CommRing R] {environment : LookupEnvironment}
    {values : GKRAddress → R} {primitive : Nat → RationalPair R}
    (sound : environment.Sound values primitive) {ports : RationalPorts} {tree : LookupTree Nat}
    (found : environment.pair ports = some tree) : ports.value values = tree.evaluate primitive := by
  unfold pair at found
  cases numeratorFound : environment.find ports.numerator with
  | none => simp [numeratorFound] at found
  | some numerator =>
    cases denominatorFound : environment.find ports.denominator with
    | none => simp [numeratorFound, denominatorFound] at found
    | some denominator =>
      simp only [numeratorFound, denominatorFound, Option.bind_eq_bind, Option.bind_some] at found
      split at found
      next checked =>
        have parts : (numerator.denominator = false ∧ denominator.denominator = true) ∧
            numerator.tree.same denominator.tree = true := by
          simpa only [Bool.and_eq_true, beq_iff_eq] using checked
        have numeratorRole : numerator.denominator = false := parts.1.1
        have denominatorRole : denominator.denominator = true := parts.1.2
        have same := LookupTree.same_sound parts.2
        have selected := Option.some.inj found
        have hn : values ports.numerator = (numerator.tree.evaluate primitive).numerator := by
          simpa [LookupMeaning.value, numeratorRole] using sound _ _ (find_member numeratorFound)
        have hd : values ports.denominator = (denominator.tree.evaluate primitive).denominator := by
          simpa [LookupMeaning.value, denominatorRole] using sound _ _ (find_member denominatorFound)
        rw [← selected]
        change RationalPair.mk _ _ = RationalPair.mk _ _
        apply congrArg₂ RationalPair.mk hn
        exact hd.trans (congrArg (fun item => (item.evaluate primitive).denominator) same.symm)
      next rejected => cases found

def LookupEnvironment.insertPair (environment : LookupEnvironment) (ports : RationalPorts)
    (tree : LookupTree Nat) : LookupEnvironment :=
  (ports.numerator, ⟨tree, false⟩) :: (ports.denominator, ⟨tree, true⟩) :: environment

theorem LookupEnvironment.insertPair_sound [CommRing R] {environment : LookupEnvironment}
    {values : GKRAddress → R} {primitive : Nat → RationalPair R}
    (sound : environment.Sound values primitive) {ports : RationalPorts} {tree : LookupTree Nat}
    (value : ports.value values = tree.evaluate primitive) :
    (environment.insertPair ports tree).Sound values primitive := by
  intro address meaning member
  simp only [insertPair, List.mem_cons] at member
  rcases member with same | same | member
  · cases same
    exact congrArg RationalPair.numerator value
  · cases same
    exact congrArg RationalPair.denominator value
  · exact sound _ _ member

/-- The finite reduction instructions retain actual output and input ports.
Primitive IDs are assigned to actual native leaf operands, before matching
them to independently reconstructed source requests. -/
inductive LookupStep where
  | seed (output : RationalPorts) (left right : Nat)
  | add (output left right : RationalPorts)
  | extend (output input : RationalPorts) (remainder : Nat)
  | copy (output input : GKRAddress)

def LookupStep.Holds [CommRing R] (values : GKRAddress → R)
    (primitive : Nat → RationalPair R) : LookupStep → Prop
  | .seed output left right => output.value values = (primitive left).add (primitive right)
  | .add output left right => output.value values = (left.value values).add (right.value values)
  | .extend output input remainder => output.value values = (input.value values).add (primitive remainder)
  | .copy output input => values output = values input

def LookupStep.advance (environment : LookupEnvironment) : LookupStep → Option LookupEnvironment
  | .seed output left right => some (environment.insertPair output (.add (.leaf left) (.leaf right)))
  | .add output left right =>
      match environment.pair left, environment.pair right with
      | some leftTree, some rightTree => some (environment.insertPair output (.add leftTree rightTree))
      | _, _ => none
  | .extend output input remainder =>
      match environment.pair input with
      | some inputTree => some (environment.insertPair output (.add inputTree (.leaf remainder)))
      | none => none
  | .copy output input =>
      match environment.find input with
      | none => some environment
      | some meaning => some ((output, meaning) :: environment)

theorem LookupStep.advance_sound [CommRing R] {environment result : LookupEnvironment}
    {values : GKRAddress → R} {primitive : Nat → RationalPair R}
    (sound : environment.Sound values primitive) {step : LookupStep}
    (holds : step.Holds values primitive) (progressed : step.advance environment = some result) :
    result.Sound values primitive := by
  cases step with
  | seed output left right =>
      simp only [advance, Option.some.injEq] at progressed
      cases progressed
      exact LookupEnvironment.insertPair_sound sound holds
  | add output left right =>
      cases leftFound : environment.pair left with
      | none => simp [advance, leftFound] at progressed
      | some leftTree =>
        cases rightFound : environment.pair right with
        | none => simp [advance, leftFound, rightFound] at progressed
        | some rightTree =>
          simp only [advance, leftFound, rightFound, Option.some.injEq] at progressed
          cases progressed
          apply LookupEnvironment.insertPair_sound sound
          exact holds.trans (congrArg₂ RationalPair.add
            (LookupEnvironment.pair_sound sound leftFound)
            (LookupEnvironment.pair_sound sound rightFound))
  | extend output input remainder =>
      cases inputFound : environment.pair input with
      | none => simp [advance, inputFound] at progressed
      | some inputTree =>
        simp only [advance, inputFound, Option.some.injEq] at progressed
        cases progressed
        apply LookupEnvironment.insertPair_sound sound
        exact holds.trans (congrArg (fun pair => pair.add (primitive remainder))
          (LookupEnvironment.pair_sound sound inputFound))
  | copy output input =>
      cases inputFound : environment.find input with
      | none =>
        simp only [advance, inputFound, Option.some.injEq] at progressed
        cases progressed
        exact sound
      | some meaning =>
        simp only [advance, inputFound, Option.some.injEq] at progressed
        cases progressed
        intro address actual member
        simp only [List.mem_cons] at member
        rcases member with same | member
        · cases same
          exact holds.trans (sound _ _ (LookupEnvironment.find_member inputFound))
        · exact sound _ _ member

def LookupStep.run : List LookupStep → LookupEnvironment → Option LookupEnvironment
  | [], environment => some environment
  | step :: rest, environment =>
      match step.advance environment with
      | none => none
      | some next => LookupStep.run rest next

theorem LookupStep.run_sound [CommRing R] {steps : List LookupStep}
    {values : GKRAddress → R} {primitive : Nat → RationalPair R}
    (holds : ∀ step ∈ steps, step.Holds values primitive)
    {environment result : LookupEnvironment} (sound : environment.Sound values primitive)
    (replayed : LookupStep.run steps environment = some result) : result.Sound values primitive := by
  induction steps generalizing environment result with
  | nil =>
      simp only [run, Option.some.injEq] at replayed
      cases replayed
      exact sound
  | cons step rest proof =>
      cases progressed : step.advance environment with
      | none => simp [run, progressed] at replayed
      | some next =>
        apply proof (fun item member => holds item (List.mem_cons_of_mem _ member))
          (advance_sound sound (holds step List.mem_cons_self) progressed)
        simpa only [run, progressed] using replayed

/-- Exact reduction follows the actual ports through copies, balanced pairs and
unbalanced remainders. Coverage is an exact multiset, not set inclusion. -/
theorem LookupStep.source_sum [CommRing R] {steps : List LookupStep}
    {values : GKRAddress → R} {primitive : Nat → RationalPair R}
    (holds : ∀ step ∈ steps, step.Holds values primitive)
    {result : LookupEnvironment} (replayed : LookupStep.run steps [] = some result)
    {output : RationalPorts} {tree : LookupTree Nat} (root : result.pair output = some tree)
    {source : List Nat} (coverage : tree.leaves.Perm source) :
    output.value values = (source.map primitive).sum := by
  have sound := run_sound holds (by intro address meaning member; cases member) replayed
  exact (LookupEnvironment.pair_sound sound root).trans (tree.exact_source primitive source coverage)

theorem LookupStep.source_translation [CommRing R] {steps : List LookupStep}
    {values : GKRAddress → R} {primitive sourcePrimitive : Nat → RationalPair R}
    (holds : ∀ step ∈ steps, step.Holds values primitive)
    {result : LookupEnvironment} (replayed : LookupStep.run steps [] = some result)
    {output : RationalPorts} {tree : LookupTree Nat} (root : result.pair output = some tree)
    (label : Nat → Nat) (fields : ∀ index ∈ tree.leaves, primitive index = sourcePrimitive (label index))
    {source : List Nat} (coverage : (tree.leaves.map label).Perm source) :
    output.value values = (source.map sourcePrimitive).sum := by
  have sound := run_sound holds (by intro address meaning member; cases member) replayed
  have native := (LookupEnvironment.pair_sound sound root).trans (tree.exact_sum primitive)
  have same : tree.leaves.map primitive = (tree.leaves.map label).map sourcePrimitive := by
    rw [List.map_map]
    exact List.map_congr_left fields
  rw [same, (coverage.map sourcePrimitive).sum_eq] at native
  exact native

end Airbender.Compiler
