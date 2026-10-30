import Airbender.Proofs.Keccak.SplitSetupTransport

namespace Airbender.Keccak.Split.Native.Proofs
open Trace
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000
set_option Elab.async false
variable [Fact babyBearModulus.Prime]

/-- Chi5 transport covers its two real query tags. Physical padding remains
in the source setup. The canonical table keeps its original real domain. -/
structure TaggedSetupRefinement (source target : Setup babyBearModulus) : Prop where
  columnParity : ∀ row, source.columnParity.toRaw.Soundness #[] row → target.columnParity.toRaw.Contains #[] row
  thetaRho : ∀ row, source.thetaRho.toRaw.Soundness #[] row → target.thetaRho.toRaw.Contains #[] row
  chi5 : ∀ row : Vector (ZMod babyBearModulus) 11, source.chi5.toRaw.Soundness #[] row →
    (row[10] = 65 ∨ row[10] = 66) → target.chi5.toRaw.Contains #[] row

private theorem lookup_transport {width : Nat} {source target : Table (ZMod babyBearModulus) (fields width)}
    (refines : ∀ row, source.toRaw.Soundness #[] row → target.toRaw.Contains #[] row)
    (entry : Vector (Expression (ZMod babyBearModulus)) width) (w : Nat → ZMod babyBearModulus) :
    (Lookup.mk source.toRaw entry).Contains (Verification.environment w) →
      (Lookup.mk target.toRaw entry).Contains (Verification.environment w) := by
  intro member
  exact refines _ (source.toRaw.imply_soundness _ _ member)

private theorem chi_lookup_transport {source target : Table (ZMod babyBearModulus) (fields 11)}
    (refines : ∀ row : Vector (ZMod babyBearModulus) 11, source.toRaw.Soundness #[] row →
      (row[10] = 65 ∨ row[10] = 66) → target.toRaw.Contains #[] row)
    (entry : Vector (Expression (ZMod babyBearModulus)) 11) (w : Nat → ZMod babyBearModulus)
    (tag : (entry.map (Expression.eval (Verification.environment w)))[10] = 65 ∨
      (entry.map (Expression.eval (Verification.environment w)))[10] = 66) :
    (Lookup.mk source.toRaw entry).Contains (Verification.environment w) →
      (Lookup.mk target.toRaw entry).Contains (Verification.environment w) := by
  intro member
  exact refines _ (source.toRaw.imply_soundness _ _ member) tag

private theorem row_lookup_transport {source target : Setup babyBearModulus}
    (refines : TaggedSetupRefinement source target) (cached : Bool) (row : Row babyBearModulus) :
    List.Forall₂ (fun left right => left.Contains (Verification.environment row.assignment) →
      right.Contains (Verification.environment row.assignment))
      (FlatOperation.lookups (row.constraints cached source))
      (FlatOperation.lookups (row.constraints cached target)) := by
  cases cached <;> cases kind : row.kind
  all_goals simp only [Row.constraints, kind]
  all_goals
    repeat' first | apply List.Forall₂.cons | apply List.Forall₂.nil
    all_goals first
      | exact fun member => member
      | exact lookup_transport refines.columnParity _ _
      | exact lookup_transport refines.thetaRho _ _
      | apply chi_lookup_transport refines.chi5 _ _
        norm_num [Vector.getElem_map, Fin.getElem_fin, Expression.eval, Verification.environment]

omit [Fact babyBearModulus.Prime] in
private theorem forall_mem_transport {α : Type} {P : α → Prop} {left right : List α}
    (related : List.Forall₂ (fun a b => P a → P b) left right)
    (holds : ∀ a ∈ left, P a) : ∀ b ∈ right, P b := by
  induction related with
  | nil => intro b member; exact False.elim (List.not_mem_nil member)
  | @cons a b left right relation _ ih =>
    intro entry member
    rcases List.mem_cons.mp member with rfl | member
    · exact relation (holds _ List.mem_cons_self)
    · exact ih (fun entry member => holds entry (List.mem_cons_of_mem _ member)) entry member

theorem equations_of_tagged_setup_refinement {source target : Setup babyBearModulus}
    (refines : TaggedSetupRefinement source target) {cached : Bool} {rows : List (Row babyBearModulus)}
    (holds : EquationsHold cached source rows) : EquationsHold cached target rows := by
  constructor
  intro row member
  have sourceHolds := FlatOperation.constraintsHoldFlat_iff_forall_mem.mp (holds.rowsHold row member)
  apply FlatOperation.constraintsHoldFlat_iff_forall_mem.mpr
  constructor
  · have same : FlatOperation.constraints (row.constraints cached target) =
        FlatOperation.constraints (row.constraints cached source) := by
      cases cached <;> cases kind : row.kind <;> simp only [Row.constraints, kind] <;> rfl
    rw [same]
    exact sourceHolds.1
  · exact forall_mem_transport (row_lookup_transport refines cached row) sourceHolds.2

theorem control_of_fixed_tagged_setup_refinement {source : Setup babyBearModulus}
    (refines : TaggedSetupRefinement source fixedSetup) : ControlSetupFacts source := by
  constructor
  · intro row member tag active
    exact fixed_control_setup_facts.thetaRho row
      (fixedSetup.thetaRho.toRaw.imply_soundness _ _ (refines.thetaRho row member)) tag active
  · intro row member tag active
    exact fixed_control_setup_facts.chi5 row
      (fixedSetup.chi5.toRaw.imply_soundness _ _ (refines.chi5 row member (Or.inr tag))) tag active

end Airbender.Keccak.Split.Native.Proofs
