import Airbender.Proofs.Keccak.SplitNativeSetup

namespace Airbender.Keccak.Split.Native.Proofs
open Trace
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000
set_option Elab.async false
variable [Fact babyBearModulus.Prime]

/-- Each source-table query belongs to the complete fixed native table. -/
structure SetupRefinement (source target : Setup babyBearModulus) : Prop where
  columnParity : ∀ row, source.columnParity.toRaw.Soundness #[] row →
    target.columnParity.toRaw.Contains #[] row
  thetaRho : ∀ row, source.thetaRho.toRaw.Soundness #[] row →
    target.thetaRho.toRaw.Contains #[] row
  chi5 : ∀ row, source.chi5.toRaw.Soundness #[] row →
    target.chi5.toRaw.Contains #[] row

private theorem lookup_transport {width : Nat}
    {source target : Table (ZMod babyBearModulus) (fields width)}
    (refines : ∀ row, source.toRaw.Soundness #[] row → target.toRaw.Contains #[] row)
    (entry : Vector (Expression (ZMod babyBearModulus)) width)
    (w : Nat → ZMod babyBearModulus) :
    (Lookup.mk source.toRaw entry).Contains (Verification.environment w) →
      (Lookup.mk target.toRaw entry).Contains (Verification.environment w) := by
  intro member
  exact refines _ (source.toRaw.imply_soundness _ _ member)

private theorem row_lookup_transport {source target : Setup babyBearModulus}
    (refines : SetupRefinement source target) (cached : Bool) (row : Row babyBearModulus) :
    List.Forall₂ (fun left right =>
      left.Contains (Verification.environment row.assignment) →
        right.Contains (Verification.environment row.assignment))
      (FlatOperation.lookups (row.constraints cached source))
      (FlatOperation.lookups (row.constraints cached target)) := by
  cases cached <;> cases kind : row.kind
  all_goals
    simp only [Row.constraints, kind]
  all_goals
    repeat' first | apply List.Forall₂.cons | apply List.Forall₂.nil
    all_goals first
      | exact fun member => member
      | exact lookup_transport refines.columnParity _ _
      | exact lookup_transport refines.thetaRho _ _
      | exact lookup_transport refines.chi5 _ _

omit [Fact babyBearModulus.Prime] in
private theorem forall_mem_transport {α : Type} {P : α → Prop} {left right : List α}
    (related : List.Forall₂ (fun a b => P a → P b) left right)
    (holds : ∀ a ∈ left, P a) : ∀ b ∈ right, P b := by
  induction related with
  | nil => intro b member; exact False.elim (List.not_mem_nil member)
  | @cons a b left right relation _ ih =>
    intro entry member
    rcases List.mem_cons.mp member with rfl | member
    · exact relation (holds _ (List.mem_cons_self))
    · exact ih (fun entry member => holds entry (List.mem_cons_of_mem _ member)) entry member

/-- Both cache modes retain every assertion and timestamp query. Only fixed
lookup membership changes, through the proved source-table refinement. -/
theorem equations_of_setup_refinement {source target : Setup babyBearModulus}
    (refines : SetupRefinement source target) {cached : Bool} {rows : List (Row babyBearModulus)}
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

/-- Complete fixed-table refinement supplies the native controller facts. -/
theorem control_of_fixed_setup_refinement {source : Setup babyBearModulus}
    (refines : SetupRefinement source fixedSetup) : ControlSetupFacts source := by
  constructor
  · intro row member tag active
    exact fixed_control_setup_facts.thetaRho row
      (fixedSetup.thetaRho.toRaw.imply_soundness _ _ (refines.thetaRho row member)) tag active
  · intro row member tag active
    exact fixed_control_setup_facts.chi5 row
      (fixedSetup.chi5.toRaw.imply_soundness _ _ (refines.chi5 row member)) tag active

end Airbender.Keccak.Split.Native.Proofs
