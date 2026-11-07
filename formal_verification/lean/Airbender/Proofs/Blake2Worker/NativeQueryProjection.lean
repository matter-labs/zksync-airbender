import Airbender.Review.Circuits.Blake2Worker.Queries
import Airbender.Proofs.Constraints

namespace Airbender.Blake2Worker.QueryProofs
open Verification Native QueryArtifact
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

/-- Both intakes retain identical complete native source bytes; no source equality is an assumption. -/
theorem same_source : querySourceBytes = constraintsSourceBytes := rfl

theorem typed_membership {p : Nat} [Fact p.Prime] (setup : Table (ZMod p) (fields 4))
    (entries : Vector (Expression (ZMod p)) 4) (w : Nat → ZMod p)
    (holds : (Lookup.mk setup.toRaw entries).Contains (environment w)) :
    setup.Contains #[] (entries.map (Expression.eval (environment w))) := by
  simpa [Lookup.Contains,Table.toRaw,environment,ProvableType.fromElements] using holds

theorem block5 {p : Nat} [Fact p.Prime] {setup : Table (ZMod p) (fields 4)}
    {w : Nat → ZMod p}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (constraints setup)) :
    FlatOperation.ConstraintsHoldFlat (environment w) (constraintsBlock5 setup) := by
  apply holds_of_sublist holds
  have base : (constraintsBlock5 setup).Sublist ([] ++ constraintsBlock0 setup ++ constraintsBlock1 setup ++ constraintsBlock2 setup ++ constraintsBlock3 setup ++ constraintsBlock4 setup ++ constraintsBlock5 setup) := List.sublist_append_right _ _
  exact (((((base.trans (List.sublist_append_left _ _)).trans (List.sublist_append_left _ _)).trans (List.sublist_append_left _ _)).trans (List.sublist_append_left _ _)).trans (List.sublist_append_left _ _))

theorem block6 {p : Nat} [Fact p.Prime] {setup : Table (ZMod p) (fields 4)}
    {w : Nat → ZMod p}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (constraints setup)) :
    FlatOperation.ConstraintsHoldFlat (environment w) (constraintsBlock6 setup) := by
  apply holds_of_sublist holds
  have base : (constraintsBlock6 setup).Sublist ([] ++ constraintsBlock0 setup ++ constraintsBlock1 setup ++ constraintsBlock2 setup ++ constraintsBlock3 setup ++ constraintsBlock4 setup ++ constraintsBlock5 setup ++ constraintsBlock6 setup) := List.sublist_append_right _ _
  exact ((((base.trans (List.sublist_append_left _ _)).trans (List.sublist_append_left _ _)).trans (List.sublist_append_left _ _)).trans (List.sublist_append_left _ _))

theorem block7 {p : Nat} [Fact p.Prime] {setup : Table (ZMod p) (fields 4)}
    {w : Nat → ZMod p}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (constraints setup)) :
    FlatOperation.ConstraintsHoldFlat (environment w) (constraintsBlock7 setup) := by
  apply holds_of_sublist holds
  have base : (constraintsBlock7 setup).Sublist ([] ++ constraintsBlock0 setup ++ constraintsBlock1 setup ++ constraintsBlock2 setup ++ constraintsBlock3 setup ++ constraintsBlock4 setup ++ constraintsBlock5 setup ++ constraintsBlock6 setup ++ constraintsBlock7 setup) := List.sublist_append_right _ _
  exact (((base.trans (List.sublist_append_left _ _)).trans (List.sublist_append_left _ _)).trans (List.sublist_append_left _ _))

theorem block8 {p : Nat} [Fact p.Prime] {setup : Table (ZMod p) (fields 4)}
    {w : Nat → ZMod p}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (constraints setup)) :
    FlatOperation.ConstraintsHoldFlat (environment w) (constraintsBlock8 setup) := by
  apply holds_of_sublist holds
  have base : (constraintsBlock8 setup).Sublist ([] ++ constraintsBlock0 setup ++ constraintsBlock1 setup ++ constraintsBlock2 setup ++ constraintsBlock3 setup ++ constraintsBlock4 setup ++ constraintsBlock5 setup ++ constraintsBlock6 setup ++ constraintsBlock7 setup ++ constraintsBlock8 setup) := List.sublist_append_right _ _
  exact ((base.trans (List.sublist_append_left _ _)).trans (List.sublist_append_left _ _))

theorem block9 {p : Nat} [Fact p.Prime] {setup : Table (ZMod p) (fields 4)}
    {w : Nat → ZMod p}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (constraints setup)) :
    FlatOperation.ConstraintsHoldFlat (environment w) (constraintsBlock9 setup) := by
  apply holds_of_sublist holds
  have base : (constraintsBlock9 setup).Sublist ([] ++ constraintsBlock0 setup ++ constraintsBlock1 setup ++ constraintsBlock2 setup ++ constraintsBlock3 setup ++ constraintsBlock4 setup ++ constraintsBlock5 setup ++ constraintsBlock6 setup ++ constraintsBlock7 setup ++ constraintsBlock8 setup ++ constraintsBlock9 setup) := List.sublist_append_right _ _
  exact (base.trans (List.sublist_append_left _ _))

theorem block10 {p : Nat} [Fact p.Prime] {setup : Table (ZMod p) (fields 4)}
    {w : Nat → ZMod p}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (constraints setup)) :
    FlatOperation.ConstraintsHoldFlat (environment w) (constraintsBlock10 setup) := by
  apply holds_of_sublist holds
  have base : (constraintsBlock10 setup).Sublist ([] ++ constraintsBlock0 setup ++ constraintsBlock1 setup ++ constraintsBlock2 setup ++ constraintsBlock3 setup ++ constraintsBlock4 setup ++ constraintsBlock5 setup ++ constraintsBlock6 setup ++ constraintsBlock7 setup ++ constraintsBlock8 setup ++ constraintsBlock9 setup ++ constraintsBlock10 setup) := List.sublist_append_right _ _
  exact base

end Airbender.Blake2Worker.QueryProofs
