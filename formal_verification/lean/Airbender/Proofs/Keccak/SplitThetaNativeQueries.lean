import Airbender.Proofs.Keccak.SplitThetaGenericMembers
import Airbender.Review.Circuits.Keccak.SplitThetaRho
import Airbender.Review.Circuits.Keccak.SplitThetaRhoCached
import Airbender.Proofs.Constraints
import Airbender.Review.Helpers.Properties

namespace Airbender.Keccak.Split.Native.Proofs
set_option warningAsError true
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
variable [Fact babyBearModulus.Prime]

/-- The retained complete physical native generic setup. -/
def thetaRhoFixedTable : Table (ZMod babyBearModulus) (fields 9) := Fixed.thetaRhoPhysicalGenericTable

/-- All fifty actual generic lookups, in their native order. -/
def thetaRhoQuery (cached : Bool) (index : Fin 50) : Lookup (ZMod babyBearModulus) :=
  match cached with
  | false => (FlatOperation.lookups (ThetaRho.importedConstraints thetaRhoFixedTable)).get
      ⟨index.val, by change index.val < 50; exact index.isLt⟩
  | true => (FlatOperation.lookups (ThetaRhoCached.importedConstraints thetaRhoFixedTable)).get
      ⟨index.val, by change index.val < 50; exact index.isLt⟩

theorem theta_rho_query_table (cached : Bool) (index : Fin 50) :
    (thetaRhoQuery cached index).table = thetaRhoFixedTable.toRaw := by
  cases cached <;> fin_cases index <;> rfl

theorem theta_rho_query_arity (cached : Bool) (index : Fin 50) :
    (thetaRhoQuery cached index).table.arity = 9 := by
  rw [theta_rho_query_table]
  rfl

def thetaRhoQueryEntry (cached : Bool) (index : Fin 50) :
    Vector (Expression (ZMod babyBearModulus)) 9 :=
  (thetaRhoQuery cached index).entry.cast (theta_rho_query_arity cached index)

theorem theta_rho_query_shape (cached : Bool) (index : Fin 50) :
    thetaRhoQuery cached index = Lookup.mk thetaRhoFixedTable.toRaw (thetaRhoQueryEntry cached index) := by
  cases cached <;> fin_cases index <;> rfl

/-- Native fixed discriminators distinguish both controllers and both arithmetic regions. -/
def thetaRhoQueryTag (index : Fin 50) : Nat :=
  if index.val = 0 then 60 else if index.val < 9 then 4 else if index.val = 9 then 59 else 58

theorem theta_rho_query_tag (cached : Bool) (index : Fin 50) (w : Nat → ZMod babyBearModulus) :
    (thetaRhoQueryEntry cached index)[8].eval (Verification.environment w) =
      (thetaRhoQueryTag index : ZMod babyBearModulus) := by
  cases cached <;> fin_cases index <;> rfl

/-- Satisfaction of either complete native capture enforces every actual generic query. -/
theorem theta_rho_native_query (cached : Bool) (w : Nat → ZMod babyBearModulus)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (if cached then ThetaRhoCached.clockConstraints thetaRhoFixedTable
        else ThetaRho.clockConstraints thetaRhoFixedTable))
    (index : Fin 50) : Fixed.thetaRhoPhysicalGenericTable.toRaw.Soundness #[]
      ((thetaRhoQueryEntry cached index).map (Expression.eval (Verification.environment w))) := by
  have member : (thetaRhoQuery cached index).Contains (Verification.environment w) := by
    cases cached
    · exact Verification.lookup_of_holds (Verification.holds_of_sublist holds
        (List.sublist_append_left _ _)) ⟨index.val, by change index.val < 50; exact index.isLt⟩
    · exact Verification.lookup_of_holds (Verification.holds_of_sublist holds
        (List.sublist_append_left _ _)) ⟨index.val, by change index.val < 50; exact index.isLt⟩
  rw [theta_rho_query_shape] at member
  exact (Lookup.mk thetaRhoFixedTable.toRaw (thetaRhoQueryEntry cached index)).table.imply_soundness _ _ member

/-- Every actual byte-XOR query enforces its exact operation and all physical fields. -/
theorem theta_rho_native_xor_queries (cached : Bool) (w : Nat → ZMod babyBearModulus)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (if cached then ThetaRhoCached.clockConstraints thetaRhoFixedTable
        else ThetaRho.clockConstraints thetaRhoFixedTable)) (index : Fin 8) :
    let row := (thetaRhoQueryEntry cached ⟨1 + index.val, by omega⟩).map
      (Expression.eval (Verification.environment w))
    row[0].val < 256 ∧ row[1].val < 256 ∧ row[2].val < 256 ∧
      row[2].val = row[0].val ^^^ row[1].val ∧
      (∀ column : Fin 5, row[3 + column.val] = 0) ∧ row[8] = 4 := by
  let query : Fin 50 := ⟨1 + index.val, by omega⟩
  have sound := theta_rho_native_query cached w holds query
  have tag : (((thetaRhoQueryEntry cached query).map
      (Expression.eval (Verification.environment w)))[8]) = 4 := by
    have native := theta_rho_query_tag cached query w
    have selected : thetaRhoQueryTag query = 4 := by fin_cases index <;> rfl
    simpa only [Vector.getElem_map, selected, Nat.cast_ofNat] using native
  exact Fixed.Proofs.xor_byte_table_sound _
    ((Fixed.Proofs.theta_rho_physical_generic_bindings _ sound).1 tag)

/-- All forty actual fragment queries enforce the selected shifted XOR and every physical field. -/
theorem theta_rho_native_split_queries (cached : Bool) (w : Nat → ZMod babyBearModulus)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (if cached then ThetaRhoCached.clockConstraints thetaRhoFixedTable
        else ThetaRho.clockConstraints thetaRhoFixedTable)) (index : Fin 40) :
    let row := (thetaRhoQueryEntry cached ⟨10 + index.val, by omega⟩).map
      (Expression.eval (Verification.environment w))
    row[0].val < 256 ∧ row[1].val < 256 ∧ row[2].val < 8 ∧
      row[3].val < 256 ∧ row[4].val < 256 ∧
      row[3].val = (row[0].val ^^^ row[1].val) * 2 ^ row[2].val % 256 ∧
      row[4].val = (row[0].val ^^^ row[1].val) / 2 ^ (8 - row[2].val) ∧
      (∀ column : Fin 3, row[5 + column.val] = 0) ∧ row[8] = 58 := by
  let query : Fin 50 := ⟨10 + index.val, by omega⟩
  have sound := theta_rho_native_query cached w holds query
  have tag : (((thetaRhoQueryEntry cached query).map
      (Expression.eval (Verification.environment w)))[8]) = 58 := by
    have native := theta_rho_query_tag cached query w
    have selected : thetaRhoQueryTag query = 58 := by fin_cases index <;> rfl
    simpa only [Vector.getElem_map, selected, Nat.cast_ofNat] using native
  exact Fixed.Proofs.theta_split_table_sound _
    ((Fixed.Proofs.theta_rho_physical_generic_bindings _ sound).2.1 tag)

/-- The actual slot query supplies exact membership in the complete native slot region. -/
theorem theta_rho_native_slot_query (cached : Bool) (w : Nat → ZMod babyBearModulus)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (if cached then ThetaRhoCached.clockConstraints thetaRhoFixedTable
        else ThetaRho.clockConstraints thetaRhoFixedTable)) :
    (Fixed.thetaRhoSlots.table "Airbender.SplitThetaRhoSlots").toRaw.Soundness #[]
      ((thetaRhoQueryEntry cached 0).map (Expression.eval (Verification.environment w))) := by
  have sound := theta_rho_native_query cached w holds 0
  have tag : (((thetaRhoQueryEntry cached 0).map
      (Expression.eval (Verification.environment w)))[8]) = 60 := by
    have selected : thetaRhoQueryTag 0 = 60 := by rfl
    simpa only [Vector.getElem_map, selected, Nat.cast_ofNat] using theta_rho_query_tag cached 0 w
  exact (Fixed.Proofs.theta_rho_physical_generic_bindings _ sound).2.2.2 tag

/-- The actual control query supplies exact membership in the complete native controller region. -/
theorem theta_rho_native_control_query (cached : Bool) (w : Nat → ZMod babyBearModulus)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (if cached then ThetaRhoCached.clockConstraints thetaRhoFixedTable
        else ThetaRho.clockConstraints thetaRhoFixedTable)) :
    (Fixed.thetaRhoControl.table "Airbender.SplitThetaRhoControl").toRaw.Soundness #[]
      ((thetaRhoQueryEntry cached 9).map (Expression.eval (Verification.environment w))) := by
  have sound := theta_rho_native_query cached w holds 9
  have tag : (((thetaRhoQueryEntry cached 9).map
      (Expression.eval (Verification.environment w)))[8]) = 59 := by
    have selected : thetaRhoQueryTag 9 = 59 := by rfl
    simpa only [Vector.getElem_map, selected, Nat.cast_ofNat] using theta_rho_query_tag cached 9 w
  exact (Fixed.Proofs.theta_rho_physical_generic_bindings _ sound).2.2.1 tag

end Airbender.Keccak.Split.Native.Proofs
