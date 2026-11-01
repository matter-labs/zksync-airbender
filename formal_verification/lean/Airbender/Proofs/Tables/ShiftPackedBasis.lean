import Airbender.Proofs.Tables.ShiftPackedBasisData

namespace Airbender.Verification.ShiftPackedReference
open Airbender.Setup.Proofs PackedWordColumn PackedSignedRun
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

def basisCheck : Bool :=
  (List.range 4).all fun position => (List.range 4).all fun lane =>
    (List.range 8).all fun bit => decide (basisRow position lane bit =
      referencePacked (rowByte lane position (2 ^ bit)) 0 256)

theorem basis_checked : basisCheck = true := by decide +kernel

theorem basis_binding (position lane bit : Nat) (positionBound : position < 4)
    (laneBound : lane < 4) (bitBound : bit < 8) :
    basisRow position lane bit = referencePacked (rowByte lane position (2 ^ bit)) 0 256 := by
  have first := List.all_eq_true.mp basis_checked position (List.mem_range.mpr positionBound)
  have second := List.all_eq_true.mp first lane (List.mem_range.mpr laneBound)
  have third := List.all_eq_true.mp second bit (List.mem_range.mpr bitBound)
  exact of_decide_eq_true third

theorem basis_digit (position lane bit control : Nat) (positionBound : position < 4)
    (laneBound : lane < 4) (bitBound : bit < 8) (controlBound : control < 256) :
    digit 65536 (basisRow position lane bit) control = rowByte lane position (2 ^ bit) control := by
  rw [basis_binding position lane bit positionBound laneBound bitBound,
    referencePacked_digit _ 0 256 control controlBound, Nat.zero_add]
  apply Nat.mod_eq_of_lt
  have bounded : rowByte lane position (2 ^ bit) control < 256 := Nat.mod_lt _ (by omega)
  omega

def disjointCheck : Bool :=
  (List.range 4).all fun position => (List.range 4).all fun lane =>
    decide ((List.range 8).Pairwise (fun left right =>
      basisRow position lane left &&& basisRow position lane right = 0))

theorem basis_disjoint_checked : disjointCheck = true := by decide +kernel

theorem basis_disjoint (position lane : Nat) (positionBound : position < 4) (laneBound : lane < 4) :
    (List.range 8).Pairwise (fun left right => basisRow position lane left &&& basisRow position lane right = 0) := by
  have first := List.all_eq_true.mp basis_disjoint_checked position (List.mem_range.mpr positionBound)
  have second := List.all_eq_true.mp first lane (List.mem_range.mpr laneBound)
  exact of_decide_eq_true second

end Airbender.Verification.ShiftPackedReference
