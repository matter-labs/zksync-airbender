import Airbender.Proofs.Keccak.SplitControlRegion
import Airbender.Proofs.Keccak.SplitControlTags

namespace Airbender.Keccak.Split.Native.Fixed.Proofs
open Airbender.Setup
set_option warningAsError true
set_option maxRecDepth 65536

/-- Theta/rho controller membership follows from its complete native generic table. -/
theorem theta_rho_generic_controller_sound [Fact babyBearModulus.Prime]
    (row : Vector (ZMod babyBearModulus) 9)
    (sound : (thetaRhoGeneric.table "Airbender.SplitThetaRhoGeneric").toRaw.Soundness #[] row)
    (tag : row[8] = 59) :
    (thetaRhoControl.table "Airbender.SplitThetaRhoControl").toRaw.Soundness #[] row := by
  change ∃ i : Fin thetaRhoGeneric.length,
    row = (thetaRhoGeneric.row i).map (fun value : Int => (value : ZMod babyBearModulus)) at sound
  obtain ⟨i, rfl⟩ := sound
  have region := theta_rho_controller_field_tag_region i tag
  let j : Fin thetaRhoControl.length := ⟨i.val - 589824, by change i.val - 589824 < 121; omega⟩
  let k : Fin thetaRhoGeneric.length := ⟨589824 + j.val, by
    have bound := j.isLt
    change j.val < 121 at bound
    change 589824 + j.val < 590066
    omega⟩
  have same : k = i := Fin.ext (by dsimp [k, j]; omega)
  have actual := theta_rho_controller_rows_equal j
  change thetaRhoGeneric.row k = thetaRhoControl.row j at actual
  rw [same] at actual
  exact ⟨j, congrArg (fun values : Vector Int 9 => values.map
    (fun value : Int => (value : ZMod babyBearModulus))) actual⟩

/-- Chi5 controller membership follows from its complete native generic table. -/
theorem chi5_generic_controller_sound [Fact babyBearModulus.Prime]
    (row : Vector (ZMod babyBearModulus) 11)
    (sound : (chi5Generic.table "Airbender.SplitChi5Generic").toRaw.Soundness #[] row)
    (tag : row[10] = 66) :
    (chi5Control.table "Airbender.SplitChi5Control").toRaw.Soundness #[] row := by
  change ∃ i : Fin chi5Generic.length,
    row = (chi5Generic.row i).map (fun value : Int => (value : ZMod babyBearModulus)) at sound
  obtain ⟨i, rfl⟩ := sound
  have region := chi5_controller_field_tag_region i tag
  let j : Fin chi5Control.length := ⟨i.val - 1048576, by change i.val - 1048576 < 121; omega⟩
  let k : Fin chi5Generic.length := ⟨1048576 + j.val, by
    have bound := j.isLt
    change j.val < 121 at bound
    change 1048576 + j.val < 1048697
    omega⟩
  have same : k = i := Fin.ext (by dsimp [k, j]; omega)
  have actual := chi5_controller_rows_equal j
  change chi5Generic.row k = chi5Control.row j at actual
  rw [same] at actual
  exact ⟨j, congrArg (fun values : Vector Int 11 => values.map
    (fun value : Int => (value : ZMod babyBearModulus))) actual⟩

/-- Complete imported generic tables supply the split memory controller facts. -/
theorem generic_control_setup_facts [Fact babyBearModulus.Prime]
    (columnParity : Table (ZMod babyBearModulus) (fields 8)) :
    ControlSetupFacts ⟨columnParity,
      thetaRhoGeneric.table "Airbender.SplitThetaRhoGeneric",
      chi5Generic.table "Airbender.SplitChi5Generic"⟩ := by
  apply control_setup_facts (by decide)
  exact {
    thetaRho := fun row sound tag _ => theta_rho_generic_controller_sound row sound tag
    chi5 := fun row sound tag _ => chi5_generic_controller_sound row sound tag }

end Airbender.Keccak.Split.Native.Fixed.Proofs
