import Airbender.Data.Setup.Keccak.SplitControl
import Airbender.Review.Trace.Workers.Keccak.SplitNative
import Airbender.Review.Helpers.Core.FieldCapacity

namespace Airbender.Keccak.Split.Native.Fixed.Proofs
set_option warningAsError true
set_option maxRecDepth 16384

/-- All 120 active rows of the retained theta/rho controller region have
exactly one selected iteration flag. The padding row has execute zero. -/
theorem theta_rho_controller_rows :
    ∀ i : Fin thetaRhoControl.length,
      (thetaRhoControl.row i)[1] = 1 →
        ∃ selected : Fin 5, ∀ index : Fin 5,
          (thetaRhoControl.row i)[3 + index.val] =
            if index = selected then 1 else 0 := by
  decide +kernel

theorem theta_rho_controller_execute :
    ∀ i : Fin thetaRhoControl.length,
      (thetaRhoControl.row i)[1] = 0 ∨ (thetaRhoControl.row i)[1] = 1 := by
  decide +kernel

/-- The active row coordinate of the retained chi5 controller region is in
the five-row Keccak plane. -/
theorem chi5_controller_rows :
    ∀ i : Fin chi5Control.length,
      (chi5Control.row i)[1] = 1 →
        0 ≤ (chi5Control.row i)[8] ∧ (chi5Control.row i)[8] < 5 := by
  decide +kernel

theorem chi5_controller_execute :
    ∀ i : Fin chi5Control.length,
      (chi5Control.row i)[1] = 0 ∨ (chi5Control.row i)[1] = 1 := by
  decide +kernel

theorem chi5_controller_index :
    ∀ i : Fin chi5Control.length,
      ∃ index : Fin 5, (chi5Control.row i)[8] = index.val := by
  decide +kernel

/-- The imported theta/rho controller region, viewed as a genuine static
lookup table, has the one-hot property needed by the clock proof. -/
theorem theta_rho_table_sound [Fact p.Prime]
    (row : Vector (ZMod p) 9)
    (sound : (thetaRhoControl.table (p := p) "Airbender.SplitThetaRhoControl").toRaw.Soundness #[] row)
    (active : row[1] = 1) :
    ∃ selected : Fin 5, ∀ index : Fin 5,
      row[3 + index.val] = if index = selected then 1 else 0 := by
  change ∃ i : Fin thetaRhoControl.length,
    row = (thetaRhoControl.row i).map (fun value : Int => (value : ZMod p)) at sound
  obtain ⟨i, rfl⟩ := sound
  have execute : (thetaRhoControl.row i)[1] = 1 := by
    rcases theta_rho_controller_execute i with zero | one
    · simp [zero] at active
    · exact one
  obtain ⟨selected, flags⟩ := theta_rho_controller_rows i execute
  refine ⟨selected, ?_⟩
  intro index
  have flag := congrArg (fun value : Int => (value : ZMod p)) (flags index)
  simpa using flag

/-- The retained chi5 controller table bounds the actual lookup's row index,
independently of its unused padding column. -/
theorem chi5_table_sound [Fact p.Prime]
    (hp : FieldCapacity.NoWrap p 5)
    (row : Vector (ZMod p) 11)
    (sound : (chi5Control.table (p := p) "Airbender.SplitChi5Control").toRaw.Soundness #[] row) :
    row[8].val < 5 := by
  change ∃ i : Fin chi5Control.length,
    row = (chi5Control.row i).map (fun value : Int => (value : ZMod p)) at sound
  obtain ⟨i, rfl⟩ := sound
  obtain ⟨index, equal⟩ := chi5_controller_index i
  simp only [Vector.getElem_map, equal, Int.cast_natCast, ZMod.val_natCast]
  simp [Nat.mod_eq_of_lt (lt_trans index.isLt hp), index.isLt]

/-- The remaining full-setup obligation is exact controller-region membership:
tagged active rows of the materialized generic table must be rows of these
retained native controller slices. -/
structure ControlRegionBinding [Fact p.Prime] (setup : Native.Setup p) : Prop where
  thetaRho : ∀ row : Vector (ZMod p) 9,
    setup.thetaRho.toRaw.Soundness #[] row → row[8] = 59 → row[1] = 1 →
      (thetaRhoControl.table (p := p) "Airbender.SplitThetaRhoControl").toRaw.Soundness #[] row
  chi5 : ∀ row : Vector (ZMod p) 11,
    setup.chi5.toRaw.Soundness #[] row → row[10] = 66 → row[1] = 1 →
      (chi5Control.table (p := p) "Airbender.SplitChi5Control").toRaw.Soundness #[] row

/-- Controller semantics follows from the retained rows once their membership
in the full fixed setup is established. -/
theorem control_setup_facts [Fact p.Prime]
    (hp : FieldCapacity.NoWrap p 5)
    {setup : Native.Setup p} (binding : ControlRegionBinding setup) :
    Native.ControlSetupFacts setup where
  thetaRho row sound tag active :=
    theta_rho_table_sound row (binding.thetaRho row sound tag active) active
  chi5 row sound tag active :=
    chi5_table_sound hp row (binding.chi5 row sound tag active)

end Airbender.Keccak.Split.Native.Fixed.Proofs
