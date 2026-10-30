import Airbender.Proofs.Keccak.SplitThetaNativeQueries
import Airbender.Proofs.Keccak.SplitChiControllerQuery
import Airbender.Proofs.Keccak.SplitParityNativeQueries
import Airbender.Review.Trace.Workers.Keccak.SplitNative

namespace Airbender.Keccak.Split.Native.Proofs
open Trace
set_option warningAsError true
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
set_option Elab.async false
variable [Fact babyBearModulus.Prime]

/-- The three complete retained native tables, including physical padding. -/
def fixedSetup : Setup babyBearModulus :=
  ⟨columnParityFixedTable, thetaRhoFixedTable, chi5FixedTable⟩

/-- Complete native table membership proves both controller facts used by grouped memory order. -/
theorem fixed_control_setup_facts : ControlSetupFacts fixedSetup := by
  constructor
  · intro row member tag active
    have control := (Fixed.Proofs.theta_rho_physical_generic_bindings row member).2.2.1 tag
    obtain ⟨index, _, _, _, flags⟩ := Fixed.Proofs.theta_rho_controller_table_schedule row control active
    refine ⟨⟨index.val % 5, Nat.mod_lt _ (by decide)⟩, ?_⟩
    intro column
    simpa only [Fin.ext_iff] using flags column
  · intro row member tag active
    obtain ⟨index, _, _, _, _, selected⟩ := Fixed.Proofs.chi5_generic_controller_schedule row member tag active
    rw [selected, ZMod.val_natCast_of_lt (lt_trans (Nat.mod_lt _ (by decide : 0 < 5)) (by decide))]
    exact Nat.mod_lt _ (by decide)

end Airbender.Keccak.Split.Native.Proofs
