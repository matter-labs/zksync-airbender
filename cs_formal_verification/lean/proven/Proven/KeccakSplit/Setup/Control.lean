module
public import Proven.KeccakSplit.Setup.ThetaRho.Members
public import Proven.KeccakSplit.Setup.Chi5.Members
public import Proven.KeccakSplit.Memory.Order

@[expose] public section

/- The exported controller rows give the grouped-clock controller facts. -/

namespace Airbender.Keccak.Split.Proofs
set_option warningAsError true

theorem control_facts : ControlFacts babyBearModulus :=
  ⟨fun _ sound tag active => ThetaRho.SetupProofs.control_table_one_hot sound tag active,
    fun _ sound tag _ => Chi5.SetupProofs.control_table_plane sound tag⟩

end Airbender.Keccak.Split.Proofs
