import Airbender.Proofs.ReducedMachine.NativePointerLedger

namespace Airbender.NativePointerLedger
/-- SAME checked native BODY/initialization prefix, now with complete finite
    GPR and PC ledgers. Worker BODY, full source/global and physical acceptance
    remain separate; no expected history, ledger or read is a premise. -/
theorem native_pointer_prefix_ledgers :
    ∃ activeRows idle, NativePointerPrefix.Components activeRows idle ∧ Balanced activeRows :=
  NativePointerLedgerProofs.fixture
end Airbender.NativePointerLedger
