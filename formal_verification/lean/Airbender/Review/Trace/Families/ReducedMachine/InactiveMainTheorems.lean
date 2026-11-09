import Airbender.Proofs.ReducedMachine.NativeInactiveMain

namespace Airbender.NativeInactiveMain
/-- Complete ordinary MAIN memory chain, individual caller and decoder access
    admit an inactive request-positive component fixture on its explicit
    nonpole domain. Caller sum completion and global acceptance remain separate;
    the constant fixture's zero caller claim is rejected by the old sum law. -/
theorem native_inactive_main_components : ∃ w, Fixture w :=
  Airbender.NativeInactiveMainProofs.fixture
end Airbender.NativeInactiveMain
