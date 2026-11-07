import Airbender.Proofs.ReducedMachine.NativeRuntimeCSR

namespace Airbender.ReducedMachine.NativeRuntimeCSR
set_option autoImplicit false
/-- Exact separately exported native runtime CSR region, not full pool or worker execution. -/
theorem implementation {key support delegate : ZMod mersenne31Modulus}
    (member : Contains #v[key,support,delegate,25]) : key.val < 4096 ∧
      support = (supported key.val : Nat) ∧ delegate = (delegated key.val : Nat) :=
  NativeRuntimeCSRProofs.values member
end Airbender.ReducedMachine.NativeRuntimeCSR
