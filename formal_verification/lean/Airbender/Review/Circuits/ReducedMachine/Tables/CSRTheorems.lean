import Airbender.Proofs.ReducedMachine.NativeCSRTable

namespace Airbender.ReducedMachine.NativeFixed
set_option autoImplicit false
/-- Exact special-CSR fixture semantics over all rows of the actual native pool. -/
theorem csr_properties_implementation {key supported delegated : ZMod mersenne31Modulus}
    (member : (table (p := mersenne31Modulus)).Contains #[] #v[key,supported,delegated,25]) :
    key.val < 4096 ∧ supported = (csrSupported key.val : Nat) ∧ delegated = (csrDelegated key.val : Nat) :=
  NativeCSRTableProofs.values member
end Airbender.ReducedMachine.NativeFixed
