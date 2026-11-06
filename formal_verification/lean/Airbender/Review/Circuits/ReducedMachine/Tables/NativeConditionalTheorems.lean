import Airbender.Proofs.ReducedMachine.NativeConditionalTable

namespace Airbender.ReducedMachine.NativeFixed
set_option autoImplicit false

/-- Exact actual packed-key resolver semantics for all native flag combinations. -/
theorem conditional_implementation (query : Vector (ZMod mersenne31Modulus) 4)
    (member : (table (p := mersenne31Modulus)).Contains #[] query) (tag : query[3] = 22) :
    ∃ i : Fin 128, query = (Native.conditionalRow i).map Nat.cast :=
  NativeConditionalTableProofs.result query member tag

end Airbender.ReducedMachine.NativeFixed
