import Airbender.Proofs.ReducedMachine.NativeRuntimeQueryTransport

namespace Airbender.ReducedMachine.NativeRuntimePool

/-- The SAME query belongs to the retained fixed fixture when its actual tag
    is outside CSR25. This is a derived stored-row consequence, not a table-
    equivalence premise, arbitrary BODY transfer or physical setup refinement. -/
theorem native_runtime_noncsr_query (query : Vector (ZMod mersenne31Modulus) 4)
    (member : (table (p := mersenne31Modulus)).Contains #[] query)
    (outside : query[3] ≠ 25) :
    (NativeFixed.table (p := mersenne31Modulus)).Contains #[] query :=
  Airbender.NativeRuntimeQueryTransportProofs.outside_csr query member outside
end Airbender.ReducedMachine.NativeRuntimePool
