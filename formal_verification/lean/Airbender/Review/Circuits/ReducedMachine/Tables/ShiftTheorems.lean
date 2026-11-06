import Airbender.Proofs.ReducedMachine.NativeShiftTable

namespace Airbender.ReducedMachine.NativeFixed

/-- Actual tag-37 membership fixes the packed key and both native arithmetic outputs. -/
theorem shift_implementation (query : Vector (ZMod mersenne31Modulus) 4)
    (member : (table (p := mersenne31Modulus)).Contains #[] query)
    (selected : query[3] = 37) :
    query[0].val < 4194304 ∧ query[1].val = (shiftOutputs query[0].val)[0] ∧
      query[2].val = (shiftOutputs query[0].val)[1] ∧
      query[1].val < 65536 ∧ query[2].val < 65536 :=
  NativeShiftTableProofs.result query member selected

end Airbender.ReducedMachine.NativeFixed
