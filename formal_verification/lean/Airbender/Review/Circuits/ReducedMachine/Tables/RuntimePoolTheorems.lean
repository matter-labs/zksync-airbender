import Airbender.Proofs.ReducedMachine.NativeRuntimePool
import Airbender.Review.Circuits.ReducedMachine.Tables.RuntimeCSRTheorems
import Airbender.Review.Circuits.ReducedMachine.Tables.SignHigh

namespace Airbender.ReducedMachine.NativeRuntimePool
/-- Actual runtime-CSR membership within the explicitly constructed full pool. -/
theorem csr_properties {key support delegate : ZMod mersenne31Modulus}
    (member : (table (p := mersenne31Modulus)).Contains #[] #v[key,support,delegate,25]) :
    key.val < 4096 ∧ support = (NativeRuntimeCSR.supported key.val : Nat) ∧
      delegate = (NativeRuntimeCSR.delegated key.val : Nat) :=
  NativeRuntimeCSR.implementation (NativeRuntimePoolProofs.csr_member _ member rfl)

/-- Reuse the unchanged literal sign certificate after fresh actual tag isolation. -/
theorem sign_high (query : Vector (ZMod mersenne31Modulus) 4)
    (member : (table (p := mersenne31Modulus)).Contains #[] query) (selected : query[3] = 16) :
    query[0].val < 65536 ∧ query[1].val = query[0].val / 32768 ∧
      query[2].val = query[0].val / 256 ∧ query[3] = 16 :=
  SignHigh.native_sign_high query (NativeRuntimePoolProofs.sign_member query member selected)
end Airbender.ReducedMachine.NativeRuntimePool
