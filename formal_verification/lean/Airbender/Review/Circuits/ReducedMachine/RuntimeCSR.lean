import Airbender.Review.Circuits.ReducedMachine.CSR
import Airbender.Review.Circuits.ReducedMachine.Tables.RuntimePool

namespace Airbender.ReducedMachine.Native
open Arithmetic
set_option autoImplicit false
/-- Actual local native CSR observables under the explicitly constructed runtime-CSR pool.
    No original CSR read, custom-operation success or worker effect is asserted. -/
structure CSRRuntimeEffects (w : Nat → ZMod mersenne31Modulus) : Prop where
  key : (w 9).val = 1984 ∨ (w 9).val = 1991
  supported : w 64 = 1
  delegated : w 65 = (NativeRuntimeCSR.delegated (w 9).val : Nat)
  selected : source2 w = #v[w 9,w 10]
  secondPort : w 39 = w 6 ∧ w 40 = 0 ∧ w 88 = 1
  tags : lookupSelectors w = #v[25,0,0,0]
  candidate : csrCandidate w = #v[w 90,w 91]
  destination : rdPort.address.code w = Nat.pair 0 (Nat.pair (rdIndex w).val 0)
  written : rdWrite w = (csrCandidate w).map (fun value => (1-rdZeroFlag w)*value)
  oracleBounded : (csrOracleWord w).Bounded
  delegationZero : NativeRuntimeCSR.delegated (w 9).val = 1 → csrOracleWord w = ⟨0,0⟩
  request : csrRequest w =
    ⟨(NativeRuntimeCSR.delegated (w 9).val : Nat),w 9*(NativeRuntimeCSR.delegated (w 9).val : Nat),
      some (w 36*(NativeRuntimeCSR.delegated (w 9).val : Nat)),3⟩
  offsetBounded : (w 93).val < 65536
  pc : #v[w 13,w 14] = #v[w 49,w 50]
end Airbender.ReducedMachine.Native
