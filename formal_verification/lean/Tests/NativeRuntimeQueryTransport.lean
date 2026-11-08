import Airbender.Review.Circuits.ReducedMachine.Tables.RuntimeQueryTransportTheorems
import Tests.NativeRuntimePool

namespace Airbender.Tests.NativeRuntimeQueryTransport
open Airbender.ReducedMachine
set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false

/-- Reuse checked membership in the distinct complete fixture configurations. -/
theorem csr_stays_distinct :
    (NativeRuntimePool.table (p := mersenne31Modulus)).Contains #[] #v[1991,1,1,25] ∧
    ¬ (NativeFixed.table (p := mersenne31Modulus)).Contains #[] #v[1991,1,1,25] :=
  ⟨_root_.Tests.NativeRuntimePool.runtime_pool_positive.1,
    _root_.Tests.NativeRuntimePool.original_fixture_stays_distinct⟩

theorem no_unrestricted_transfer : ¬ (∀ query : Vector (ZMod mersenne31Modulus) 4,
    (NativeRuntimePool.table (p := mersenne31Modulus)).Contains #[] query →
    (NativeFixed.table (p := mersenne31Modulus)).Contains #[] query) := by
  intro all
  exact csr_stays_distinct.2 (all _ csr_stays_distinct.1)

theorem csr_outside_domain : ¬ ((#v[(1991 : ZMod mersenne31Modulus),1,1,25] :
    Vector (ZMod mersenne31Modulus) 4)[3] ≠ 25) := by simp

theorem retained_tags : NativeRuntimePool.tags.filter (fun tag => tag != 25) =
    [0,4,6,7,16,17,18,20,22,23,24,37,47] := by decide +kernel
end Airbender.Tests.NativeRuntimeQueryTransport
