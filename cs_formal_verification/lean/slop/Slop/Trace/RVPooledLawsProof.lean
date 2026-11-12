module
public import Slop.Trace.RVPooledLaws
public import Slop.Trace.Pooled
public import Slop.Trace.RVZeroPooled
public import Slop.Trace.RVValuesPooled

@[expose] public section

/-! Proof of the pooled RV laws contract (`RVPooledLaws`): the only module that imports every family's row lemmas.
    Imported by the final theorems, not by the per-family proofs. -/

namespace Airbender.Trace.Proofs

theorem rvPooledLaws : RVPooledLaws where
  clockLaws := pooledClockLaws
  zeroPreserving := RVZero.rv_pooled_zero_preserving
  valueBounds := RVValues.rv_pooled_value_bounds

end Airbender.Trace.Proofs
