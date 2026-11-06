import Slop.Trace.RVPooledLaws
import Slop.Trace.Pooled
import Slop.Trace.RVZeroPooled
import Slop.Trace.RVWritablePooled
import Slop.Trace.RVValuesPooled

/-! Proof of the pooled RV laws contract (`RVPooledLaws`): the only module that imports every family's row lemmas.
    Imported by the final theorems, not by the per-family proofs. -/

namespace Airbender.Trace.Proofs

theorem rvPooledLaws : RVPooledLaws where
  clockLaws := pooledClockLaws
  zeroPreserving := RVZero.rv_pooled_zero_preserving
  writable := RVWritable.rv_pooled_writable
  valueBounds := RVValues.rv_pooled_value_bounds

end Airbender.Trace.Proofs
