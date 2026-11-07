import Human.Trace.WritesRangeChecked
import Slop.Trace.WriteSites
import Slop.Trace.RVPooled.Oracle
import Slop.UnifiedReduced.Values
import Slop.Delegation.Operations
import Slop.KeccakSplit.Contract

/-! The write-site inventory of `Human.Trace.WritesRangeChecked`: each circuit set's per-row write rule. -/

namespace Airbender.Trace

/-- The six pooled families, with the standard or the CSR 0x7C0-extended program table: every row's writes are
    range-checked (`rv_pooled_write_rules`, `rv_oracle_write_rules`). -/
theorem writes_range_checked : WritesRangeCheckedClaim := by
  intro trace initial cells program inits projection table inputs accepted decoded row member
  obtain ⟨addresses, programImage⟩ := inputs.programImage
  apply Proofs.writesRangeChecked_of_rule
  rcases table with rfl | rfl
  · exact RVValues.rv_pooled_write_rules (by decide) accepted inputs.wordTable inputs.subwordSetup programImage
      decoded row member
  · exact Proofs.rv_oracle_write_rules (by decide) accepted inputs.wordTable inputs.subwordSetup programImage
      decoded row member

end Airbender.Trace

namespace Airbender.UnifiedReduced
open Trace

/-- The unified reduced machine: every row's writes are range-checked by its own constraints
    (`row_write_sources`: the destination is range-checked, the two source ports are readonly refreshes). -/
theorem writes_range_checked : WritesRangeCheckedClaim := by
  intro trace accepted row member
  exact Trace.Proofs.writesRangeChecked_of_rule
    (Trace.Proofs.row_write_rule_of_sources (Proofs.row_write_sources row (accepted.constraints row member)))

end Airbender.UnifiedReduced

namespace Airbender.Delegation
open Trace

/-- The four delegation workers: every row's writes are range-checked (`operation_rules_of_queries`). -/
theorem writes_range_checked : WritesRangeCheckedClaim := by
  intro data control accepted tables rounds keccakActive row member
  exact Trace.Proofs.writesRangeChecked_of_ports
    (Proofs.operation_rules_of_queries (by decide) (by decide) accepted.constraints tables rounds keccakActive
      row member)

end Airbender.Delegation

namespace Airbender.Keccak.Split.Native
open Trace

/-- The split Keccak workers: every active row's writes are range-checked (`RowContract.writes`). -/
theorem writes_range_checked : WritesRangeCheckedClaim := by
  intro data accepted active row member
  exact Trace.Proofs.writesRangeChecked_of_ports
    (Proofs.row_contract.writes row (accepted.constraints row member) (active row member))

end Airbender.Keccak.Split.Native

namespace Airbender.InitsTeardowns

/-- Every `Init` tuple writes the zero word. -/
theorem writes_range_checked : WritesRangeCheckedClaim := by
  intro p layout w
  exact Proofs.init_bounded w

end Airbender.InitsTeardowns
