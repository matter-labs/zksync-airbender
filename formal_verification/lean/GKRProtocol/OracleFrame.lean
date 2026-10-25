import GKRProtocol.BaseAssignment
import GKRProtocol.MaterializedSetup

namespace Airbender.Compiler
set_option warningAsError true

/-- Values at addresses outside the finite arithmetic bank retain the caller's
external interpretation. The check uses the actual bank lookup and address. -/
theorem WireBank.materialize_external (bank : WireBank n)
    (values : Fin n → Source.BaseField) (fallback : GKRAddress → Source.BaseField)
    (address : GKRAddress)
    (external : addressEqual (bank.address (bank.placement address)) address = false) :
    bank.materialize values fallback address = fallback address := by
  simp only [WireBank.materialize, external, Bool.false_eq_true, ↓reduceIte]

/-- Bind physical setup addresses to literal imported table rows, retaining the
caller's interpretation for the rest of the external address space. -/
def MaterializedLookupSetup.baseOracle (model : MaterializedLookupSetup width)
    (row : Fin model.imported.data.length) (fallback : GKRAddress → Source.BaseField) :
    GKRAddress → Source.BaseField
  | .Setup column => model.value row (.generic column)
  | .VirtualSetup .RangeCheck16Bits => model.value row .range16
  | .VirtualSetup .RangeCheckTimestamp => model.value row .timestamp
  | address => fallback address

theorem MaterializedLookupSetup.baseOracle_at (model : MaterializedLookupSetup width)
    (row : Fin model.imported.data.length) (fallback : GKRAddress → Source.BaseField)
    (column : SourceSetupColumn) :
    model.baseOracle row fallback column.address = model.value row column := by
  cases column <;> rfl

end Airbender.Compiler
