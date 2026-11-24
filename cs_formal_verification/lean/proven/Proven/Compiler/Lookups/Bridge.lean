module
public import Human.Compiler.NativeLookups
public import Proven.GKRProtocol.LookupOperands

@[expose] public section
namespace Airbender.Compiler.NativeLookups
set_option warningAsError true

/-- Materialize one actual native operand without alpha compression. -/
def materialize (physical : GKRAddress → NativeArithmetic.F) (operand : Operand) : MaterializedQuery :=
  ⟨operand.input.fields physical, operand.weight.value physical⟩

/-- Filtering enabled requests commutes with materializing their fields. -/
theorem active_materialized (physical : GKRAddress → NativeArithmetic.F) (operands : List Operand) :
    (operands.filter (fun operand => operand.weight.value physical != 0)).map
      (fun operand => operand.input.fields physical) =
    activeLookupFields (operands.map (materialize physical)) := by
  induction operands with
  | nil => rfl
  | cons first rest ih =>
    by_cases enabled : first.weight.value physical = 0
    · simpa [activeLookupFields, materialize, enabled] using ih
    · simpa [activeLookupFields, materialize, enabled] using congrArg (first.input.fields physical :: ·) ih

/-- Resolve the actual operands, then use their checked uncompressed fields. -/
theorem requests_of_resolved {circuit : Circuit} {selectors : List Selector}
    (physical : GKRAddress → NativeArithmetic.F) (group : Fin 3) (resolved : List Operand)
    (binding : (selectors.filter (fun selector => selector.group == group)).mapM (select circuit) = .ok resolved) :
    requests circuit selectors physical group =
      .ok (activeLookupFields (resolved.map (materialize physical))) := by
  unfold requests
  rw [binding]
  exact congrArg Except.ok (active_materialized physical resolved)

end Airbender.Compiler.NativeLookups
