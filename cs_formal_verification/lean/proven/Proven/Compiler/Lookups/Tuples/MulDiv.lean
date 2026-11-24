module
public import Proven.Compiler.Lookups.Bridge
public import Human.Compiler.LookupSelectors
public import Proven.GKRProtocol.LookupSourceNative.MulDivCached
public import Proven.KernelRfl
public import Mathlib.Tactic.IntervalCases

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.NativeLookups.TupleBindings.MulDiv
open Airbender.Compiler
set_option maxRecDepth 32768

/-- The complete native query tuples at the checked scalar or vector encodings. -/
noncomputable def checkedTuples (physical : GKRAddress → NativeArithmetic.F) (group : Fin 3) : List MaterializedQuery :=
  ([[⟨Airbender.Compiler.LookupSourceNative.MulDivCached.native.encoding16.fields physical, Airbender.Compiler.LookupSourceNative.MulDivCached.native.leaf16.weight.value physical⟩,
      ⟨Airbender.Compiler.LookupSourceNative.MulDivCached.native.encoding18.fields physical, Airbender.Compiler.LookupSourceNative.MulDivCached.native.leaf18.weight.value physical⟩,
      ⟨Airbender.Compiler.LookupSourceNative.MulDivCached.native.encoding19.fields physical, Airbender.Compiler.LookupSourceNative.MulDivCached.native.leaf19.weight.value physical⟩,
      ⟨Airbender.Compiler.LookupSourceNative.MulDivCached.native.encoding20.fields physical, Airbender.Compiler.LookupSourceNative.MulDivCached.native.leaf20.weight.value physical⟩,
      ⟨Airbender.Compiler.LookupSourceNative.MulDivCached.native.encoding21.fields physical, Airbender.Compiler.LookupSourceNative.MulDivCached.native.leaf21.weight.value physical⟩,
      ⟨Airbender.Compiler.LookupSourceNative.MulDivCached.native.encoding22.fields physical, Airbender.Compiler.LookupSourceNative.MulDivCached.native.leaf22.weight.value physical⟩,
      ⟨Airbender.Compiler.LookupSourceNative.MulDivCached.native.encoding23.fields physical, Airbender.Compiler.LookupSourceNative.MulDivCached.native.leaf23.weight.value physical⟩,
      ⟨Airbender.Compiler.LookupSourceNative.MulDivCached.native.encoding26.fields physical, Airbender.Compiler.LookupSourceNative.MulDivCached.native.leaf26.weight.value physical⟩,
      ⟨Airbender.Compiler.LookupSourceNative.MulDivCached.native.encoding27.fields physical, Airbender.Compiler.LookupSourceNative.MulDivCached.native.leaf27.weight.value physical⟩],
    [⟨Airbender.Compiler.LookupSourceNative.MulDivCached.native.encoding0.fields physical, Airbender.Compiler.LookupSourceNative.MulDivCached.native.leaf0.weight.value physical⟩,
      ⟨Airbender.Compiler.LookupSourceNative.MulDivCached.native.encoding2.fields physical, Airbender.Compiler.LookupSourceNative.MulDivCached.native.leaf2.weight.value physical⟩,
      ⟨Airbender.Compiler.LookupSourceNative.MulDivCached.native.encoding3.fields physical, Airbender.Compiler.LookupSourceNative.MulDivCached.native.leaf3.weight.value physical⟩,
      ⟨Airbender.Compiler.LookupSourceNative.MulDivCached.native.encoding4.fields physical, Airbender.Compiler.LookupSourceNative.MulDivCached.native.leaf4.weight.value physical⟩,
      ⟨Airbender.Compiler.LookupSourceNative.MulDivCached.native.encoding5.fields physical, Airbender.Compiler.LookupSourceNative.MulDivCached.native.leaf5.weight.value physical⟩,
      ⟨Airbender.Compiler.LookupSourceNative.MulDivCached.native.encoding6.fields physical, Airbender.Compiler.LookupSourceNative.MulDivCached.native.leaf6.weight.value physical⟩,
      ⟨Airbender.Compiler.LookupSourceNative.MulDivCached.native.encoding7.fields physical, Airbender.Compiler.LookupSourceNative.MulDivCached.native.leaf7.weight.value physical⟩,
      ⟨Airbender.Compiler.LookupSourceNative.MulDivCached.native.encoding24.fields physical, Airbender.Compiler.LookupSourceNative.MulDivCached.native.leaf24.weight.value physical⟩],
    [⟨Airbender.Compiler.LookupSourceNative.MulDivCached.native.encoding8.fields physical, Airbender.Compiler.LookupSourceNative.MulDivCached.native.leaf8.weight.value physical⟩,
      ⟨Airbender.Compiler.LookupSourceNative.MulDivCached.native.encoding10.fields physical, Airbender.Compiler.LookupSourceNative.MulDivCached.native.leaf10.weight.value physical⟩,
      ⟨Airbender.Compiler.LookupSourceNative.MulDivCached.native.encoding11.fields physical, Airbender.Compiler.LookupSourceNative.MulDivCached.native.leaf11.weight.value physical⟩,
      ⟨Airbender.Compiler.LookupSourceNative.MulDivCached.native.encoding12.fields physical, Airbender.Compiler.LookupSourceNative.MulDivCached.native.leaf12.weight.value physical⟩,
      ⟨Airbender.Compiler.LookupSourceNative.MulDivCached.native.encoding13.fields physical, Airbender.Compiler.LookupSourceNative.MulDivCached.native.leaf13.weight.value physical⟩,
      ⟨Airbender.Compiler.LookupSourceNative.MulDivCached.native.encoding14.fields physical, Airbender.Compiler.LookupSourceNative.MulDivCached.native.leaf14.weight.value physical⟩,
      ⟨Airbender.Compiler.LookupSourceNative.MulDivCached.native.encoding15.fields physical, Airbender.Compiler.LookupSourceNative.MulDivCached.native.leaf15.weight.value physical⟩,
      ⟨Airbender.Compiler.LookupSourceNative.MulDivCached.native.encoding25.fields physical, Airbender.Compiler.LookupSourceNative.MulDivCached.native.leaf25.weight.value physical⟩]] : List (List MaterializedQuery)).get group

/-- Resolve the actual selected primitive operands once. -/
noncomputable def resolved (group : Fin 3) : List Operand :=
  match ((selectorsFor (.pooled .mulDiv)).filter (fun selector => selector.group == group)).mapM
      (select (circuitFor (.pooled .mulDiv))) with
  | .ok operands => operands
  | .error _ => []

/-- Every selector resolves to the retained actual operands. -/
theorem resolved_binding (group : Fin 3) :
    ((selectorsFor (.pooled .mulDiv)).filter (fun selector => selector.group == group)).mapM
      (select (circuitFor (.pooled .mulDiv))) = .ok (resolved group) := by
  obtain ⟨index, bound⟩ := group
  interval_cases index <;> kernel_rfl

/-- The resolved sparse columns are the checked native leaf fields. -/
theorem fields_binding (physical : GKRAddress → NativeArithmetic.F) (group : Fin 3) :
    (resolved group).map (materialize physical) = checkedTuples physical group := by
  obtain ⟨index, bound⟩ := group
  interval_cases index <;> kernel_rfl

/-- Public certificate tuples are exactly the checked native leaf encodings. -/
theorem binding (physical : GKRAddress → NativeArithmetic.F) (group : Fin 3) :
    requests (circuitFor (.pooled .mulDiv)) (selectorsFor (.pooled .mulDiv)) physical group =
      .ok (activeLookupFields (checkedTuples physical group)) := by
  exact (requests_of_resolved physical group (resolved group) (resolved_binding group)).trans
    (congrArg (fun values => Except.ok (activeLookupFields values)) (fields_binding physical group))

/-- Transport exact public matching to the original checked native tuple interface. -/
def matching {Index : Type} {physical : GKRAddress → NativeArithmetic.F}
    {tables : Fin 3 → Index → List NativeArithmetic.F}
    (arguments : Arguments (circuitFor (.pooled .mulDiv)) (selectorsFor (.pooled .mulDiv)) physical tables) :
    GroupedLookupArguments tables (fun group => activeLookupFields (checkedTuples physical group)) := by
  intro group
  have same : arguments.tuples group = activeLookupFields (checkedTuples physical group) :=
    Except.ok.inj ((arguments.binding group).symm.trans (binding physical group))
  exact cast (congrArg (LookupArgument (tables group)) same) (arguments.matching group)

end Airbender.Compiler.NativeLookups.TupleBindings.MulDiv
