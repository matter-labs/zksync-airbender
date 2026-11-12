module
public import Proven.Compiler.Lookups.Bridge
public import Human.Compiler.LookupSelectors
public import Proven.GKRProtocol.LookupSourceNative.SubwordMemoryCached
public import Proven.KernelRfl
public import Mathlib.Tactic.IntervalCases

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.NativeLookups.TupleBindings.SubwordMemory
open Airbender.Compiler
set_option maxRecDepth 32768

/-- The complete native query tuples at the checked scalar or vector encodings. -/
noncomputable def checkedTuples (physical : GKRAddress → NativeArithmetic.F) (group : Fin 3) : List MaterializedQuery :=
  ([[⟨Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.encoding12.fields physical, Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.leaf12.weight.value physical⟩,
      ⟨Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.encoding17.fields physical, Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.leaf17.weight.value physical⟩,
      ⟨Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.encoding18.fields physical, Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.leaf18.weight.value physical⟩],
    [⟨Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.encoding0.fields physical, Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.leaf0.weight.value physical⟩,
      ⟨Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.encoding2.fields physical, Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.leaf2.weight.value physical⟩,
      ⟨Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.encoding3.fields physical, Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.leaf3.weight.value physical⟩,
      ⟨Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.encoding14.fields physical, Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.leaf14.weight.value physical⟩,
      ⟨Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.encoding15.fields physical, Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.leaf15.weight.value physical⟩],
    [⟨Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.encoding4.fields physical, Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.leaf4.weight.value physical⟩,
      ⟨Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.encoding6.fields physical, Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.leaf6.weight.value physical⟩,
      ⟨Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.encoding7.fields physical, Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.leaf7.weight.value physical⟩,
      ⟨Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.encoding8.fields physical, Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.leaf8.weight.value physical⟩,
      ⟨Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.encoding9.fields physical, Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.leaf9.weight.value physical⟩,
      ⟨Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.encoding10.fields physical, Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.leaf10.weight.value physical⟩,
      ⟨Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.encoding11.fields physical, Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.leaf11.weight.value physical⟩,
      ⟨Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.encoding16.fields physical, Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.leaf16.weight.value physical⟩]] : List (List MaterializedQuery)).get group

/-- Resolve the actual selected primitive operands once. -/
noncomputable def resolved (group : Fin 3) : List Operand :=
  match ((selectorsFor (.pooled .subwordMemory)).filter (fun selector => selector.group == group)).mapM
      (select (circuitFor (.pooled .subwordMemory))) with
  | .ok operands => operands
  | .error _ => []

/-- Every selector resolves to the retained actual operands. -/
theorem resolved_binding (group : Fin 3) :
    ((selectorsFor (.pooled .subwordMemory)).filter (fun selector => selector.group == group)).mapM
      (select (circuitFor (.pooled .subwordMemory))) = .ok (resolved group) := by
  obtain ⟨index, bound⟩ := group
  interval_cases index <;> kernel_rfl

/-- The resolved sparse columns are the checked native leaf fields. -/
theorem fields_binding (physical : GKRAddress → NativeArithmetic.F) (group : Fin 3) :
    (resolved group).map (materialize physical) = checkedTuples physical group := by
  obtain ⟨index, bound⟩ := group
  interval_cases index <;> kernel_rfl

/-- Public certificate tuples are exactly the checked native leaf encodings. -/
theorem binding (physical : GKRAddress → NativeArithmetic.F) (group : Fin 3) :
    requests (circuitFor (.pooled .subwordMemory)) (selectorsFor (.pooled .subwordMemory)) physical group =
      .ok (activeLookupFields (checkedTuples physical group)) := by
  exact (requests_of_resolved physical group (resolved group) (resolved_binding group)).trans
    (congrArg (fun values => Except.ok (activeLookupFields values)) (fields_binding physical group))

/-- Transport exact public matching to the original checked native tuple interface. -/
def matching {Index : Type} {physical : GKRAddress → NativeArithmetic.F}
    {tables : Fin 3 → Index → List NativeArithmetic.F}
    (arguments : Arguments (circuitFor (.pooled .subwordMemory)) (selectorsFor (.pooled .subwordMemory)) physical tables) :
    GroupedLookupArguments tables (fun group => activeLookupFields (checkedTuples physical group)) := by
  intro group
  have same : arguments.tuples group = activeLookupFields (checkedTuples physical group) :=
    Except.ok.inj ((arguments.binding group).symm.trans (binding physical group))
  exact cast (congrArg (LookupArgument (tables group)) same) (arguments.matching group)

end Airbender.Compiler.NativeLookups.TupleBindings.SubwordMemory
