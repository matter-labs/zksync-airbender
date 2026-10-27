import Airbender.Import.Compiler.LogicalRows.ShiftBinopCached
import Airbender.Proofs.GKRProtocol.LogicalLookup
import Airbender.Proofs.GKRProtocol.MaterializedRangeNative.ShiftBinopCached
import Airbender.Proofs.GKRProtocol.PhysicalClosedNative.ShiftBinopCached
import Airbender.Proofs.GKRProtocol.PooledRowNative.ShiftBinopCached

namespace Airbender.Compiler.PooledRowNative.ShiftBinopCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option linter.unusedVariables false
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

/-- The readable physical input contract has exactly the generated arithmetic
and execute-column interpretation; this equality changes no row condition. -/
theorem input_binding : Input = PhysicalRowInput
    (fun physical => ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.artifact.gates,
    gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.bank.address) = 0)
    (fun physical => (Airbender.Compiler.CleanArithmeticNative.ShiftBinopCached.native.environment physical (fun _ _ => #[])).get
    Airbender.ShiftBinop.importedConstraintsTraceColumns.execute = 1) := rfl

/-- The public address projection is exactly the retained generated Clean row
interpretation. This is a definitional binding, not an execution premise. -/
theorem inputRow_binding (input : Input) :
    inputRow input = (show Trace.Row babyBearModulus Trace.PooledFamily from
      ⟨.shiftBinop, (Airbender.Compiler.CleanArithmeticNative.ShiftBinopCached.native.environment input.physical (fun _ _ => #[])).get⟩) := rfl

/-- Explicit public column-group selection agrees with the retained captured
lookup reduction's group ordering. -/
theorem lookupArguments_binding (input : Input) : LookupArguments input =
    ((group : Fin 3) → LookupArgument
      (Airbender.Compiler.MaterializedNative.ShiftBinopCached.native.model.fields
        (Airbender.Compiler.MaterializedWitnessNative.ShiftBinopCached.setupColumns group))
      (activeLookupFields (nativeRequests input group))) := rfl

/-- Native base arithmetic transports the actual expanded operands to the
source-projected logical interface; none of the field equalities is a premise. -/
private theorem native_query14 (input : Input) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.encoding14.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.leaf14.weight.value input.physical) =
      Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.query14.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.ShiftBinopCached.native.sourcePlacement) :=
  let copies := Airbender.Compiler.FunctionalLinksNative.ShiftBinopCached.native.lookupCopies input.physical input.arithmetic
  (congrArg₂ MaterializedQuery.mk (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.sourceField14_0 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.sourceField14_1 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.sourceField14_2 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.sourceField14_3 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.sourceField14_4 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.sourceField14_5 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.sourceField14_6 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.sourceField14_7 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.sourceField14_8 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.sourceField14_9 input.physical copies) rfl)))))))))) rfl).symm

private theorem native_query15 (input : Input) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.encoding15.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.leaf15.weight.value input.physical) =
      Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.query15.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.ShiftBinopCached.native.sourcePlacement) :=
  let copies := Airbender.Compiler.FunctionalLinksNative.ShiftBinopCached.native.lookupCopies input.physical input.arithmetic
  (congrArg₂ MaterializedQuery.mk (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.sourceField15_0 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.sourceField15_1 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.sourceField15_2 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.sourceField15_3 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.sourceField15_4 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.sourceField15_5 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.sourceField15_6 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.sourceField15_7 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.sourceField15_8 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.sourceField15_9 input.physical copies) rfl)))))))))) rfl).symm

private theorem native_query16 (input : Input) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.encoding16.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.leaf16.weight.value input.physical) =
      Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.query16.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.ShiftBinopCached.native.sourcePlacement) :=
  let copies := Airbender.Compiler.FunctionalLinksNative.ShiftBinopCached.native.lookupCopies input.physical input.arithmetic
  (congrArg₂ MaterializedQuery.mk (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.sourceField16_0 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.sourceField16_1 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.sourceField16_2 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.sourceField16_3 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.sourceField16_4 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.sourceField16_5 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.sourceField16_6 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.sourceField16_7 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.sourceField16_8 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.sourceField16_9 input.physical copies) rfl)))))))))) rfl).symm

private theorem native_query17 (input : Input) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.encoding17.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.leaf17.weight.value input.physical) =
      Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.query17.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.ShiftBinopCached.native.sourcePlacement) :=
  let copies := Airbender.Compiler.FunctionalLinksNative.ShiftBinopCached.native.lookupCopies input.physical input.arithmetic
  (congrArg₂ MaterializedQuery.mk (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.sourceField17_0 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.sourceField17_1 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.sourceField17_2 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.sourceField17_3 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.sourceField17_4 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.sourceField17_5 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.sourceField17_6 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.sourceField17_7 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.sourceField17_8 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.sourceField17_9 input.physical copies) rfl)))))))))) rfl).symm

private theorem native_query18 (input : Input) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.encoding18.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.leaf18.weight.value input.physical) =
      Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.query18.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.ShiftBinopCached.native.sourcePlacement) :=
  let copies := Airbender.Compiler.FunctionalLinksNative.ShiftBinopCached.native.lookupCopies input.physical input.arithmetic
  (congrArg₂ MaterializedQuery.mk (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.sourceField18_0 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.sourceField18_1 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.sourceField18_2 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.sourceField18_3 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.sourceField18_4 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.sourceField18_5 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.sourceField18_6 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.sourceField18_7 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.sourceField18_8 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.sourceField18_9 input.physical copies) rfl)))))))))) rfl).symm

private theorem native_query10 (input : Input) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.encoding10.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.leaf10.weight.value input.physical) =
      Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.query10.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.ShiftBinopCached.native.sourcePlacement) :=
  let copies := Airbender.Compiler.FunctionalLinksNative.ShiftBinopCached.native.lookupCopies input.physical input.arithmetic
  (congrArg₂ MaterializedQuery.mk (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.sourceField10_1 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.sourceField10_2 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.sourceField10_3 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.sourceField10_4 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.sourceField10_5 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.sourceField10_6 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.sourceField10_7 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.sourceField10_8 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.sourceField10_9 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.sourceField10_10 input.physical copies) rfl)))))))))) (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.sourceField10_0 input.physical copies)).symm

private theorem native_query0 (input : Input) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.encoding0.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.leaf0.weight.value input.physical) =
      Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.query0.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.ShiftBinopCached.native.sourcePlacement) :=
  let copies := Airbender.Compiler.FunctionalLinksNative.ShiftBinopCached.native.lookupCopies input.physical input.arithmetic
  (congrArg₂ MaterializedQuery.mk (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.sourceField0_0 input.physical copies) rfl) rfl).symm

private theorem native_query12 (input : Input) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.encoding12.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.leaf12.weight.value input.physical) =
      Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.query12.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.ShiftBinopCached.native.sourcePlacement) :=
  let copies := Airbender.Compiler.FunctionalLinksNative.ShiftBinopCached.native.lookupCopies input.physical input.arithmetic
  (congrArg₂ MaterializedQuery.mk (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.sourceField12_0 input.physical copies) rfl) rfl).symm

private theorem native_timestamp0 (input : Input) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.encoding2.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.leaf2.weight.value input.physical) =
      MaterializedQuery.mk [((Airbender.Compiler.HelperNative.ShiftBinopCached.native.fields).get ⟨0, by decide⟩).value (Airbender.Compiler.HelperNative.ShiftBinopCached.native.sourceValues input.physical)] 1 := by
  have same := (Airbender.Compiler.HelperNative.ShiftBinopCached.native.candidate2).sound
    Airbender.Compiler.HelperNative.ShiftBinopCached.native.placement Airbender.Compiler.MemoryNative.ShiftBinopCached.native.bank
    Airbender.Compiler.HelperNative.ShiftBinopCached.native.checked2 Airbender.Compiler.HelperNative.ShiftBinopCached.native.inBank2
    input.physical (Airbender.Compiler.FunctionalLinksNative.ShiftBinopCached.native.helperCopies input.physical input.arithmetic)
  rw [Airbender.Compiler.CleanArgumentsNative.ShiftBinopCached.native.timestampFieldMatch0] at same
  change MaterializedQuery.mk [Airbender.Compiler.HelperNative.ShiftBinopCached.native.recipe2.value input.physical] 1 = _
  exact congrArg (fun value : Source.BaseField => MaterializedQuery.mk [value] 1) same.symm

private theorem native_timestamp1 (input : Input) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.encoding4.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.leaf4.weight.value input.physical) =
      MaterializedQuery.mk [((Airbender.Compiler.HelperNative.ShiftBinopCached.native.fields).get ⟨1, by decide⟩).value (Airbender.Compiler.HelperNative.ShiftBinopCached.native.sourceValues input.physical)] 1 := by
  have same := (Airbender.Compiler.HelperNative.ShiftBinopCached.native.candidate4).sound
    Airbender.Compiler.HelperNative.ShiftBinopCached.native.placement Airbender.Compiler.MemoryNative.ShiftBinopCached.native.bank
    Airbender.Compiler.HelperNative.ShiftBinopCached.native.checked4 Airbender.Compiler.HelperNative.ShiftBinopCached.native.inBank4
    input.physical (Airbender.Compiler.FunctionalLinksNative.ShiftBinopCached.native.helperCopies input.physical input.arithmetic)
  rw [Airbender.Compiler.CleanArgumentsNative.ShiftBinopCached.native.timestampFieldMatch1] at same
  change MaterializedQuery.mk [Airbender.Compiler.HelperNative.ShiftBinopCached.native.recipe4.value input.physical] 1 = _
  exact congrArg (fun value : Source.BaseField => MaterializedQuery.mk [value] 1) same.symm

private theorem native_timestamp2 (input : Input) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.encoding5.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.leaf5.weight.value input.physical) =
      MaterializedQuery.mk [((Airbender.Compiler.HelperNative.ShiftBinopCached.native.fields).get ⟨2, by decide⟩).value (Airbender.Compiler.HelperNative.ShiftBinopCached.native.sourceValues input.physical)] 1 := by
  have same := (Airbender.Compiler.HelperNative.ShiftBinopCached.native.candidate5).sound
    Airbender.Compiler.HelperNative.ShiftBinopCached.native.placement Airbender.Compiler.MemoryNative.ShiftBinopCached.native.bank
    Airbender.Compiler.HelperNative.ShiftBinopCached.native.checked5 Airbender.Compiler.HelperNative.ShiftBinopCached.native.inBank5
    input.physical (Airbender.Compiler.FunctionalLinksNative.ShiftBinopCached.native.helperCopies input.physical input.arithmetic)
  rw [Airbender.Compiler.CleanArgumentsNative.ShiftBinopCached.native.timestampFieldMatch2] at same
  change MaterializedQuery.mk [Airbender.Compiler.HelperNative.ShiftBinopCached.native.recipe5.value input.physical] 1 = _
  exact congrArg (fun value : Source.BaseField => MaterializedQuery.mk [value] 1) same.symm

private theorem native_timestamp3 (input : Input) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.encoding6.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.leaf6.weight.value input.physical) =
      MaterializedQuery.mk [((Airbender.Compiler.HelperNative.ShiftBinopCached.native.fields).get ⟨3, by decide⟩).value (Airbender.Compiler.HelperNative.ShiftBinopCached.native.sourceValues input.physical)] 1 := by
  have same := (Airbender.Compiler.HelperNative.ShiftBinopCached.native.candidate6).sound
    Airbender.Compiler.HelperNative.ShiftBinopCached.native.placement Airbender.Compiler.MemoryNative.ShiftBinopCached.native.bank
    Airbender.Compiler.HelperNative.ShiftBinopCached.native.checked6 Airbender.Compiler.HelperNative.ShiftBinopCached.native.inBank6
    input.physical (Airbender.Compiler.FunctionalLinksNative.ShiftBinopCached.native.helperCopies input.physical input.arithmetic)
  rw [Airbender.Compiler.CleanArgumentsNative.ShiftBinopCached.native.timestampFieldMatch3] at same
  change MaterializedQuery.mk [Airbender.Compiler.HelperNative.ShiftBinopCached.native.recipe6.value input.physical] 1 = _
  exact congrArg (fun value : Source.BaseField => MaterializedQuery.mk [value] 1) same.symm

private theorem native_timestamp4 (input : Input) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.encoding7.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.leaf7.weight.value input.physical) =
      MaterializedQuery.mk [((Airbender.Compiler.HelperNative.ShiftBinopCached.native.fields).get ⟨4, by decide⟩).value (Airbender.Compiler.HelperNative.ShiftBinopCached.native.sourceValues input.physical)] 1 := by
  have same := (Airbender.Compiler.HelperNative.ShiftBinopCached.native.candidate7).sound
    Airbender.Compiler.HelperNative.ShiftBinopCached.native.placement Airbender.Compiler.MemoryNative.ShiftBinopCached.native.bank
    Airbender.Compiler.HelperNative.ShiftBinopCached.native.checked7 Airbender.Compiler.HelperNative.ShiftBinopCached.native.inBank7
    input.physical (Airbender.Compiler.FunctionalLinksNative.ShiftBinopCached.native.helperCopies input.physical input.arithmetic)
  rw [Airbender.Compiler.CleanArgumentsNative.ShiftBinopCached.native.timestampFieldMatch4] at same
  change MaterializedQuery.mk [Airbender.Compiler.HelperNative.ShiftBinopCached.native.recipe7.value input.physical] 1 = _
  exact congrArg (fun value : Source.BaseField => MaterializedQuery.mk [value] 1) same.symm

private theorem native_timestamp5 (input : Input) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.encoding8.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.leaf8.weight.value input.physical) =
      MaterializedQuery.mk [((Airbender.Compiler.HelperNative.ShiftBinopCached.native.fields).get ⟨5, by decide⟩).value (Airbender.Compiler.HelperNative.ShiftBinopCached.native.sourceValues input.physical)] 1 := by
  have same := (Airbender.Compiler.HelperNative.ShiftBinopCached.native.candidate8).sound
    Airbender.Compiler.HelperNative.ShiftBinopCached.native.placement Airbender.Compiler.MemoryNative.ShiftBinopCached.native.bank
    Airbender.Compiler.HelperNative.ShiftBinopCached.native.checked8 Airbender.Compiler.HelperNative.ShiftBinopCached.native.inBank8
    input.physical (Airbender.Compiler.FunctionalLinksNative.ShiftBinopCached.native.helperCopies input.physical input.arithmetic)
  rw [Airbender.Compiler.CleanArgumentsNative.ShiftBinopCached.native.timestampFieldMatch5] at same
  change MaterializedQuery.mk [Airbender.Compiler.HelperNative.ShiftBinopCached.native.recipe8.value input.physical] 1 = _
  exact congrArg (fun value : Source.BaseField => MaterializedQuery.mk [value] 1) same.symm

private theorem native_timestamp6 (input : Input) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.encoding9.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.leaf9.weight.value input.physical) =
      MaterializedQuery.mk [((Airbender.Compiler.HelperNative.ShiftBinopCached.native.fields).get ⟨6, by decide⟩).value (Airbender.Compiler.HelperNative.ShiftBinopCached.native.sourceValues input.physical)] 1 := by
  have same := (Airbender.Compiler.HelperNative.ShiftBinopCached.native.candidate9).sound
    Airbender.Compiler.HelperNative.ShiftBinopCached.native.placement Airbender.Compiler.MemoryNative.ShiftBinopCached.native.bank
    Airbender.Compiler.HelperNative.ShiftBinopCached.native.checked9 Airbender.Compiler.HelperNative.ShiftBinopCached.native.inBank9
    input.physical (Airbender.Compiler.FunctionalLinksNative.ShiftBinopCached.native.helperCopies input.physical input.arithmetic)
  rw [Airbender.Compiler.CleanArgumentsNative.ShiftBinopCached.native.timestampFieldMatch6] at same
  change MaterializedQuery.mk [Airbender.Compiler.HelperNative.ShiftBinopCached.native.recipe9.value input.physical] 1 = _
  exact congrArg (fun value : Source.BaseField => MaterializedQuery.mk [value] 1) same.symm

private theorem native_timestamp7 (input : Input) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.encoding13.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.leaf13.weight.value input.physical) =
      MaterializedQuery.mk [((Airbender.Compiler.HelperNative.ShiftBinopCached.native.fields).get ⟨7, by decide⟩).value (Airbender.Compiler.HelperNative.ShiftBinopCached.native.sourceValues input.physical)] 1 := by
  have same := (Airbender.Compiler.HelperNative.ShiftBinopCached.native.candidate13).sound
    Airbender.Compiler.HelperNative.ShiftBinopCached.native.placement Airbender.Compiler.MemoryNative.ShiftBinopCached.native.bank
    Airbender.Compiler.HelperNative.ShiftBinopCached.native.checked13 Airbender.Compiler.HelperNative.ShiftBinopCached.native.inBank13
    input.physical (Airbender.Compiler.FunctionalLinksNative.ShiftBinopCached.native.helperCopies input.physical input.arithmetic)
  rw [Airbender.Compiler.CleanArgumentsNative.ShiftBinopCached.native.timestampFieldMatch7] at same
  change MaterializedQuery.mk [Airbender.Compiler.HelperNative.ShiftBinopCached.native.recipe13.value input.physical] 1 = _
  exact congrArg (fun value : Source.BaseField => MaterializedQuery.mk [value] 1) same.symm

/-- Native base arithmetic identifies each enabled expanded payload and mask
with its source interpretation, including every timestamp helper. -/
theorem nativeRequests_source (input : Input) (group : Fin 3) :
    nativeRequests input group = physicalRequests input group := by
  fin_cases group

  · change [MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.encoding14.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.leaf14.weight.value input.physical),
      MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.encoding15.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.leaf15.weight.value input.physical),
      MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.encoding16.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.leaf16.weight.value input.physical),
      MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.encoding17.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.leaf17.weight.value input.physical),
      MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.encoding18.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.leaf18.weight.value input.physical),
      MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.encoding10.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.leaf10.weight.value input.physical)] =
      [Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.query14.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.ShiftBinopCached.native.sourcePlacement),
      Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.query15.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.ShiftBinopCached.native.sourcePlacement),
      Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.query16.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.ShiftBinopCached.native.sourcePlacement),
      Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.query17.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.ShiftBinopCached.native.sourcePlacement),
      Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.query18.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.ShiftBinopCached.native.sourcePlacement),
      Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.query10.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.ShiftBinopCached.native.sourcePlacement)]
    exact (congrArg₂ List.cons (native_query14 input) (congrArg₂ List.cons (native_query15 input) (congrArg₂ List.cons (native_query16 input) (congrArg₂ List.cons (native_query17 input) (congrArg₂ List.cons (native_query18 input) (congrArg₂ List.cons (native_query10 input) rfl))))))

  · change [MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.encoding0.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.leaf0.weight.value input.physical),
      MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.encoding12.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.leaf12.weight.value input.physical)] =
      [Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.query0.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.ShiftBinopCached.native.sourcePlacement),
      Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.query12.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.ShiftBinopCached.native.sourcePlacement)]
    exact (congrArg₂ List.cons (native_query0 input) (congrArg₂ List.cons (native_query12 input) rfl))

  · change [MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.encoding2.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.leaf2.weight.value input.physical),
      MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.encoding4.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.leaf4.weight.value input.physical),
      MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.encoding5.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.leaf5.weight.value input.physical),
      MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.encoding6.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.leaf6.weight.value input.physical),
      MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.encoding7.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.leaf7.weight.value input.physical),
      MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.encoding8.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.leaf8.weight.value input.physical),
      MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.encoding9.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.leaf9.weight.value input.physical),
      MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.encoding13.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.leaf13.weight.value input.physical)] =
      [MaterializedQuery.mk [((Airbender.Compiler.HelperNative.ShiftBinopCached.native.fields).get ⟨0, by decide⟩).value (Airbender.Compiler.HelperNative.ShiftBinopCached.native.sourceValues input.physical)] 1,
      MaterializedQuery.mk [((Airbender.Compiler.HelperNative.ShiftBinopCached.native.fields).get ⟨1, by decide⟩).value (Airbender.Compiler.HelperNative.ShiftBinopCached.native.sourceValues input.physical)] 1,
      MaterializedQuery.mk [((Airbender.Compiler.HelperNative.ShiftBinopCached.native.fields).get ⟨2, by decide⟩).value (Airbender.Compiler.HelperNative.ShiftBinopCached.native.sourceValues input.physical)] 1,
      MaterializedQuery.mk [((Airbender.Compiler.HelperNative.ShiftBinopCached.native.fields).get ⟨3, by decide⟩).value (Airbender.Compiler.HelperNative.ShiftBinopCached.native.sourceValues input.physical)] 1,
      MaterializedQuery.mk [((Airbender.Compiler.HelperNative.ShiftBinopCached.native.fields).get ⟨4, by decide⟩).value (Airbender.Compiler.HelperNative.ShiftBinopCached.native.sourceValues input.physical)] 1,
      MaterializedQuery.mk [((Airbender.Compiler.HelperNative.ShiftBinopCached.native.fields).get ⟨5, by decide⟩).value (Airbender.Compiler.HelperNative.ShiftBinopCached.native.sourceValues input.physical)] 1,
      MaterializedQuery.mk [((Airbender.Compiler.HelperNative.ShiftBinopCached.native.fields).get ⟨6, by decide⟩).value (Airbender.Compiler.HelperNative.ShiftBinopCached.native.sourceValues input.physical)] 1,
      MaterializedQuery.mk [((Airbender.Compiler.HelperNative.ShiftBinopCached.native.fields).get ⟨7, by decide⟩).value (Airbender.Compiler.HelperNative.ShiftBinopCached.native.sourceValues input.physical)] 1]
    exact (congrArg₂ List.cons (native_timestamp0 input) (congrArg₂ List.cons (native_timestamp1 input) (congrArg₂ List.cons (native_timestamp2 input) (congrArg₂ List.cons (native_timestamp3 input) (congrArg₂ List.cons (native_timestamp4 input) (congrArg₂ List.cons (native_timestamp5 input) (congrArg₂ List.cons (native_timestamp6 input) (congrArg₂ List.cons (native_timestamp7 input) rfl))))))))

/-- Every native query leaf occurs once, with the single setup leaf completing
exactly the retained native reduction tree's primitive multiset. -/
theorem nativeOperands_coverage (input : Input) (group : Fin 3) :
    (((nativeOperands input group).map Prod.fst) ++ [nativeSetupLeaf group]).Perm
      (([Airbender.Compiler.LookupNative.ShiftBinopCached.native.genericTree,
      Airbender.Compiler.LookupNative.ShiftBinopCached.native.range16Tree,
      Airbender.Compiler.LookupNative.ShiftBinopCached.native.timestampTree]).get group).leaves := by
  fin_cases group

  · change ([14,
      15,
      16,
      17,
      18,
      10,
      11] : List Nat).Perm (Airbender.Compiler.LookupNative.ShiftBinopCached.native.genericTree).leaves
    exact Eq.mpr (congrArg (fun leaves : List Nat => ([14,
      15,
      16,
      17,
      18,
      10,
      11] : List Nat).Perm leaves)
      Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.genericLeavesChecked) (by decide +kernel)

  · change ([0,
      12,
      1] : List Nat).Perm (Airbender.Compiler.LookupNative.ShiftBinopCached.native.range16Tree).leaves
    exact Eq.mpr (congrArg (fun leaves : List Nat => ([0,
      12,
      1] : List Nat).Perm leaves)
      Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.range16LeavesChecked) (by decide +kernel)

  · change ([2,
      4,
      5,
      6,
      7,
      8,
      9,
      13,
      3] : List Nat).Perm (Airbender.Compiler.LookupNative.ShiftBinopCached.native.timestampTree).leaves
    exact Eq.mpr (congrArg (fun leaves : List Nat => ([2,
      4,
      5,
      6,
      7,
      8,
      9,
      13,
      3] : List Nat).Perm leaves)
      Airbender.Compiler.HelperNative.ShiftBinopCached.native.leavesChecked) (by decide +kernel)

/-- Each designated native setup operand contains precisely the columns used
by the literal setup table in the corresponding logical argument. -/
theorem nativeSetupColumns_binding (group : Fin 3) :
    ([Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.encoding11.columns,
      Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.encoding1.columns,
      Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.encoding3.columns]).get group =
      (Airbender.Compiler.MaterializedWitnessNative.ShiftBinopCached.setupColumns group).map
        (fun column => AffineProgram.input (Address := GKRAddress) (R := Nat) column.address) := by
  fin_cases group
  · exact Airbender.Compiler.TableNative.ShiftBinopCached.native.genericSetupColumnsPreserved
  · exact Airbender.Compiler.TableNative.ShiftBinopCached.native.range16SetupColumnsPreserved
  · exact Airbender.Compiler.TableNative.ShiftBinopCached.native.timestampSetupColumnsPreserved

private noncomputable def sourceArguments (input : Input) (arguments : LookupArguments input)
    (group : Fin 3) : LookupArgument
      (Airbender.Compiler.MaterializedNative.ShiftBinopCached.native.model.fields
        (Airbender.Compiler.MaterializedWitnessNative.ShiftBinopCached.setupColumns group))
      (activeLookupFields (physicalRequests input group)) := by
  simpa only [nativeRequests_source input group, Airbender.Compiler.MaterializedWitnessNative.ShiftBinopCached.setupColumns] using arguments group
-- End native operand transport.

private theorem physical_member (input : Input) (arguments : LookupArguments input)
    (group : Fin 3) (query : MaterializedQuery)
    (member : query ∈ physicalRequests input group) (enabled : query.weight ≠ 0) :
    Airbender.Compiler.MaterializedNative.ShiftBinopCached.native.model.Contains
      (Airbender.Compiler.MaterializedWitnessNative.ShiftBinopCached.setupColumns group) query.fields :=
  LookupArgument.member (sourceArguments input arguments group) (activeLookupFields.member member enabled)

/-- Authored lookup membership is proved at physical coordinates, without a
canonical source frame, using exact matching of the emitted tuples. -/
theorem authored_from_arguments (input : Input) (arguments : LookupArguments input) :
    PhysicalAuthoredLookupValid input.physical := by
  constructor
  · intro query member enabled
    apply physical_member input arguments 0 (query.materialized
      ((input.physical ∘ Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.ShiftBinopCached.native.sourcePlacement)) ?_ enabled
    simpa [physicalRequests] using
      (List.mem_map.mpr ⟨query, member, rfl⟩ :
        query.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.ShiftBinopCached.native.sourcePlacement) ∈
          Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.genericQueries.map (fun item => item.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.ShiftBinopCached.native.sourcePlacement)))
  · intro query member enabled
    apply physical_member input arguments 1 (query.materialized
      ((input.physical ∘ Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.ShiftBinopCached.native.sourcePlacement)) ?_ enabled
    simpa [physicalRequests] using
      (List.mem_map.mpr ⟨query, member, rfl⟩ :
        query.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.ShiftBinopCached.native.sourcePlacement) ∈
          Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.range16Queries.map (fun item => item.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.ShiftBinopCached.native.sourcePlacement)))

/-- The complete literal timestamp column, including zero padding, bounds
actual physical helper values. No canonical borrow choice is imposed. -/
theorem helpers_from_arguments (input : Input) (arguments : LookupArguments input) :
    ∀ field ∈ Airbender.Compiler.HelperNative.ShiftBinopCached.native.fields,
      (field.value (Airbender.Compiler.HelperNative.ShiftBinopCached.native.sourceValues input.physical)).val < 524288 := by
  intro field member
  let value := field.value (Airbender.Compiler.HelperNative.ShiftBinopCached.native.sourceValues input.physical)
  have present := physical_member input arguments 2 (MaterializedQuery.mk [value] 1)
    (by simpa [physicalRequests, value, Airbender.Compiler.HelperNative.ShiftBinopCached.native.sourceValues] using
          (List.mem_map.mpr ⟨field, member, rfl⟩ :
            MaterializedQuery.mk [field.value (Airbender.Compiler.HelperNative.ShiftBinopCached.native.sourceValues input.physical)] 1 ∈
              Airbender.Compiler.HelperNative.ShiftBinopCached.native.fields.map (fun item => MaterializedQuery.mk
                [item.value (Airbender.Compiler.HelperNative.ShiftBinopCached.native.sourceValues input.physical)] 1))) one_ne_zero
  change Airbender.Compiler.MaterializedNative.ShiftBinopCached.native.model.Contains [.timestamp] [value] at present
  exact Airbender.Compiler.MaterializedRangeNative.ShiftBinopCached.native.timestamp_bounded value present

theorem input_active (input : Input) :
    (inputRow input).assignment (inputRow input).columns.execute = 1 := input.active

theorem input_constraints (input : Input) (arguments : LookupArguments input) {before : Reference.RiscV.Sail.State}
    (image : Trace.ROM.ImportedImage before) {cells : List Trace.Cell}
    {tokens : List (Trace.MemoryToken babyBearModulus)}
    (physical : Trace.initialImage before cells = some tokens)
    (domain : ROMNative.WordFullPublic.CoversROM cells) :
    FlatOperation.ConstraintsHoldFlat (Verification.environment (inputRow input).assignment)
      ((inputRow input).constraints (⟨Trace.ROM.table cells tokens,
        Verification.subwordTable (Trace.ROM.words before)⟩ : Trace.PooledSetup babyBearModulus)) := by
  have native := Airbender.Compiler.PhysicalClosedNative.ShiftBinopCached.retained_clock_from_physical
    input.physical (fun _ _ => #[]) input.arithmetic (helpers_from_arguments input arguments)
    (authored_from_arguments input arguments)
  exact native

/-- Decode by transporting physical table membership directly through the
checked decoder-payload geometry. No canonical borrow frame is needed. -/
theorem input_decoded (input : Input) (arguments : LookupArguments input)
    (typed : (inputRow input).decoderQuery[0].val < 65536) :
    (Trace.decoderTable Trace.NativeDecoder.pooledProgram (inputRow input).family).Contains #[]
      (inputRow input).decoderQuery := by
  apply Airbender.Compiler.DecoderQueryNative.ShiftBinopCached.program_from_source_membership (by decide +kernel)
    input.physical (fun _ _ => #[]) input.arithmetic typed
  apply (authored_from_arguments input arguments).1 Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.query10
    Airbender.Compiler.DecoderQueryNative.ShiftBinopCached.decoder_query_member
  rw [Airbender.Compiler.DecoderArgumentsNative.ShiftBinopCached.native.execute_weight input.physical (fun _ _ => #[]) input.arithmetic]
  have enabled : (Airbender.Compiler.CleanArithmeticNative.ShiftBinopCached.native.environment input.physical (fun _ _ => #[])).get
      Airbender.ShiftBinop.importedConstraintsTraceColumns.execute = 1 := input.active
  have nonzero : (Airbender.Compiler.CleanArithmeticNative.ShiftBinopCached.native.environment input.physical (fun _ _ => #[])).get
      Airbender.ShiftBinop.importedConstraintsTraceColumns.execute ≠ 0 :=
    fun zero => one_ne_zero (enabled.symm.trans zero)
  simpa [Airbender.Compiler.DecoderArgumentsNative.ShiftBinopCached.native.expression0, _root_.Expression.eval] using nonzero

end Airbender.Compiler.PooledRowNative.ShiftBinopCached
