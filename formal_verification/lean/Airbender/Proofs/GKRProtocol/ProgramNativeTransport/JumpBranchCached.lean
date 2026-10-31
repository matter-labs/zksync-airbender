import Airbender.Import.Compiler.LogicalRows.JumpBranchCached
import Airbender.Proofs.GKRProtocol.LogicalLookup
import Airbender.Proofs.GKRProtocol.MaterializedRangeNative.JumpBranchCached
import Airbender.Proofs.GKRProtocol.PhysicalClosedNative.JumpBranchCached

namespace Airbender.Compiler.PooledRowNative.JumpBranchCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option linter.unusedVariables false
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

/-- The readable physical input contract has exactly the generated arithmetic
and execute-column interpretation; this equality changes no row condition. -/
theorem input_binding : Input = PhysicalRowInput
    (fun physical => ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.JumpBranchCached.native.artifact.gates,
    gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.JumpBranchCached.native.bank.address) = 0)
    (fun physical => (Airbender.Compiler.CleanArithmeticNative.JumpBranchCached.native.environment physical (fun _ _ => #[])).get
    Airbender.JumpBranchSlt.importedConstraintsTraceColumns.execute = 1) := rfl

/-- The public address projection is exactly the retained generated Clean row
interpretation. This is a definitional binding, not an execution premise. -/
theorem inputRow_binding (input : Input) :
    inputRow input = (show Trace.Row babyBearModulus Trace.PooledFamily from
      ⟨.jumpBranchSlt, (Airbender.Compiler.CleanArithmeticNative.JumpBranchCached.native.environment input.physical (fun _ _ => #[])).get⟩) := rfl

/-- Explicit public column-group selection agrees with the retained captured
lookup reduction's group ordering. -/
theorem lookupArguments_binding (input : Input) : LookupArguments input =
    ((group : Fin 3) → LookupArgument
      (Airbender.Compiler.MaterializedNative.JumpBranchCached.native.model.fields
        (Airbender.Compiler.MaterializedWitnessNative.JumpBranchCached.setupColumns group))
      (activeLookupFields (nativeRequests input group))) := rfl

/-- Native base arithmetic transports the actual expanded operands to the
source-projected logical interface; none of the field equalities is a premise. -/
private theorem native_query14 (input : Input) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.encoding14.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.leaf14.weight.value input.physical) =
      Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.query14.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.JumpBranchCached.native.sourcePlacement) :=
  let copies := Airbender.Compiler.FunctionalLinksNative.JumpBranchCached.native.lookupCopies input.physical input.arithmetic
  (congrArg₂ MaterializedQuery.mk (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.sourceField14_0 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.sourceField14_1 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.sourceField14_2 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.sourceField14_3 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.sourceField14_4 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.sourceField14_5 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.sourceField14_6 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.sourceField14_7 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.sourceField14_8 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.sourceField14_9 input.physical copies) rfl)))))))))) rfl).symm

private theorem native_query15 (input : Input) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.encoding15.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.leaf15.weight.value input.physical) =
      Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.query15.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.JumpBranchCached.native.sourcePlacement) :=
  let copies := Airbender.Compiler.FunctionalLinksNative.JumpBranchCached.native.lookupCopies input.physical input.arithmetic
  (congrArg₂ MaterializedQuery.mk (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.sourceField15_0 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.sourceField15_1 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.sourceField15_2 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.sourceField15_3 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.sourceField15_4 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.sourceField15_5 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.sourceField15_6 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.sourceField15_7 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.sourceField15_8 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.sourceField15_9 input.physical copies) rfl)))))))))) rfl).symm

private theorem native_query16 (input : Input) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.encoding16.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.leaf16.weight.value input.physical) =
      Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.query16.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.JumpBranchCached.native.sourcePlacement) :=
  let copies := Airbender.Compiler.FunctionalLinksNative.JumpBranchCached.native.lookupCopies input.physical input.arithmetic
  (congrArg₂ MaterializedQuery.mk (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.sourceField16_0 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.sourceField16_1 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.sourceField16_2 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.sourceField16_3 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.sourceField16_4 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.sourceField16_5 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.sourceField16_6 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.sourceField16_7 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.sourceField16_8 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.sourceField16_9 input.physical copies) rfl)))))))))) rfl).symm

private theorem native_query17 (input : Input) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.encoding17.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.leaf17.weight.value input.physical) =
      Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.query17.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.JumpBranchCached.native.sourcePlacement) :=
  let copies := Airbender.Compiler.FunctionalLinksNative.JumpBranchCached.native.lookupCopies input.physical input.arithmetic
  (congrArg₂ MaterializedQuery.mk (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.sourceField17_0 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.sourceField17_1 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.sourceField17_2 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.sourceField17_3 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.sourceField17_4 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.sourceField17_5 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.sourceField17_6 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.sourceField17_7 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.sourceField17_8 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.sourceField17_9 input.physical copies) rfl)))))))))) rfl).symm

private theorem native_query12 (input : Input) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.encoding12.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.leaf12.weight.value input.physical) =
      Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.query12.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.JumpBranchCached.native.sourcePlacement) :=
  let copies := Airbender.Compiler.FunctionalLinksNative.JumpBranchCached.native.lookupCopies input.physical input.arithmetic
  (congrArg₂ MaterializedQuery.mk (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.sourceField12_1 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.sourceField12_2 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.sourceField12_3 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.sourceField12_4 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.sourceField12_5 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.sourceField12_6 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.sourceField12_7 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.sourceField12_8 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.sourceField12_9 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.sourceField12_10 input.physical copies) rfl)))))))))) (Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.sourceField12_0 input.physical copies)).symm

private theorem native_query0 (input : Input) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.encoding0.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.leaf0.weight.value input.physical) =
      Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.query0.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.JumpBranchCached.native.sourcePlacement) :=
  let copies := Airbender.Compiler.FunctionalLinksNative.JumpBranchCached.native.lookupCopies input.physical input.arithmetic
  (congrArg₂ MaterializedQuery.mk (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.sourceField0_0 input.physical copies) rfl) rfl).symm

private theorem native_query2 (input : Input) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.encoding2.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.leaf2.weight.value input.physical) =
      Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.query2.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.JumpBranchCached.native.sourcePlacement) :=
  let copies := Airbender.Compiler.FunctionalLinksNative.JumpBranchCached.native.lookupCopies input.physical input.arithmetic
  (congrArg₂ MaterializedQuery.mk (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.sourceField2_0 input.physical copies) rfl) rfl).symm

private theorem native_query3 (input : Input) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.encoding3.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.leaf3.weight.value input.physical) =
      Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.query3.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.JumpBranchCached.native.sourcePlacement) :=
  let copies := Airbender.Compiler.FunctionalLinksNative.JumpBranchCached.native.lookupCopies input.physical input.arithmetic
  (congrArg₂ MaterializedQuery.mk (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.sourceField3_0 input.physical copies) rfl) rfl).symm

private theorem native_query18 (input : Input) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.encoding18.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.leaf18.weight.value input.physical) =
      Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.query18.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.JumpBranchCached.native.sourcePlacement) :=
  let copies := Airbender.Compiler.FunctionalLinksNative.JumpBranchCached.native.lookupCopies input.physical input.arithmetic
  (congrArg₂ MaterializedQuery.mk (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.sourceField18_0 input.physical copies) rfl) rfl).symm

private theorem native_timestamp0 (input : Input) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.encoding4.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.leaf4.weight.value input.physical) =
      MaterializedQuery.mk [((Airbender.Compiler.HelperNative.JumpBranchCached.native.fields).get ⟨0, by decide⟩).value (Airbender.Compiler.HelperNative.JumpBranchCached.native.sourceValues input.physical)] 1 := by
  have same := (Airbender.Compiler.HelperNative.JumpBranchCached.native.candidate4).sound
    Airbender.Compiler.HelperNative.JumpBranchCached.native.placement Airbender.Compiler.MemoryNative.JumpBranchCached.native.bank
    Airbender.Compiler.HelperNative.JumpBranchCached.native.checked4 Airbender.Compiler.HelperNative.JumpBranchCached.native.inBank4
    input.physical (Airbender.Compiler.FunctionalLinksNative.JumpBranchCached.native.helperCopies input.physical input.arithmetic)
  rw [Airbender.Compiler.CleanArgumentsNative.JumpBranchCached.native.timestampFieldMatch0] at same
  change MaterializedQuery.mk [Airbender.Compiler.HelperNative.JumpBranchCached.native.recipe4.value input.physical] 1 = _
  exact congrArg (fun value : Source.BaseField => MaterializedQuery.mk [value] 1) same.symm

private theorem native_timestamp1 (input : Input) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.encoding6.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.leaf6.weight.value input.physical) =
      MaterializedQuery.mk [((Airbender.Compiler.HelperNative.JumpBranchCached.native.fields).get ⟨1, by decide⟩).value (Airbender.Compiler.HelperNative.JumpBranchCached.native.sourceValues input.physical)] 1 := by
  have same := (Airbender.Compiler.HelperNative.JumpBranchCached.native.candidate6).sound
    Airbender.Compiler.HelperNative.JumpBranchCached.native.placement Airbender.Compiler.MemoryNative.JumpBranchCached.native.bank
    Airbender.Compiler.HelperNative.JumpBranchCached.native.checked6 Airbender.Compiler.HelperNative.JumpBranchCached.native.inBank6
    input.physical (Airbender.Compiler.FunctionalLinksNative.JumpBranchCached.native.helperCopies input.physical input.arithmetic)
  rw [Airbender.Compiler.CleanArgumentsNative.JumpBranchCached.native.timestampFieldMatch1] at same
  change MaterializedQuery.mk [Airbender.Compiler.HelperNative.JumpBranchCached.native.recipe6.value input.physical] 1 = _
  exact congrArg (fun value : Source.BaseField => MaterializedQuery.mk [value] 1) same.symm

private theorem native_timestamp2 (input : Input) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.encoding7.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.leaf7.weight.value input.physical) =
      MaterializedQuery.mk [((Airbender.Compiler.HelperNative.JumpBranchCached.native.fields).get ⟨2, by decide⟩).value (Airbender.Compiler.HelperNative.JumpBranchCached.native.sourceValues input.physical)] 1 := by
  have same := (Airbender.Compiler.HelperNative.JumpBranchCached.native.candidate7).sound
    Airbender.Compiler.HelperNative.JumpBranchCached.native.placement Airbender.Compiler.MemoryNative.JumpBranchCached.native.bank
    Airbender.Compiler.HelperNative.JumpBranchCached.native.checked7 Airbender.Compiler.HelperNative.JumpBranchCached.native.inBank7
    input.physical (Airbender.Compiler.FunctionalLinksNative.JumpBranchCached.native.helperCopies input.physical input.arithmetic)
  rw [Airbender.Compiler.CleanArgumentsNative.JumpBranchCached.native.timestampFieldMatch2] at same
  change MaterializedQuery.mk [Airbender.Compiler.HelperNative.JumpBranchCached.native.recipe7.value input.physical] 1 = _
  exact congrArg (fun value : Source.BaseField => MaterializedQuery.mk [value] 1) same.symm

private theorem native_timestamp3 (input : Input) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.encoding8.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.leaf8.weight.value input.physical) =
      MaterializedQuery.mk [((Airbender.Compiler.HelperNative.JumpBranchCached.native.fields).get ⟨3, by decide⟩).value (Airbender.Compiler.HelperNative.JumpBranchCached.native.sourceValues input.physical)] 1 := by
  have same := (Airbender.Compiler.HelperNative.JumpBranchCached.native.candidate8).sound
    Airbender.Compiler.HelperNative.JumpBranchCached.native.placement Airbender.Compiler.MemoryNative.JumpBranchCached.native.bank
    Airbender.Compiler.HelperNative.JumpBranchCached.native.checked8 Airbender.Compiler.HelperNative.JumpBranchCached.native.inBank8
    input.physical (Airbender.Compiler.FunctionalLinksNative.JumpBranchCached.native.helperCopies input.physical input.arithmetic)
  rw [Airbender.Compiler.CleanArgumentsNative.JumpBranchCached.native.timestampFieldMatch3] at same
  change MaterializedQuery.mk [Airbender.Compiler.HelperNative.JumpBranchCached.native.recipe8.value input.physical] 1 = _
  exact congrArg (fun value : Source.BaseField => MaterializedQuery.mk [value] 1) same.symm

private theorem native_timestamp4 (input : Input) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.encoding9.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.leaf9.weight.value input.physical) =
      MaterializedQuery.mk [((Airbender.Compiler.HelperNative.JumpBranchCached.native.fields).get ⟨4, by decide⟩).value (Airbender.Compiler.HelperNative.JumpBranchCached.native.sourceValues input.physical)] 1 := by
  have same := (Airbender.Compiler.HelperNative.JumpBranchCached.native.candidate9).sound
    Airbender.Compiler.HelperNative.JumpBranchCached.native.placement Airbender.Compiler.MemoryNative.JumpBranchCached.native.bank
    Airbender.Compiler.HelperNative.JumpBranchCached.native.checked9 Airbender.Compiler.HelperNative.JumpBranchCached.native.inBank9
    input.physical (Airbender.Compiler.FunctionalLinksNative.JumpBranchCached.native.helperCopies input.physical input.arithmetic)
  rw [Airbender.Compiler.CleanArgumentsNative.JumpBranchCached.native.timestampFieldMatch4] at same
  change MaterializedQuery.mk [Airbender.Compiler.HelperNative.JumpBranchCached.native.recipe9.value input.physical] 1 = _
  exact congrArg (fun value : Source.BaseField => MaterializedQuery.mk [value] 1) same.symm

private theorem native_timestamp5 (input : Input) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.encoding10.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.leaf10.weight.value input.physical) =
      MaterializedQuery.mk [((Airbender.Compiler.HelperNative.JumpBranchCached.native.fields).get ⟨5, by decide⟩).value (Airbender.Compiler.HelperNative.JumpBranchCached.native.sourceValues input.physical)] 1 := by
  have same := (Airbender.Compiler.HelperNative.JumpBranchCached.native.candidate10).sound
    Airbender.Compiler.HelperNative.JumpBranchCached.native.placement Airbender.Compiler.MemoryNative.JumpBranchCached.native.bank
    Airbender.Compiler.HelperNative.JumpBranchCached.native.checked10 Airbender.Compiler.HelperNative.JumpBranchCached.native.inBank10
    input.physical (Airbender.Compiler.FunctionalLinksNative.JumpBranchCached.native.helperCopies input.physical input.arithmetic)
  rw [Airbender.Compiler.CleanArgumentsNative.JumpBranchCached.native.timestampFieldMatch5] at same
  change MaterializedQuery.mk [Airbender.Compiler.HelperNative.JumpBranchCached.native.recipe10.value input.physical] 1 = _
  exact congrArg (fun value : Source.BaseField => MaterializedQuery.mk [value] 1) same.symm

private theorem native_timestamp6 (input : Input) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.encoding11.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.leaf11.weight.value input.physical) =
      MaterializedQuery.mk [((Airbender.Compiler.HelperNative.JumpBranchCached.native.fields).get ⟨6, by decide⟩).value (Airbender.Compiler.HelperNative.JumpBranchCached.native.sourceValues input.physical)] 1 := by
  have same := (Airbender.Compiler.HelperNative.JumpBranchCached.native.candidate11).sound
    Airbender.Compiler.HelperNative.JumpBranchCached.native.placement Airbender.Compiler.MemoryNative.JumpBranchCached.native.bank
    Airbender.Compiler.HelperNative.JumpBranchCached.native.checked11 Airbender.Compiler.HelperNative.JumpBranchCached.native.inBank11
    input.physical (Airbender.Compiler.FunctionalLinksNative.JumpBranchCached.native.helperCopies input.physical input.arithmetic)
  rw [Airbender.Compiler.CleanArgumentsNative.JumpBranchCached.native.timestampFieldMatch6] at same
  change MaterializedQuery.mk [Airbender.Compiler.HelperNative.JumpBranchCached.native.recipe11.value input.physical] 1 = _
  exact congrArg (fun value : Source.BaseField => MaterializedQuery.mk [value] 1) same.symm

private theorem native_timestamp7 (input : Input) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.encoding19.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.leaf19.weight.value input.physical) =
      MaterializedQuery.mk [((Airbender.Compiler.HelperNative.JumpBranchCached.native.fields).get ⟨7, by decide⟩).value (Airbender.Compiler.HelperNative.JumpBranchCached.native.sourceValues input.physical)] 1 := by
  have same := (Airbender.Compiler.HelperNative.JumpBranchCached.native.candidate19).sound
    Airbender.Compiler.HelperNative.JumpBranchCached.native.placement Airbender.Compiler.MemoryNative.JumpBranchCached.native.bank
    Airbender.Compiler.HelperNative.JumpBranchCached.native.checked19 Airbender.Compiler.HelperNative.JumpBranchCached.native.inBank19
    input.physical (Airbender.Compiler.FunctionalLinksNative.JumpBranchCached.native.helperCopies input.physical input.arithmetic)
  rw [Airbender.Compiler.CleanArgumentsNative.JumpBranchCached.native.timestampFieldMatch7] at same
  change MaterializedQuery.mk [Airbender.Compiler.HelperNative.JumpBranchCached.native.recipe19.value input.physical] 1 = _
  exact congrArg (fun value : Source.BaseField => MaterializedQuery.mk [value] 1) same.symm

/-- Native base arithmetic identifies each enabled expanded payload and mask
with its source interpretation, including every timestamp helper. -/
theorem nativeRequests_source (input : Input) (group : Fin 3) :
    nativeRequests input group = physicalRequests input group := by
  fin_cases group

  · change [MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.encoding14.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.leaf14.weight.value input.physical),
      MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.encoding15.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.leaf15.weight.value input.physical),
      MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.encoding16.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.leaf16.weight.value input.physical),
      MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.encoding17.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.leaf17.weight.value input.physical),
      MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.encoding12.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.leaf12.weight.value input.physical)] =
      [Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.query14.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.JumpBranchCached.native.sourcePlacement),
      Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.query15.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.JumpBranchCached.native.sourcePlacement),
      Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.query16.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.JumpBranchCached.native.sourcePlacement),
      Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.query17.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.JumpBranchCached.native.sourcePlacement),
      Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.query12.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.JumpBranchCached.native.sourcePlacement)]
    exact (congrArg₂ List.cons (native_query14 input) (congrArg₂ List.cons (native_query15 input) (congrArg₂ List.cons (native_query16 input) (congrArg₂ List.cons (native_query17 input) (congrArg₂ List.cons (native_query12 input) rfl)))))

  · change [MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.encoding0.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.leaf0.weight.value input.physical),
      MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.encoding2.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.leaf2.weight.value input.physical),
      MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.encoding3.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.leaf3.weight.value input.physical),
      MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.encoding18.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.leaf18.weight.value input.physical)] =
      [Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.query0.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.JumpBranchCached.native.sourcePlacement),
      Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.query2.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.JumpBranchCached.native.sourcePlacement),
      Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.query3.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.JumpBranchCached.native.sourcePlacement),
      Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.query18.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.JumpBranchCached.native.sourcePlacement)]
    exact (congrArg₂ List.cons (native_query0 input) (congrArg₂ List.cons (native_query2 input) (congrArg₂ List.cons (native_query3 input) (congrArg₂ List.cons (native_query18 input) rfl))))

  · change [MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.encoding4.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.leaf4.weight.value input.physical),
      MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.encoding6.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.leaf6.weight.value input.physical),
      MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.encoding7.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.leaf7.weight.value input.physical),
      MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.encoding8.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.leaf8.weight.value input.physical),
      MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.encoding9.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.leaf9.weight.value input.physical),
      MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.encoding10.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.leaf10.weight.value input.physical),
      MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.encoding11.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.leaf11.weight.value input.physical),
      MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.encoding19.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.leaf19.weight.value input.physical)] =
      [MaterializedQuery.mk [((Airbender.Compiler.HelperNative.JumpBranchCached.native.fields).get ⟨0, by decide⟩).value (Airbender.Compiler.HelperNative.JumpBranchCached.native.sourceValues input.physical)] 1,
      MaterializedQuery.mk [((Airbender.Compiler.HelperNative.JumpBranchCached.native.fields).get ⟨1, by decide⟩).value (Airbender.Compiler.HelperNative.JumpBranchCached.native.sourceValues input.physical)] 1,
      MaterializedQuery.mk [((Airbender.Compiler.HelperNative.JumpBranchCached.native.fields).get ⟨2, by decide⟩).value (Airbender.Compiler.HelperNative.JumpBranchCached.native.sourceValues input.physical)] 1,
      MaterializedQuery.mk [((Airbender.Compiler.HelperNative.JumpBranchCached.native.fields).get ⟨3, by decide⟩).value (Airbender.Compiler.HelperNative.JumpBranchCached.native.sourceValues input.physical)] 1,
      MaterializedQuery.mk [((Airbender.Compiler.HelperNative.JumpBranchCached.native.fields).get ⟨4, by decide⟩).value (Airbender.Compiler.HelperNative.JumpBranchCached.native.sourceValues input.physical)] 1,
      MaterializedQuery.mk [((Airbender.Compiler.HelperNative.JumpBranchCached.native.fields).get ⟨5, by decide⟩).value (Airbender.Compiler.HelperNative.JumpBranchCached.native.sourceValues input.physical)] 1,
      MaterializedQuery.mk [((Airbender.Compiler.HelperNative.JumpBranchCached.native.fields).get ⟨6, by decide⟩).value (Airbender.Compiler.HelperNative.JumpBranchCached.native.sourceValues input.physical)] 1,
      MaterializedQuery.mk [((Airbender.Compiler.HelperNative.JumpBranchCached.native.fields).get ⟨7, by decide⟩).value (Airbender.Compiler.HelperNative.JumpBranchCached.native.sourceValues input.physical)] 1]
    exact (congrArg₂ List.cons (native_timestamp0 input) (congrArg₂ List.cons (native_timestamp1 input) (congrArg₂ List.cons (native_timestamp2 input) (congrArg₂ List.cons (native_timestamp3 input) (congrArg₂ List.cons (native_timestamp4 input) (congrArg₂ List.cons (native_timestamp5 input) (congrArg₂ List.cons (native_timestamp6 input) (congrArg₂ List.cons (native_timestamp7 input) rfl))))))))

/-- Every native query leaf occurs once, with the single setup leaf completing
exactly the retained native reduction tree's primitive multiset. -/
theorem nativeOperands_coverage (input : Input) (group : Fin 3) :
    (((nativeOperands input group).map Prod.fst) ++ [nativeSetupLeaf group]).Perm
      (([Airbender.Compiler.LookupNative.JumpBranchCached.native.genericTree,
      Airbender.Compiler.LookupNative.JumpBranchCached.native.range16Tree,
      Airbender.Compiler.LookupNative.JumpBranchCached.native.timestampTree]).get group).leaves := by
  fin_cases group

  · change ([14,
      15,
      16,
      17,
      12,
      13] : List Nat).Perm (Airbender.Compiler.LookupNative.JumpBranchCached.native.genericTree).leaves
    exact Eq.mpr (congrArg (fun leaves : List Nat => ([14,
      15,
      16,
      17,
      12,
      13] : List Nat).Perm leaves)
      Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.genericLeavesChecked) (by decide +kernel)

  · change ([0,
      2,
      3,
      18,
      1] : List Nat).Perm (Airbender.Compiler.LookupNative.JumpBranchCached.native.range16Tree).leaves
    exact Eq.mpr (congrArg (fun leaves : List Nat => ([0,
      2,
      3,
      18,
      1] : List Nat).Perm leaves)
      Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.range16LeavesChecked) (by decide +kernel)

  · change ([4,
      6,
      7,
      8,
      9,
      10,
      11,
      19,
      5] : List Nat).Perm (Airbender.Compiler.LookupNative.JumpBranchCached.native.timestampTree).leaves
    exact Eq.mpr (congrArg (fun leaves : List Nat => ([4,
      6,
      7,
      8,
      9,
      10,
      11,
      19,
      5] : List Nat).Perm leaves)
      Airbender.Compiler.HelperNative.JumpBranchCached.native.leavesChecked) (by decide +kernel)

/-- Each designated native setup operand contains precisely the columns used
by the literal setup table in the corresponding logical argument. -/
theorem nativeSetupColumns_binding (group : Fin 3) :
    ([Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.encoding13.columns,
      Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.encoding1.columns,
      Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.encoding5.columns]).get group =
      (Airbender.Compiler.MaterializedWitnessNative.JumpBranchCached.setupColumns group).map
        (fun column => AffineProgram.input (Address := GKRAddress) (R := Nat) column.address) := by
  fin_cases group
  · exact Airbender.Compiler.TableNative.JumpBranchCached.native.genericSetupColumnsPreserved
  · exact Airbender.Compiler.TableNative.JumpBranchCached.native.range16SetupColumnsPreserved
  · exact Airbender.Compiler.TableNative.JumpBranchCached.native.timestampSetupColumnsPreserved

/-- Exact native matching supplies every enabled source tuple in the supplied
setup rows. Native arithmetic proves the operand transport. -/
theorem source_member_with
    (tables : Fin 3 → Fin Airbender.Compiler.MaterializedNative.JumpBranchCached.native.model.imported.data.length →
      List Source.BaseField) (input : Input) (arguments : LookupArgumentsWith tables input)
    (group : Fin 3) (query : MaterializedQuery)
    (member : query ∈ physicalRequests input group) (enabled : query.weight ≠ 0) :
    ∃ index, query.fields = tables group index := by
  apply LookupArgument.member (arguments group)
  change query.fields ∈ activeLookupFields (nativeRequests input group)
  rw [nativeRequests_source input group]
  exact activeLookupFields.member member enabled

private noncomputable def sourceArguments (input : Input) (arguments : LookupArguments input)
    (group : Fin 3) : LookupArgument
      (Airbender.Compiler.MaterializedNative.JumpBranchCached.native.model.fields
        (Airbender.Compiler.MaterializedWitnessNative.JumpBranchCached.setupColumns group))
      (activeLookupFields (physicalRequests input group)) := by
  simpa only [nativeRequests_source input group, Airbender.Compiler.MaterializedWitnessNative.JumpBranchCached.setupColumns] using arguments group
-- End native operand transport.

private theorem physical_member (input : Input) (arguments : LookupArguments input)
    (group : Fin 3) (query : MaterializedQuery)
    (member : query ∈ physicalRequests input group) (enabled : query.weight ≠ 0) :
    Airbender.Compiler.MaterializedNative.JumpBranchCached.native.model.Contains
      (Airbender.Compiler.MaterializedWitnessNative.JumpBranchCached.setupColumns group) query.fields :=
  LookupArgument.member (sourceArguments input arguments group) (activeLookupFields.member member enabled)

/-- Authored lookup membership is proved at physical coordinates, without a
canonical source frame, using exact matching of the emitted tuples. -/
theorem authored_from_arguments (input : Input) (arguments : LookupArguments input) :
    PhysicalAuthoredLookupValid input.physical := by
  constructor
  · intro query member enabled
    apply physical_member input arguments 0 (query.materialized
      ((input.physical ∘ Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.JumpBranchCached.native.sourcePlacement)) ?_ enabled
    simpa [physicalRequests] using
      (List.mem_map.mpr ⟨query, member, rfl⟩ :
        query.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.JumpBranchCached.native.sourcePlacement) ∈
          Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.genericQueries.map (fun item => item.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.JumpBranchCached.native.sourcePlacement)))
  · intro query member enabled
    apply physical_member input arguments 1 (query.materialized
      ((input.physical ∘ Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.JumpBranchCached.native.sourcePlacement)) ?_ enabled
    simpa [physicalRequests] using
      (List.mem_map.mpr ⟨query, member, rfl⟩ :
        query.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.JumpBranchCached.native.sourcePlacement) ∈
          Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.range16Queries.map (fun item => item.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.JumpBranchCached.native.sourcePlacement)))

/-- The complete literal timestamp column, including zero padding, bounds
actual physical helper values. No canonical borrow choice is imposed. -/
theorem helpers_from_arguments (input : Input) (arguments : LookupArguments input) :
    ∀ field ∈ Airbender.Compiler.HelperNative.JumpBranchCached.native.fields,
      (field.value (Airbender.Compiler.HelperNative.JumpBranchCached.native.sourceValues input.physical)).val < 524288 := by
  intro field member
  let value := field.value (Airbender.Compiler.HelperNative.JumpBranchCached.native.sourceValues input.physical)
  have present := physical_member input arguments 2 (MaterializedQuery.mk [value] 1)
    (by simpa [physicalRequests, value, Airbender.Compiler.HelperNative.JumpBranchCached.native.sourceValues] using
          (List.mem_map.mpr ⟨field, member, rfl⟩ :
            MaterializedQuery.mk [field.value (Airbender.Compiler.HelperNative.JumpBranchCached.native.sourceValues input.physical)] 1 ∈
              Airbender.Compiler.HelperNative.JumpBranchCached.native.fields.map (fun item => MaterializedQuery.mk
                [item.value (Airbender.Compiler.HelperNative.JumpBranchCached.native.sourceValues input.physical)] 1))) one_ne_zero
  change Airbender.Compiler.MaterializedNative.JumpBranchCached.native.model.Contains [.timestamp] [value] at present
  exact Airbender.Compiler.MaterializedRangeNative.JumpBranchCached.native.timestamp_bounded value present

theorem input_active (input : Input) :
    (inputRow input).assignment (inputRow input).columns.execute = 1 := input.active

end Airbender.Compiler.PooledRowNative.JumpBranchCached
