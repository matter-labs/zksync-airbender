import Airbender.Import.Compiler.LogicalRows.SubwordMemoryUncached
import Airbender.Proofs.GKRProtocol.LogicalLookup
import Airbender.Proofs.GKRProtocol.MaterializedRangeNative.SubwordMemoryUncached
import Airbender.Proofs.GKRProtocol.PhysicalClosedNative.SubwordMemoryUncached
import Airbender.Proofs.GKRProtocol.PooledRowNative.SubwordMemoryUncached

namespace Airbender.Compiler.PooledRowNative.SubwordMemoryUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option linter.unusedVariables false
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

/-- The readable physical input contract has exactly the generated arithmetic
and execute-column interpretation; this equality changes no row condition. -/
theorem input_binding : Input = PhysicalRowInput
    (fun physical => ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.SubwordMemoryUncached.native.artifact.gates,
    gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.SubwordMemoryUncached.native.bank.address) = 0)
    (fun physical => (Airbender.Compiler.CleanArithmeticNative.SubwordMemoryUncached.native.environment physical (fun _ _ => #[])).get
    Airbender.SubwordMemory.importedConstraintsTraceColumns.execute = 1) := rfl

/-- The public address projection is exactly the retained generated Clean row
interpretation. This is a definitional binding, not an execution premise. -/
theorem inputRow_binding (input : Input) :
    inputRow input = (show Trace.Row babyBearModulus Trace.PooledFamily from
      ⟨.subwordMemory, (Airbender.Compiler.CleanArithmeticNative.SubwordMemoryUncached.native.environment input.physical (fun _ _ => #[])).get⟩) := rfl

/-- Explicit public column-group selection agrees with the retained captured
lookup reduction's group ordering. -/
theorem lookupArguments_binding (input : Input) : LookupArguments input =
    ((group : Fin 3) → LookupArgument
      (Airbender.Compiler.MaterializedNative.SubwordMemoryUncached.native.model.fields
        (Airbender.Compiler.MaterializedWitnessNative.SubwordMemoryUncached.setupColumns group))
      (activeLookupFields (nativeRequests input group))) := rfl

/-- Native base arithmetic transports the actual expanded operands to the
source-projected logical interface; none of the field equalities is a premise. -/
private theorem native_query17 (input : Input) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.encoding17.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.leaf17.weight.value input.physical) =
      Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.query17.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement) :=
  let copies := Airbender.Compiler.FunctionalLinksNative.SubwordMemoryUncached.native.lookupCopies input.physical input.arithmetic
  (congrArg₂ MaterializedQuery.mk (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.sourceField17_0 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.sourceField17_1 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.sourceField17_2 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.sourceField17_3 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.sourceField17_4 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.sourceField17_5 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.sourceField17_6 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.sourceField17_7 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.sourceField17_8 input.physical copies) rfl))))))))) rfl).symm

private theorem native_query18 (input : Input) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.encoding18.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.leaf18.weight.value input.physical) =
      Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.query18.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement) :=
  let copies := Airbender.Compiler.FunctionalLinksNative.SubwordMemoryUncached.native.lookupCopies input.physical input.arithmetic
  (congrArg₂ MaterializedQuery.mk (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.sourceField18_0 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.sourceField18_1 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.sourceField18_2 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.sourceField18_3 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.sourceField18_4 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.sourceField18_5 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.sourceField18_6 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.sourceField18_7 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.sourceField18_8 input.physical copies) rfl))))))))) rfl).symm

private theorem native_query12 (input : Input) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.encoding12.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.leaf12.weight.value input.physical) =
      Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.query12.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement) :=
  let copies := Airbender.Compiler.FunctionalLinksNative.SubwordMemoryUncached.native.lookupCopies input.physical input.arithmetic
  (congrArg₂ MaterializedQuery.mk (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.sourceField12_1 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.sourceField12_2 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.sourceField12_3 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.sourceField12_4 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.sourceField12_5 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.sourceField12_6 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.sourceField12_7 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.sourceField12_8 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.sourceField12_9 input.physical copies) rfl))))))))) (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.sourceField12_0 input.physical copies)).symm

private theorem native_query14 (input : Input) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.encoding14.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.leaf14.weight.value input.physical) =
      Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.query14.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement) :=
  let copies := Airbender.Compiler.FunctionalLinksNative.SubwordMemoryUncached.native.lookupCopies input.physical input.arithmetic
  (congrArg₂ MaterializedQuery.mk (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.sourceField14_0 input.physical copies) rfl) rfl).symm

private theorem native_query0 (input : Input) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.encoding0.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.leaf0.weight.value input.physical) =
      Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.query0.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement) :=
  let copies := Airbender.Compiler.FunctionalLinksNative.SubwordMemoryUncached.native.lookupCopies input.physical input.arithmetic
  (congrArg₂ MaterializedQuery.mk (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.sourceField0_0 input.physical copies) rfl) rfl).symm

private theorem native_query15 (input : Input) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.encoding15.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.leaf15.weight.value input.physical) =
      Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.query15.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement) :=
  let copies := Airbender.Compiler.FunctionalLinksNative.SubwordMemoryUncached.native.lookupCopies input.physical input.arithmetic
  (congrArg₂ MaterializedQuery.mk (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.sourceField15_0 input.physical copies) rfl) rfl).symm

private theorem native_query2 (input : Input) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.encoding2.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.leaf2.weight.value input.physical) =
      Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.query2.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement) :=
  let copies := Airbender.Compiler.FunctionalLinksNative.SubwordMemoryUncached.native.lookupCopies input.physical input.arithmetic
  (congrArg₂ MaterializedQuery.mk (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.sourceField2_0 input.physical copies) rfl) rfl).symm

private theorem native_query3 (input : Input) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.encoding3.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.leaf3.weight.value input.physical) =
      Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.query3.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement) :=
  let copies := Airbender.Compiler.FunctionalLinksNative.SubwordMemoryUncached.native.lookupCopies input.physical input.arithmetic
  (congrArg₂ MaterializedQuery.mk (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.sourceField3_0 input.physical copies) rfl) rfl).symm

private theorem native_timestamp0 (input : Input) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.encoding4.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.leaf4.weight.value input.physical) =
      MaterializedQuery.mk [((Airbender.Compiler.HelperNative.SubwordMemoryUncached.native.fields).get ⟨0, by decide⟩).value (Airbender.Compiler.HelperNative.SubwordMemoryUncached.native.sourceValues input.physical)] 1 := by
  have same := (Airbender.Compiler.HelperNative.SubwordMemoryUncached.native.candidate4).sound
    Airbender.Compiler.HelperNative.SubwordMemoryUncached.native.placement Airbender.Compiler.MemoryNative.SubwordMemoryUncached.native.bank
    Airbender.Compiler.HelperNative.SubwordMemoryUncached.native.checked4 Airbender.Compiler.HelperNative.SubwordMemoryUncached.native.inBank4
    input.physical (Airbender.Compiler.FunctionalLinksNative.SubwordMemoryUncached.native.helperCopies input.physical input.arithmetic)
  rw [Airbender.Compiler.CleanArgumentsNative.SubwordMemoryUncached.native.timestampFieldMatch0] at same
  change MaterializedQuery.mk [Airbender.Compiler.HelperNative.SubwordMemoryUncached.native.recipe4.value input.physical] 1 = _
  exact congrArg (fun value : Source.BaseField => MaterializedQuery.mk [value] 1) same.symm

private theorem native_timestamp1 (input : Input) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.encoding6.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.leaf6.weight.value input.physical) =
      MaterializedQuery.mk [((Airbender.Compiler.HelperNative.SubwordMemoryUncached.native.fields).get ⟨1, by decide⟩).value (Airbender.Compiler.HelperNative.SubwordMemoryUncached.native.sourceValues input.physical)] 1 := by
  have same := (Airbender.Compiler.HelperNative.SubwordMemoryUncached.native.candidate6).sound
    Airbender.Compiler.HelperNative.SubwordMemoryUncached.native.placement Airbender.Compiler.MemoryNative.SubwordMemoryUncached.native.bank
    Airbender.Compiler.HelperNative.SubwordMemoryUncached.native.checked6 Airbender.Compiler.HelperNative.SubwordMemoryUncached.native.inBank6
    input.physical (Airbender.Compiler.FunctionalLinksNative.SubwordMemoryUncached.native.helperCopies input.physical input.arithmetic)
  rw [Airbender.Compiler.CleanArgumentsNative.SubwordMemoryUncached.native.timestampFieldMatch1] at same
  change MaterializedQuery.mk [Airbender.Compiler.HelperNative.SubwordMemoryUncached.native.recipe6.value input.physical] 1 = _
  exact congrArg (fun value : Source.BaseField => MaterializedQuery.mk [value] 1) same.symm

private theorem native_timestamp2 (input : Input) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.encoding7.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.leaf7.weight.value input.physical) =
      MaterializedQuery.mk [((Airbender.Compiler.HelperNative.SubwordMemoryUncached.native.fields).get ⟨2, by decide⟩).value (Airbender.Compiler.HelperNative.SubwordMemoryUncached.native.sourceValues input.physical)] 1 := by
  have same := (Airbender.Compiler.HelperNative.SubwordMemoryUncached.native.candidate7).sound
    Airbender.Compiler.HelperNative.SubwordMemoryUncached.native.placement Airbender.Compiler.MemoryNative.SubwordMemoryUncached.native.bank
    Airbender.Compiler.HelperNative.SubwordMemoryUncached.native.checked7 Airbender.Compiler.HelperNative.SubwordMemoryUncached.native.inBank7
    input.physical (Airbender.Compiler.FunctionalLinksNative.SubwordMemoryUncached.native.helperCopies input.physical input.arithmetic)
  rw [Airbender.Compiler.CleanArgumentsNative.SubwordMemoryUncached.native.timestampFieldMatch2] at same
  change MaterializedQuery.mk [Airbender.Compiler.HelperNative.SubwordMemoryUncached.native.recipe7.value input.physical] 1 = _
  exact congrArg (fun value : Source.BaseField => MaterializedQuery.mk [value] 1) same.symm

private theorem native_timestamp3 (input : Input) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.encoding8.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.leaf8.weight.value input.physical) =
      MaterializedQuery.mk [((Airbender.Compiler.HelperNative.SubwordMemoryUncached.native.fields).get ⟨3, by decide⟩).value (Airbender.Compiler.HelperNative.SubwordMemoryUncached.native.sourceValues input.physical)] 1 := by
  have same := (Airbender.Compiler.HelperNative.SubwordMemoryUncached.native.candidate8).sound
    Airbender.Compiler.HelperNative.SubwordMemoryUncached.native.placement Airbender.Compiler.MemoryNative.SubwordMemoryUncached.native.bank
    Airbender.Compiler.HelperNative.SubwordMemoryUncached.native.checked8 Airbender.Compiler.HelperNative.SubwordMemoryUncached.native.inBank8
    input.physical (Airbender.Compiler.FunctionalLinksNative.SubwordMemoryUncached.native.helperCopies input.physical input.arithmetic)
  rw [Airbender.Compiler.CleanArgumentsNative.SubwordMemoryUncached.native.timestampFieldMatch3] at same
  change MaterializedQuery.mk [Airbender.Compiler.HelperNative.SubwordMemoryUncached.native.recipe8.value input.physical] 1 = _
  exact congrArg (fun value : Source.BaseField => MaterializedQuery.mk [value] 1) same.symm

private theorem native_timestamp4 (input : Input) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.encoding9.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.leaf9.weight.value input.physical) =
      MaterializedQuery.mk [((Airbender.Compiler.HelperNative.SubwordMemoryUncached.native.fields).get ⟨4, by decide⟩).value (Airbender.Compiler.HelperNative.SubwordMemoryUncached.native.sourceValues input.physical)] 1 := by
  have same := (Airbender.Compiler.HelperNative.SubwordMemoryUncached.native.candidate9).sound
    Airbender.Compiler.HelperNative.SubwordMemoryUncached.native.placement Airbender.Compiler.MemoryNative.SubwordMemoryUncached.native.bank
    Airbender.Compiler.HelperNative.SubwordMemoryUncached.native.checked9 Airbender.Compiler.HelperNative.SubwordMemoryUncached.native.inBank9
    input.physical (Airbender.Compiler.FunctionalLinksNative.SubwordMemoryUncached.native.helperCopies input.physical input.arithmetic)
  rw [Airbender.Compiler.CleanArgumentsNative.SubwordMemoryUncached.native.timestampFieldMatch4] at same
  change MaterializedQuery.mk [Airbender.Compiler.HelperNative.SubwordMemoryUncached.native.recipe9.value input.physical] 1 = _
  exact congrArg (fun value : Source.BaseField => MaterializedQuery.mk [value] 1) same.symm

private theorem native_timestamp5 (input : Input) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.encoding10.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.leaf10.weight.value input.physical) =
      MaterializedQuery.mk [((Airbender.Compiler.HelperNative.SubwordMemoryUncached.native.fields).get ⟨5, by decide⟩).value (Airbender.Compiler.HelperNative.SubwordMemoryUncached.native.sourceValues input.physical)] 1 := by
  have same := (Airbender.Compiler.HelperNative.SubwordMemoryUncached.native.candidate10).sound
    Airbender.Compiler.HelperNative.SubwordMemoryUncached.native.placement Airbender.Compiler.MemoryNative.SubwordMemoryUncached.native.bank
    Airbender.Compiler.HelperNative.SubwordMemoryUncached.native.checked10 Airbender.Compiler.HelperNative.SubwordMemoryUncached.native.inBank10
    input.physical (Airbender.Compiler.FunctionalLinksNative.SubwordMemoryUncached.native.helperCopies input.physical input.arithmetic)
  rw [Airbender.Compiler.CleanArgumentsNative.SubwordMemoryUncached.native.timestampFieldMatch5] at same
  change MaterializedQuery.mk [Airbender.Compiler.HelperNative.SubwordMemoryUncached.native.recipe10.value input.physical] 1 = _
  exact congrArg (fun value : Source.BaseField => MaterializedQuery.mk [value] 1) same.symm

private theorem native_timestamp6 (input : Input) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.encoding11.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.leaf11.weight.value input.physical) =
      MaterializedQuery.mk [((Airbender.Compiler.HelperNative.SubwordMemoryUncached.native.fields).get ⟨6, by decide⟩).value (Airbender.Compiler.HelperNative.SubwordMemoryUncached.native.sourceValues input.physical)] 1 := by
  have same := (Airbender.Compiler.HelperNative.SubwordMemoryUncached.native.candidate11).sound
    Airbender.Compiler.HelperNative.SubwordMemoryUncached.native.placement Airbender.Compiler.MemoryNative.SubwordMemoryUncached.native.bank
    Airbender.Compiler.HelperNative.SubwordMemoryUncached.native.checked11 Airbender.Compiler.HelperNative.SubwordMemoryUncached.native.inBank11
    input.physical (Airbender.Compiler.FunctionalLinksNative.SubwordMemoryUncached.native.helperCopies input.physical input.arithmetic)
  rw [Airbender.Compiler.CleanArgumentsNative.SubwordMemoryUncached.native.timestampFieldMatch6] at same
  change MaterializedQuery.mk [Airbender.Compiler.HelperNative.SubwordMemoryUncached.native.recipe11.value input.physical] 1 = _
  exact congrArg (fun value : Source.BaseField => MaterializedQuery.mk [value] 1) same.symm

private theorem native_timestamp7 (input : Input) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.encoding16.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.leaf16.weight.value input.physical) =
      MaterializedQuery.mk [((Airbender.Compiler.HelperNative.SubwordMemoryUncached.native.fields).get ⟨7, by decide⟩).value (Airbender.Compiler.HelperNative.SubwordMemoryUncached.native.sourceValues input.physical)] 1 := by
  have same := (Airbender.Compiler.HelperNative.SubwordMemoryUncached.native.candidate16).sound
    Airbender.Compiler.HelperNative.SubwordMemoryUncached.native.placement Airbender.Compiler.MemoryNative.SubwordMemoryUncached.native.bank
    Airbender.Compiler.HelperNative.SubwordMemoryUncached.native.checked16 Airbender.Compiler.HelperNative.SubwordMemoryUncached.native.inBank16
    input.physical (Airbender.Compiler.FunctionalLinksNative.SubwordMemoryUncached.native.helperCopies input.physical input.arithmetic)
  rw [Airbender.Compiler.CleanArgumentsNative.SubwordMemoryUncached.native.timestampFieldMatch7] at same
  change MaterializedQuery.mk [Airbender.Compiler.HelperNative.SubwordMemoryUncached.native.recipe16.value input.physical] 1 = _
  exact congrArg (fun value : Source.BaseField => MaterializedQuery.mk [value] 1) same.symm

/-- Native base arithmetic identifies each enabled expanded payload and mask
with its source interpretation, including every timestamp helper. -/
theorem nativeRequests_source (input : Input) (group : Fin 3) :
    nativeRequests input group = physicalRequests input group := by
  fin_cases group

  · change [MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.encoding17.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.leaf17.weight.value input.physical),
      MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.encoding18.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.leaf18.weight.value input.physical),
      MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.encoding12.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.leaf12.weight.value input.physical)] =
      [Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.query17.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement),
      Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.query18.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement),
      Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.query12.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement)]
    exact (congrArg₂ List.cons (native_query17 input) (congrArg₂ List.cons (native_query18 input) (congrArg₂ List.cons (native_query12 input) rfl)))

  · change [MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.encoding14.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.leaf14.weight.value input.physical),
      MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.encoding0.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.leaf0.weight.value input.physical),
      MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.encoding15.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.leaf15.weight.value input.physical),
      MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.encoding2.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.leaf2.weight.value input.physical),
      MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.encoding3.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.leaf3.weight.value input.physical)] =
      [Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.query14.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement),
      Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.query0.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement),
      Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.query15.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement),
      Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.query2.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement),
      Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.query3.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement)]
    exact (congrArg₂ List.cons (native_query14 input) (congrArg₂ List.cons (native_query0 input) (congrArg₂ List.cons (native_query15 input) (congrArg₂ List.cons (native_query2 input) (congrArg₂ List.cons (native_query3 input) rfl)))))

  · change [MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.encoding4.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.leaf4.weight.value input.physical),
      MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.encoding6.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.leaf6.weight.value input.physical),
      MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.encoding7.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.leaf7.weight.value input.physical),
      MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.encoding8.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.leaf8.weight.value input.physical),
      MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.encoding9.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.leaf9.weight.value input.physical),
      MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.encoding10.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.leaf10.weight.value input.physical),
      MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.encoding11.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.leaf11.weight.value input.physical),
      MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.encoding16.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.leaf16.weight.value input.physical)] =
      [MaterializedQuery.mk [((Airbender.Compiler.HelperNative.SubwordMemoryUncached.native.fields).get ⟨0, by decide⟩).value (Airbender.Compiler.HelperNative.SubwordMemoryUncached.native.sourceValues input.physical)] 1,
      MaterializedQuery.mk [((Airbender.Compiler.HelperNative.SubwordMemoryUncached.native.fields).get ⟨1, by decide⟩).value (Airbender.Compiler.HelperNative.SubwordMemoryUncached.native.sourceValues input.physical)] 1,
      MaterializedQuery.mk [((Airbender.Compiler.HelperNative.SubwordMemoryUncached.native.fields).get ⟨2, by decide⟩).value (Airbender.Compiler.HelperNative.SubwordMemoryUncached.native.sourceValues input.physical)] 1,
      MaterializedQuery.mk [((Airbender.Compiler.HelperNative.SubwordMemoryUncached.native.fields).get ⟨3, by decide⟩).value (Airbender.Compiler.HelperNative.SubwordMemoryUncached.native.sourceValues input.physical)] 1,
      MaterializedQuery.mk [((Airbender.Compiler.HelperNative.SubwordMemoryUncached.native.fields).get ⟨4, by decide⟩).value (Airbender.Compiler.HelperNative.SubwordMemoryUncached.native.sourceValues input.physical)] 1,
      MaterializedQuery.mk [((Airbender.Compiler.HelperNative.SubwordMemoryUncached.native.fields).get ⟨5, by decide⟩).value (Airbender.Compiler.HelperNative.SubwordMemoryUncached.native.sourceValues input.physical)] 1,
      MaterializedQuery.mk [((Airbender.Compiler.HelperNative.SubwordMemoryUncached.native.fields).get ⟨6, by decide⟩).value (Airbender.Compiler.HelperNative.SubwordMemoryUncached.native.sourceValues input.physical)] 1,
      MaterializedQuery.mk [((Airbender.Compiler.HelperNative.SubwordMemoryUncached.native.fields).get ⟨7, by decide⟩).value (Airbender.Compiler.HelperNative.SubwordMemoryUncached.native.sourceValues input.physical)] 1]
    exact (congrArg₂ List.cons (native_timestamp0 input) (congrArg₂ List.cons (native_timestamp1 input) (congrArg₂ List.cons (native_timestamp2 input) (congrArg₂ List.cons (native_timestamp3 input) (congrArg₂ List.cons (native_timestamp4 input) (congrArg₂ List.cons (native_timestamp5 input) (congrArg₂ List.cons (native_timestamp6 input) (congrArg₂ List.cons (native_timestamp7 input) rfl))))))))

/-- Every native query leaf occurs once, with the single setup leaf completing
exactly the retained native reduction tree's primitive multiset. -/
theorem nativeOperands_coverage (input : Input) (group : Fin 3) :
    (((nativeOperands input group).map Prod.fst) ++ [nativeSetupLeaf group]).Perm
      (([Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.genericTree,
      Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.range16Tree,
      Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.timestampTree]).get group).leaves := by
  fin_cases group

  · change ([17,
      18,
      12,
      13] : List Nat).Perm (Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.genericTree).leaves
    exact Eq.mpr (congrArg (fun leaves : List Nat => ([17,
      18,
      12,
      13] : List Nat).Perm leaves)
      Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.genericLeavesChecked) (by decide +kernel)

  · change ([14,
      0,
      15,
      2,
      3,
      1] : List Nat).Perm (Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.range16Tree).leaves
    exact Eq.mpr (congrArg (fun leaves : List Nat => ([14,
      0,
      15,
      2,
      3,
      1] : List Nat).Perm leaves)
      Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.range16LeavesChecked) (by decide +kernel)

  · change ([4,
      6,
      7,
      8,
      9,
      10,
      11,
      16,
      5] : List Nat).Perm (Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.timestampTree).leaves
    exact Eq.mpr (congrArg (fun leaves : List Nat => ([4,
      6,
      7,
      8,
      9,
      10,
      11,
      16,
      5] : List Nat).Perm leaves)
      Airbender.Compiler.HelperNative.SubwordMemoryUncached.native.leavesChecked) (by decide +kernel)

/-- Each designated native setup operand contains precisely the columns used
by the literal setup table in the corresponding logical argument. -/
theorem nativeSetupColumns_binding (group : Fin 3) :
    ([Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.encoding13.columns,
      Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.encoding1.columns,
      Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.encoding5.columns]).get group =
      (Airbender.Compiler.MaterializedWitnessNative.SubwordMemoryUncached.setupColumns group).map
        (fun column => AffineProgram.input (Address := GKRAddress) (R := Nat) column.address) := by
  fin_cases group
  · exact Airbender.Compiler.TableNative.SubwordMemoryUncached.native.genericSetupColumnsPreserved
  · exact Airbender.Compiler.TableNative.SubwordMemoryUncached.native.range16SetupColumnsPreserved
  · exact Airbender.Compiler.TableNative.SubwordMemoryUncached.native.timestampSetupColumnsPreserved

private noncomputable def sourceArguments (input : Input) (arguments : LookupArguments input)
    (group : Fin 3) : LookupArgument
      (Airbender.Compiler.MaterializedNative.SubwordMemoryUncached.native.model.fields
        (Airbender.Compiler.MaterializedWitnessNative.SubwordMemoryUncached.setupColumns group))
      (activeLookupFields (physicalRequests input group)) := by
  simpa only [nativeRequests_source input group, Airbender.Compiler.MaterializedWitnessNative.SubwordMemoryUncached.setupColumns] using arguments group
-- End native operand transport.

private theorem physical_member (input : Input) (arguments : LookupArguments input)
    (group : Fin 3) (query : MaterializedQuery)
    (member : query ∈ physicalRequests input group) (enabled : query.weight ≠ 0) :
    Airbender.Compiler.MaterializedNative.SubwordMemoryUncached.native.model.Contains
      (Airbender.Compiler.MaterializedWitnessNative.SubwordMemoryUncached.setupColumns group) query.fields :=
  LookupArgument.member (sourceArguments input arguments group) (activeLookupFields.member member enabled)

/-- Authored lookup membership is proved at physical coordinates, without a
canonical source frame, using exact matching of the emitted tuples. -/
theorem authored_from_arguments (input : Input) (arguments : LookupArguments input) :
    PhysicalAuthoredLookupValid input.physical := by
  constructor
  · intro query member enabled
    apply physical_member input arguments 0 (query.materialized
      ((input.physical ∘ Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement)) ?_ enabled
    simpa [physicalRequests] using
      (List.mem_map.mpr ⟨query, member, rfl⟩ :
        query.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement) ∈
          Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.genericQueries.map (fun item => item.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement)))
  · intro query member enabled
    apply physical_member input arguments 1 (query.materialized
      ((input.physical ∘ Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement)) ?_ enabled
    simpa [physicalRequests] using
      (List.mem_map.mpr ⟨query, member, rfl⟩ :
        query.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement) ∈
          Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.range16Queries.map (fun item => item.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement)))

/-- The complete literal timestamp column, including zero padding, bounds
actual physical helper values. No canonical borrow choice is imposed. -/
theorem helpers_from_arguments (input : Input) (arguments : LookupArguments input) :
    ∀ field ∈ Airbender.Compiler.HelperNative.SubwordMemoryUncached.native.fields,
      (field.value (Airbender.Compiler.HelperNative.SubwordMemoryUncached.native.sourceValues input.physical)).val < 524288 := by
  intro field member
  let value := field.value (Airbender.Compiler.HelperNative.SubwordMemoryUncached.native.sourceValues input.physical)
  have present := physical_member input arguments 2 (MaterializedQuery.mk [value] 1)
    (by simpa [physicalRequests, value, Airbender.Compiler.HelperNative.SubwordMemoryUncached.native.sourceValues] using
          (List.mem_map.mpr ⟨field, member, rfl⟩ :
            MaterializedQuery.mk [field.value (Airbender.Compiler.HelperNative.SubwordMemoryUncached.native.sourceValues input.physical)] 1 ∈
              Airbender.Compiler.HelperNative.SubwordMemoryUncached.native.fields.map (fun item => MaterializedQuery.mk
                [item.value (Airbender.Compiler.HelperNative.SubwordMemoryUncached.native.sourceValues input.physical)] 1))) one_ne_zero
  change Airbender.Compiler.MaterializedNative.SubwordMemoryUncached.native.model.Contains [.timestamp] [value] at present
  exact Airbender.Compiler.MaterializedRangeNative.SubwordMemoryUncached.native.timestamp_bounded value present

theorem input_active (input : Input) :
    (inputRow input).assignment (inputRow input).columns.execute = 1 := input.active

theorem input_constraints (input : Input) (arguments : LookupArguments input) {before : Reference.RiscV.Sail.State}
    (image : Trace.ROM.ImportedImage before) {cells : List Trace.Cell}
    {tokens : List (Trace.MemoryToken babyBearModulus)}
    (_physical : Trace.initialImage before cells = some tokens)
    (_domain : ROMNative.WordFullPublic.CoversROM cells) :
    FlatOperation.ConstraintsHoldFlat (Verification.environment (inputRow input).assignment)
      ((inputRow input).constraints (⟨Trace.ROM.table cells tokens,
        Verification.subwordTable (Trace.ROM.words before)⟩ : Trace.PooledSetup babyBearModulus)) := by
  have native := Airbender.Compiler.PhysicalClosedNative.SubwordMemoryUncached.retained_clock_from_physical
    input.physical (fun _ _ => #[]) input.arithmetic (helpers_from_arguments input arguments)
    (authored_from_arguments input arguments)
  exact PublicConstraints.subword_transport _ _ _ native
    (fun _ member guard => ROMNative.SubwordPublic.public_table_refinement image member guard)

/-- Decode by transporting physical table membership directly through the
checked decoder-payload geometry. No canonical borrow frame is needed. -/
theorem input_decoded (input : Input) (arguments : LookupArguments input)
    (typed : (inputRow input).decoderQuery[0].val < 65536) :
    (Trace.decoderTable Trace.NativeDecoder.pooledProgram (inputRow input).family).Contains #[]
      (inputRow input).decoderQuery := by
  apply Airbender.Compiler.DecoderQueryNative.SubwordMemoryUncached.program_from_source_membership (by decide +kernel)
    input.physical (fun _ _ => #[]) input.arithmetic typed
  apply (authored_from_arguments input arguments).1 Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.query12
    Airbender.Compiler.DecoderQueryNative.SubwordMemoryUncached.decoder_query_member
  rw [Airbender.Compiler.DecoderArgumentsNative.SubwordMemoryUncached.native.execute_weight input.physical (fun _ _ => #[]) input.arithmetic]
  have enabled : (Airbender.Compiler.CleanArithmeticNative.SubwordMemoryUncached.native.environment input.physical (fun _ _ => #[])).get
      Airbender.SubwordMemory.importedConstraintsTraceColumns.execute = 1 := input.active
  have nonzero : (Airbender.Compiler.CleanArithmeticNative.SubwordMemoryUncached.native.environment input.physical (fun _ _ => #[])).get
      Airbender.SubwordMemory.importedConstraintsTraceColumns.execute ≠ 0 :=
    fun zero => one_ne_zero (enabled.symm.trans zero)
  simpa [Airbender.Compiler.DecoderArgumentsNative.SubwordMemoryUncached.native.expression0, _root_.Expression.eval] using nonzero

end Airbender.Compiler.PooledRowNative.SubwordMemoryUncached
